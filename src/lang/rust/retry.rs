//! A byte-slice progress summary for a loop over std::str::from_utf8.

use super::{Node, line, named_children, squash, text, walk};
use crate::facts::RetryBound;
use crate::lang::children;
use crate::lang::retry::{any_local, reads, statements};
use std::collections::BTreeSet;

mod counter;
pub(super) mod protocol;

const UTF8: &str = "std::str::from_utf8 resolves to the standard byte-slice API";
const SLICE: &str = "a standard byte slice indexed by [n..] drops its first n bytes";
const PREFIX: &str = "Utf8Error::valid_up_to() is the length of the valid prefix of this input";
const INVALID: &str =
    "Utf8Error::error_len(), when Some(n), gives n >= 1 invalid bytes after that prefix";
const SPLIT: &str = "slice::split_at returns the suffix after the split index as its second result";
const TAIL: &str =
    "a from_utf8 error leaves at least one byte after the valid prefix, even for incomplete UTF-8";

type Assumptions = BTreeSet<&'static str>;

pub(super) fn retries_operation(loop_node: Node, src: &str) -> bool {
    let Some(body) = loop_node.child_by_field_name("body") else {
        return false;
    };
    let index = if loop_node.kind() == "for_expression" {
        let Some(pattern) = loop_node.child_by_field_name("pattern") else {
            return false;
        };
        if !matches!(pattern.kind(), "identifier" | "_") {
            return false;
        }
        Some(text(pattern, src))
    } else {
        None
    };
    let fresh = protocol::volume_input(loop_node, src).or_else(|| {
        if !drains_queue(loop_node, body, src) {
            return None;
        }
        let pattern = loop_node
            .child_by_field_name("condition")?
            .child_by_field_name("pattern")?;
        let [tag, item] = nodes(pattern)[..] else {
            return None;
        };
        (pattern.kind() == "tuple_struct_pattern" && ident(tag, src) == Some("Some"))
            .then(|| ident(item, src))
            .flatten()
    });
    let fresh_probe = counter::fresh_probe(loop_node, body, src);
    let may_repeat = |operation, site| {
        !index.is_some_and(|name| reads(operation, name, src))
            && fresh_probe != Some(site)
            && !fresh.is_some_and(|input| derived_from(operation, site, body, input, src, 8))
            && !from_consumed_line(loop_node, body, operation, site, src)
            && !in_fresh_event_dispatch(body, site, src)
    };
    has_retrying_error(loop_node, body, src, may_repeat)
}

fn drains_queue(loop_node: Node, body: Node, src: &str) -> bool {
    let Some((member, args)) = loop_node
        .child_by_field_name("condition")
        .filter(|n| loop_node.kind() == "while_expression" && n.kind() == "let_condition")
        .and_then(|n| n.child_by_field_name("value"))
        .and_then(call)
    else {
        return false;
    };
    let Some((receiver, field)) = member
        .child_by_field_name("value")
        .zip(member.child_by_field_name("field"))
    else {
        return false;
    };
    if text(field, src) != "pop_front" || !args.is_empty() {
        return false;
    }
    let Some(queue) = receiver.child_by_field_name("field").filter(|_| {
        receiver
            .child_by_field_name("value")
            .is_some_and(|n| n.kind() == "self")
    }) else {
        return false;
    };
    let Some(implementation) =
        std::iter::successors(loop_node.parent(), |n| n.parent()).find(|n| n.kind() == "impl_item")
    else {
        return false;
    };
    let Some(owner) = implementation.child_by_field_name("type") else {
        return false;
    };
    let Some(module) = implementation.parent() else {
        return false;
    };
    let standard_queue = nodes(module)
        .into_iter()
        .find(|n| {
            n.kind() == "struct_item"
                && n.child_by_field_name("name")
                    .is_some_and(|n| text(n, src) == text(owner, src))
        })
        .and_then(|n| n.child_by_field_name("body"))
        .is_some_and(|fields| {
            nodes(fields).into_iter().any(|field| {
                field
                    .child_by_field_name("name")
                    .is_some_and(|n| text(n, src) == text(queue, src))
                    && field
                        .child_by_field_name("type")
                        .and_then(|n| n.child_by_field_name("type"))
                        .is_some_and(|n| match squash(text(n, src)).as_str() {
                            "std::collections::VecDeque" | "::std::collections::VecDeque" => true,
                            "VecDeque" => {
                                imports_symbol(module, "std::collections", "VecDeque", src)
                            }
                            _ => false,
                        })
            })
        });
    if !standard_queue {
        return false;
    }
    let mut used = false;
    walk(body, &mut |n| {
        if n.kind() == "self" {
            used |= !n.parent().is_some_and(|p| {
                p.kind() == "field_expression"
                    && p.child_by_field_name("field")
                        .is_some_and(|field| text(field, src) != text(queue, src))
                    && !p.parent().is_some_and(|p| p.kind() == "call_expression")
            });
        }
    });
    !used
}

fn imports_symbol(module: Node, path: &str, symbol: &str, src: &str) -> bool {
    nodes(module).into_iter().any(|n| {
        if n.kind() != "use_declaration" {
            return false;
        }
        let Some(argument) = n.child_by_field_name("argument") else {
            return false;
        };
        argument
            .child_by_field_name("path")
            .is_some_and(|n| squash(text(n, src)).trim_start_matches("::") == path)
            && (argument
                .child_by_field_name("name")
                .and_then(|n| ident(n, src))
                == Some(symbol)
                || argument.child_by_field_name("list").is_some_and(|list| {
                    nodes(list)
                        .into_iter()
                        .any(|n| ident(n, src) == Some(symbol))
                }))
    })
}

fn derived_from(
    expression: Node,
    site: Node,
    body: Node,
    input: &str,
    src: &str,
    depth: usize,
) -> bool {
    if depth == 0
        || matches!(
            expression.kind(),
            "block" | "unsafe_block" | "match_expression"
        )
    {
        return false;
    }
    any_local(expression, &|node| {
        let Some(name) = ident(node, src) else {
            return false;
        };
        let scopes = std::iter::successors(Some(site), |n| n.parent())
            .take_while(|n| n.start_byte() >= body.start_byte());
        for scope in scopes {
            if scope.kind() == "match_arm"
                && let Some(pattern) = scope.child_by_field_name("pattern")
                && pattern.named_child(0).is_some_and(|p| {
                    p.kind() == "tuple_struct_pattern"
                        && nodes(p).get(1).and_then(|&n| ident(n, src)) == Some(name)
                })
                && let Some(matched) = scope.parent().and_then(|n| n.parent())
            {
                return matched.child_by_field_name("value").is_some_and(|value| {
                    derived_from(value, matched, body, input, src, depth - 1)
                });
            }
            if scope.kind() == "if_expression"
                && scope
                    .child_by_field_name("consequence")
                    .is_some_and(|arm| arm.byte_range().contains(&site.start_byte()))
                && let Some(condition) = scope
                    .child_by_field_name("condition")
                    .filter(|n| n.kind() == "let_condition")
                && condition
                    .child_by_field_name("pattern")
                    .is_some_and(|pattern| {
                        pattern.kind() == "tuple_struct_pattern"
                            && nodes(pattern).get(1).and_then(|&n| ident(n, src)) == Some(name)
                    })
            {
                return condition
                    .child_by_field_name("value")
                    .is_some_and(|value| derived_from(value, scope, body, input, src, depth - 1));
            }
            let Some(block) = scope.parent().filter(|n| *n == body || n.kind() == "block") else {
                continue;
            };
            for statement in statements(block)
                .into_iter()
                .rev()
                .filter(|n| n.end_byte() <= scope.start_byte())
            {
                if let Some(pattern) = statement.child_by_field_name("pattern")
                    && statement.kind() == "let_declaration"
                    && references(pattern, name, src)
                {
                    return ident(pattern, src) == Some(name)
                        && statement.child_by_field_name("value").is_some_and(|value| {
                            derived_from(value, statement, body, input, src, depth - 1)
                        });
                }
                if any_local(statement, &|n| {
                    matches!(
                        n.kind(),
                        "assignment_expression" | "compound_assignment_expr"
                    ) && n
                        .child_by_field_name("left")
                        .is_some_and(|left| references(left, name, src))
                        || n.kind() == "reference_expression"
                            && text(n, src).starts_with("&mut")
                            && references(n, name, src)
                }) {
                    return false;
                }
            }
        }
        name == input
    })
}

fn has_retrying_error<'t>(
    loop_node: Node<'t>,
    body: Node<'t>,
    src: &str,
    may_repeat: impl Fn(Node<'t>, Node<'t>) -> bool,
) -> bool {
    let error_can_retry =
        |pattern: Node, arm: Node| error_pattern(pattern, src) && can_continue(arm, loop_node, src);
    any_local(body, &|n| match n.kind() {
        "match_expression" => {
            n.child_by_field_name("body").is_some_and(|arms| {
                nodes(arms).into_iter().any(|arm| {
                    arm.child_by_field_name("pattern")
                        .zip(arm.child_by_field_name("value"))
                        .is_some_and(|(pat, value)| error_can_retry(pat, value))
                })
            }) && n
                .child_by_field_name("value")
                .is_some_and(|v| may_repeat(v, n))
        }
        "if_expression" => n.child_by_field_name("condition").is_some_and(|cond| {
            cond.kind() == "let_condition"
                && cond
                    .child_by_field_name("pattern")
                    .zip(n.child_by_field_name("consequence"))
                    .is_some_and(|(pat, arm)| error_can_retry(pat, arm))
                && cond
                    .child_by_field_name("value")
                    .is_some_and(|v| may_repeat(v, n))
        }),
        _ => false,
    })
}

fn error_pattern(pattern: Node, src: &str) -> bool {
    match pattern.kind() {
        "match_pattern" => pattern
            .named_child(0)
            .is_some_and(|p| error_pattern(p, src)),
        "or_pattern" => nodes(pattern).into_iter().any(|p| error_pattern(p, src)),
        "tuple_struct_pattern" => {
            match pattern
                .child_by_field_name("type")
                .and_then(|tag| text(tag, src).rsplit("::").next())
            {
                Some("Err") => true,
                Some("Some") => nodes(pattern)
                    .get(1)
                    .is_some_and(|&p| error_pattern(p, src)),
                _ => false,
            }
        }
        _ => false,
    }
}

fn from_consumed_line(loop_node: Node, body: Node, value: Node, site: Node, src: &str) -> bool {
    let Some(parsed) = ident(value, src) else {
        return false;
    };
    let stmts = statements(body);
    // A completed line is parsed and then explicitly discarded before handling its result.
    stmts.windows(4).any(|window| {
        let [read, parse, clear, handle] = window else {
            return false;
        };
        if *handle != site
            || read.kind() != "match_expression"
            || !read
                .child_by_field_name("value")
                .is_some_and(|n| squash(text(n, src)) == "self.read_line().await")
            || parse.kind() != "let_declaration"
            || parse
                .child_by_field_name("pattern")
                .and_then(|n| ident(n, src))
                != Some(parsed)
        {
            return false;
        }
        let Some(read_arms) = read.child_by_field_name("body") else {
            return false;
        };
        nodes(read_arms).iter().any(|arm| {
            arm.child_by_field_name("pattern")
                .is_some_and(|p| text(p, src).starts_with("LineRead::Io("))
                && arm
                    .child_by_field_name("value")
                    .is_some_and(|v| !can_continue(v, loop_node, src))
        }) && squash(text(*clear, src)) == "self.line_buf.clear()"
            && parse.child_by_field_name("value").is_some_and(|v| {
                any_local(v, &|n| {
                    n.kind() == "field_expression" && squash(text(n, src)) == "self.line_buf"
                })
            })
    })
}

fn in_fresh_event_dispatch(body: Node, mut site: Node, src: &str) -> bool {
    while let Some(parent) = site.parent().filter(|&n| n != body) {
        site = parent;
        if site.kind() != "match_arm" {
            continue;
        }
        let Some(pattern) = site.child_by_field_name("pattern") else {
            return false;
        };
        let pattern_text = squash(text(pattern, src));
        if ![
            "Event::SendTaskResult(",
            "Event::ResponseSendTaskResult(",
            "Event::PeerMessage(",
            "Event::ToSink(",
            "Event::ProxyMessage(",
        ]
        .iter()
        .any(|prefix| pattern_text.starts_with(prefix))
        {
            continue;
        }
        let Some(dispatch) = site.parent().and_then(|block| block.parent()) else {
            return false;
        };
        let Some(event) = dispatch
            .child_by_field_name("value")
            .and_then(|v| ident(v, src))
        else {
            return false;
        };
        if squash(text(site, src)).contains(".push_back(") {
            return false;
        }
        // These arms consume an incoming message or a joined task's completion.
        return statements(body)
            .into_iter()
            .take_while(|n| n.end_byte() <= dispatch.start_byte())
            .any(|n| {
                n.kind() == "let_declaration"
                    && n.child_by_field_name("pattern").and_then(|n| ident(n, src)) == Some(event)
                    && n.child_by_field_name("value").is_some_and(|v| {
                        let reading = squash(text(v, src));
                        reading.contains(".pop_front()")
                            && any_local(v, &|m| {
                                m.kind() == "macro_invocation"
                                    && m.child_by_field_name("macro")
                                        .is_some_and(|tag| text(tag, src) == "tokio::select")
                                    && reading.contains(".join_next()")
                                    && reading.contains(".receive()")
                            })
                    })
            });
    }
    false
}

/// An error arm may reach the next iteration through either kind of back edge.
fn can_continue(arm: Node, loop_node: Node, src: &str) -> bool {
    any_local(arm, &|n| {
        n.kind() == "continue_expression" && !leaves_enclosing_loop(n, loop_node, src)
    }) || !always_leaves(arm, loop_node, src)
}

fn always_leaves(n: Node, loop_node: Node, src: &str) -> bool {
    let leaves = |n| always_leaves(n, loop_node, src);
    match n.kind() {
        "return_expression" => exits_loop(n),
        "break_expression" => exits_loop(n) || leaves_enclosing_loop(n, loop_node, src),
        "continue_expression" => leaves_enclosing_loop(n, loop_node, src),
        "block" => statements(n).into_iter().any(leaves),
        "if_expression" => {
            n.child_by_field_name("consequence").is_some_and(leaves)
                && n.child_by_field_name("alternative")
                    .and_then(|n| n.named_child(0))
                    .is_some_and(leaves)
        }
        "macro_invocation" => n.child_by_field_name("macro").is_some_and(|callee| {
            match squash(text(callee, src)).as_str() {
                "std::panic" | "::std::panic" | "core::panic" | "::core::panic" => true,
                "panic" => {
                    let root = std::iter::successors(Some(n), |n| n.parent())
                        .last()
                        .unwrap_or(n);
                    let mut shadowed = false;
                    walk(root, &mut |n| {
                        shadowed |= matches!(n.kind(), "macro_definition" | "use_declaration")
                            && text(n, src)
                                .split(|c: char| !c.is_alphanumeric() && c != '_')
                                .any(|word| word == "panic");
                    });
                    !shadowed
                }
                _ => false,
            }
        }),
        _ => false,
    }
}

fn leaves_enclosing_loop(jump: Node, loop_node: Node, src: &str) -> bool {
    let Some(label) = nodes(jump).into_iter().find(|n| n.kind() == "label") else {
        return false;
    };
    let mut ancestor = jump;
    while let Some(parent) = ancestor.parent() {
        ancestor = parent;
        if nodes(ancestor)
            .into_iter()
            .any(|n| n.kind() == "label" && text(n, src) == text(label, src))
        {
            return ancestor.start_byte() <= loop_node.start_byte()
                && (ancestor != loop_node || jump.kind() == "break_expression");
        }
    }
    false
}

pub(super) fn unmodeled_retry(loop_node: Node, src: &str) -> bool {
    let Some(body) = loop_node.child_by_field_name("body") else {
        return false;
    };
    let polls_pipe = any_local(body, &|n| {
        n.kind() == "call_expression"
            && n.child_by_field_name("function")
                .is_some_and(|f| text(f, src).rsplit("::").next() == Some("PeekNamedPipe"))
    });
    // Status-returning APIs use retry arms with constants in place of Result patterns.
    any_local(body, &|n| match n.kind() {
        "match_arm" => {
            n.child_by_field_name("pattern").is_some_and(|p| {
                let p = text(p, src).trim();
                p.starts_with("ERROR_")
                    && p.bytes()
                        .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_')
                    || retries_status(n, src)
            }) && n
                .child_by_field_name("value")
                .is_some_and(|v| can_continue(v, loop_node, src))
        }
        "if_expression" => {
            (polls_pipe
                || n.child_by_field_name("condition").is_some_and(|cond| {
                    any_local(cond, &|n| {
                        let value = text(n, src);
                        n.kind() == "identifier"
                            && (value.starts_with("ERROR_") || value == "WBEM_S_TIMEDOUT")
                            || n.kind() == "scoped_identifier" && value.contains("ErrorKind::")
                            || n.kind() == "macro_invocation"
                                && value.starts_with("matches!")
                                && value.contains("ErrorKind::")
                    })
                }))
                && n.child_by_field_name("consequence")
                    .is_some_and(|arm| any_local(arm, &|n| n.kind() == "continue_expression"))
        }
        "macro_invocation" => retries_accept(n, src),
        _ => false,
    }) || rearmed_batch(loop_node, body, src)
}

fn retries_status(arm: Node, src: &str) -> bool {
    let Some(pattern) = arm
        .child_by_field_name("pattern")
        .and_then(|n| n.named_child(0))
    else {
        return false;
    };
    if squash(text(pattern, src)) == "ProbeEnd::Drift" {
        return true;
    }
    let http_error = pattern.kind() == "integer_literal"
        && text(pattern, src)
            .parse::<u16>()
            .is_ok_and(|n| (400..=599).contains(&n));
    let status = arm
        .parent()
        .and_then(|n| n.parent())
        .and_then(|n| n.child_by_field_name("value"));
    http_error
        && status.is_some_and(|n| squash(text(n, src)).ends_with(".as_u16()"))
        && arm
            .child_by_field_name("value")
            .is_some_and(|effect| any_local(effect, &|n| n.kind() == "continue_expression"))
}

fn retries_accept(select: Node, src: &str) -> bool {
    if !select
        .child_by_field_name("macro")
        .is_some_and(|callee| matches!(text(callee, src), "tokio::select" | "::tokio::select"))
    {
        return false;
    }
    let Some(tokens) = nodes(select).into_iter().find(|n| n.kind() == "token_tree") else {
        return false;
    };
    children(tokens).windows(8).any(|window| {
        let [bound, assign, receiver, dot, accept, args, arrow, branch] = window else {
            return false;
        };
        let Some(bound) = ident(*bound, src) else {
            return false;
        };
        if assign.kind() != "="
            || ident(*receiver, src).is_none()
            || dot.kind() != "."
            || ident(*accept, src) != Some("accept")
            || squash(text(*args, src)) != "()"
            || arrow.kind() != "=>"
            || branch.kind() != "token_tree"
        {
            return false;
        }
        let branch = format!("loop {}", text(*branch, src));
        let mut parser = tree_sitter::Parser::new();
        if parser
            .set_language(&tree_sitter_rust::LANGUAGE.into())
            .is_err()
        {
            return false;
        }
        let Some(tree) = parser.parse(&branch, None) else {
            return false;
        };
        let Some(loop_node) = tree.root_node().named_child(0).map(statement) else {
            return false;
        };
        let Some(body) = loop_node.child_by_field_name("body") else {
            return false;
        };
        has_retrying_error(loop_node, body, &branch, |value, site| {
            ident(value, &branch) == Some(bound)
                && site.child_by_field_name("body").is_some_and(|arms| {
                    nodes(arms).into_iter().any(|arm| {
                        arm.child_by_field_name("pattern")
                            .is_some_and(|p| error_pattern(p, &branch))
                            && arm.child_by_field_name("value").is_some_and(|effect| {
                                any_local(effect, &|n| n.kind() == "continue_expression")
                            })
                    })
                })
        })
    })
}

fn rearmed_batch(loop_node: Node, body: Node, src: &str) -> bool {
    // An error in a batch can request that the outer poll run the same work again.
    any_local(body, &|branch| {
        let Some((condition, arm)) = branch
            .child_by_field_name("condition")
            .filter(|_| branch.kind() == "if_expression")
            .zip(branch.child_by_field_name("consequence"))
        else {
            return false;
        };
        let flags: Vec<_> = crate::lang::retry::true_conjuncts(condition)
            .into_iter()
            .filter_map(|n| boolean_method(n, "swap", "false", src))
            .collect();
        !flags.is_empty()
            && any_local(arm, &|block| {
                if block.kind() != "block" {
                    return false;
                }
                statements(block)
                    .into_iter()
                    .filter(|n| n.kind() == "for_expression")
                    .any(|n| {
                        n.child_by_field_name("body").is_some_and(|batch| {
                            any_local(batch, &|error| {
                                let Some((condition, handler)) = error
                                    .child_by_field_name("condition")
                                    .filter(|n| {
                                        error.kind() == "if_expression"
                                            && n.kind() == "let_condition"
                                    })
                                    .zip(error.child_by_field_name("consequence"))
                                else {
                                    return false;
                                };
                                condition
                                    .child_by_field_name("pattern")
                                    .is_some_and(|p| error_pattern(p, src))
                                    && can_continue(handler, loop_node, src)
                                    && statements(handler).into_iter().any(|n| {
                                        boolean_method(n, "store", "true", src)
                                            .is_some_and(|f| flags.contains(&f))
                                    })
                            })
                        })
                    })
            })
    })
}

fn boolean_method<'s>(n: Node, method: &str, value: &str, src: &'s str) -> Option<&'s str> {
    let (member, args) = call(n)?;
    let [state, _] = args[..] else { return None };
    (text(state, src) == value && text(member.child_by_field_name("field")?, src) == method)
        .then_some(ident(member.child_by_field_name("value")?, src)?)
}

pub(super) fn retries_pending_batch(loop_node: Node, src: &str) -> bool {
    let Some(body) = loop_node.child_by_field_name("body") else {
        return false;
    };
    // A nested batch can read the same durable pending entries on the next poll.
    any_local(body, &|branch| {
        let Some(condition) = branch.child_by_field_name("condition") else {
            return false;
        };
        if branch.kind() != "if_expression" || condition.kind() != "let_condition" {
            return false;
        }
        let (Some(pattern), Some(value), Some(arm)) = (
            condition.child_by_field_name("pattern"),
            condition.child_by_field_name("value"),
            branch.child_by_field_name("consequence"),
        ) else {
            return false;
        };
        any_local(value, &|n| {
            call(n).is_some_and(|(method, args)| {
                args.is_empty()
                    && method
                        .child_by_field_name("field")
                        .is_some_and(|f| text(f, src) == "pending")
            })
        }) && statements(arm).into_iter().any(|batch| {
            batch.kind() == "for_expression"
                && batch
                    .child_by_field_name("value")
                    .and_then(|n| ident(n, src))
                    .is_some_and(|items| references(pattern, items, src))
                && batch
                    .child_by_field_name("body")
                    .is_some_and(|body| has_retrying_error(batch, body, src, |_, _| true))
        })
    })
}

pub(super) fn records_failed_delivery(loop_node: Node, src: &str) -> bool {
    let Some(body) = loop_node.child_by_field_name("body") else {
        return false;
    };
    any_local(body, &|branch| {
        let Some((condition, arm)) = branch
            .child_by_field_name("condition")
            .filter(|n| branch.kind() == "if_expression" && n.kind() == "let_condition")
            .zip(branch.child_by_field_name("consequence"))
        else {
            return false;
        };
        let Some(value) = condition.child_by_field_name("value") else {
            return false;
        };
        let mut stores = Vec::new();
        walk(value, &mut |n| {
            if let Some((callee, args)) = call(n)
                && args.is_empty()
                && callee
                    .child_by_field_name("field")
                    .is_some_and(|n| text(n, src) == "pending")
                && let Some(store) = callee.child_by_field_name("value")
            {
                stores.push(squash(text(store, src)));
            }
        });
        statements(arm).into_iter().any(|batch| {
            if batch.kind() != "for_expression" {
                return false;
            }
            let Some((id, body)) = batch
                .child_by_field_name("pattern")
                .filter(|n| n.kind() == "tuple_pattern")
                .and_then(|n| n.named_child(0))
                .and_then(|n| ident(n, src))
                .zip(batch.child_by_field_name("body"))
            else {
                return false;
            };
            any_local(body, &|n| {
                if n.kind() != "match_expression" {
                    return false;
                }
                stores.iter().any(|store| {
                    let mut success = false;
                    let mut failure = false;
                    for arm in n.child_by_field_name("body").into_iter().flat_map(nodes) {
                        let Some((pattern, effect)) = arm
                            .child_by_field_name("pattern")
                            .zip(arm.child_by_field_name("value"))
                        else {
                            continue;
                        };
                        let tag = if error_pattern(pattern, src) {
                            "false"
                        } else if squash(text(pattern, src)) == "Ok(())" {
                            "true"
                        } else {
                            continue;
                        };
                        let records = any_local(effect, &|n| {
                            call(n).is_some_and(|(callee, args)| {
                                squash(text(callee, src)) == format!("{store}.delivery_result")
                                    && matches!(args.as_slice(), [key, status, _]
                                        if ident(*key, src) == Some(id) && text(*status, src) == tag)
                            })
                        });
                        success |= tag == "true" && records;
                        failure |= tag == "false" && records;
                    }
                    success && failure
                })
            })
        })
    })
}

pub(super) fn unproven_requeue(loop_node: Node, src: &str) -> Option<RetryBound> {
    let body = loop_node.child_by_field_name("body")?;
    let mut requeue = None;
    walk(body, &mut |n| {
        if requeue.is_some() {
            return;
        }
        if n.kind() == "block" {
            for stmts in statements(n).windows(2) {
                let [push, again] = stmts else { continue };
                if again.kind() == "continue_expression"
                    && call(*push).is_some_and(|(callee, args)| {
                        args.len() == 1
                            && callee
                                .child_by_field_name("field")
                                .is_some_and(|f| text(f, src) == "push_back")
                    })
                {
                    requeue = Some(RetryBound::UnknownReplay(line(*push)));
                    break;
                }
            }
        }
        if n.kind() != "token_tree" {
            return;
        }
        for parts in children(n).windows(5) {
            let [dot, method, args, semicolon, again] = parts else {
                continue;
            };
            if dot.kind() == "."
                && text(*method, src) == "push_back"
                && args.kind() == "token_tree"
                && semicolon.kind() == ";"
                && again.kind() == "continue"
            {
                requeue = Some(RetryBound::UnknownReplay(line(*method)));
                break;
            }
        }
    });
    requeue
}

pub(super) fn input_progress(loop_node: Node, src: &str, swallows: bool) -> Option<RetryBound> {
    let body = loop_node.child_by_field_name("body")?;
    let statements = nodes(body);
    let (subject, input) = statements.iter().copied().map(statement).find_map(|expr| {
        if expr.kind() != "match_expression" {
            return None;
        }
        let (callee, args) = call(expr.child_by_field_name("value")?)?;
        let [arg] = args[..] else { return None };
        matches!(
            squash(text(callee, src)).as_str(),
            "std::str::from_utf8" | "::std::str::from_utf8"
        )
        .then_some((expr, ident(arg, src)?))
    })?;
    let mut updates_input = false;
    let mut slices_other = false;
    walk(body, &mut |n| {
        if !matches!(
            n.kind(),
            "assignment_expression" | "compound_assignment_expr"
        ) {
            return;
        }
        if let Some(left) = n.child_by_field_name("left") {
            updates_input |= references(left, input, src);
        }
        slices_other |= n
            .child_by_field_name("right")
            .and_then(suffix_index)
            .is_some();
    });
    if !updates_input {
        // Dropping bytes from another slice provides no bound on the call's input.
        return (swallows && slices_other).then_some(RetryBound::None);
    }
    let path = Path {
        src,
        input,
        error: None,
        suffix: None,
        positive: None,
        advance: None,
    };
    let mut unsupported = body.has_error();
    walk(body, &mut |n| {
        unsupported |= matches!(
            n.kind(),
            "attribute_item" | "inner_attribute_item" | "macro_invocation" | "unsafe_block"
        );
    });
    if !unsupported
        && statements.len() == 1
        && is_byte_slice(loop_node, input, src)
        && let Some(Edges::Continue(mut assumptions)) =
            path.match_paths(subject, ["Ok", "Err"], |mut p, kind, binding, value| {
                if kind == "Err" {
                    p.error = binding;
                    p.edges(value)
                } else {
                    // A successful parse, including one of the empty slice, must leave the loop.
                    p.edges(value).filter(|edge| matches!(edge, Edges::Exit))
                }
            })
    {
        assumptions.extend([UTF8, SLICE]);
        return Some(RetryBound::InputProgress(
            assumptions.into_iter().map(str::to_owned).collect(),
        ));
    }
    Some(RetryBound::UnknownProgress)
}

fn nodes(n: Node<'_>) -> Vec<Node<'_>> {
    named_children(n)
        .into_iter()
        .filter(|c| !matches!(c.kind(), "line_comment" | "block_comment"))
        .collect()
}

fn statement(n: Node<'_>) -> Node<'_> {
    if n.kind() == "expression_statement" {
        n.named_child(0).unwrap_or(n)
    } else {
        n
    }
}

fn ident<'s>(n: Node, src: &'s str) -> Option<&'s str> {
    (n.kind() == "identifier").then(|| text(n, src).trim_start_matches("r#"))
}

fn references(n: Node, name: &str, src: &str) -> bool {
    let mut found = false;
    walk(n, &mut |child| found |= ident(child, src) == Some(name));
    found
}

fn is_byte_slice<'s>(loop_node: Node, mut name: &'s str, src: &'s str) -> bool {
    let Some(mut block) = loop_node.parent() else {
        return false;
    };
    if block.kind() == "expression_statement" {
        let Some(parent) = block.parent() else {
            return false;
        };
        block = parent;
    }
    let Some(function) = block.parent().filter(|p| p.kind() == "function_item") else {
        return false;
    };
    let byte_slice = |ty: Node| squash(text(ty, src)) == "&[u8]";
    let preceding: Vec<_> = nodes(block)
        .into_iter()
        .filter(|n| n.end_byte() <= loop_node.start_byte())
        .collect();
    if preceding.iter().any(|&n| {
        matches!(
            statement(n).kind(),
            "attribute_item" | "inner_attribute_item" | "macro_invocation"
        )
    }) {
        return false;
    }
    for decl in preceding.into_iter().rev() {
        if let Some(pattern) = decl.child_by_field_name("pattern")
            && decl.kind() == "let_declaration"
            && references(pattern, name, src)
        {
            if ident(pattern, src) != Some(name) {
                return false;
            }
            if let Some(ty) = decl.child_by_field_name("type") {
                return byte_slice(ty);
            }
            let Some(alias) = decl
                .child_by_field_name("value")
                .and_then(|n| ident(n, src))
            else {
                return false;
            };
            name = alias;
        }
    }
    function.child_by_field_name("parameters").is_some_and(|p| {
        nodes(p).into_iter().any(|parameter| {
            parameter
                .child_by_field_name("pattern")
                .and_then(|n| ident(n, src))
                == Some(name)
                && parameter
                    .child_by_field_name("type")
                    .is_some_and(byte_slice)
        })
    })
}

fn call(n: Node<'_>) -> Option<(Node<'_>, Vec<Node<'_>>)> {
    (n.kind() == "call_expression").then_some(())?;
    Some((
        n.child_by_field_name("function")?,
        nodes(n.child_by_field_name("arguments")?),
    ))
}

fn suffix_index(n: Node<'_>) -> Option<(Node<'_>, Node<'_>)> {
    (n.kind() == "reference_expression").then_some(())?;
    let index = n.child_by_field_name("value")?;
    (index.kind() == "index_expression").then_some(())?;
    let [slice, range] = nodes(index)[..] else {
        return None;
    };
    (range.kind() == "range_expression").then_some((slice, range))
}

fn changes_control(n: Node) -> bool {
    matches!(
        n.kind(),
        "return_expression"
            | "break_expression"
            | "continue_expression"
            | "loop_expression"
            | "while_expression"
            | "for_expression"
    )
}

fn falls_through(n: Node) -> bool {
    !changes_control(n) && nodes(n).into_iter().all(falls_through)
}

fn exits_loop(n: Node) -> bool {
    matches!(n.kind(), "return_expression" | "break_expression")
        && nodes(n)
            .into_iter()
            .all(|child| child.kind() != "label" && falls_through(child))
}

enum Edges {
    Exit,
    Continue(Assumptions),
}

#[derive(Clone)]
struct Path<'s> {
    src: &'s str,
    input: &'s str,
    error: Option<&'s str>,
    suffix: Option<&'s str>,
    positive: Option<&'s str>,
    advance: Option<Assumptions>,
}

impl<'s> Path<'s> {
    fn protected(&self, name: &str) -> bool {
        name == self.input || [self.error, self.suffix, self.positive].contains(&Some(name))
    }

    fn method<'t>(&self, n: Node<'t>, receiver: Option<&str>, name: &str) -> Option<Vec<Node<'t>>> {
        let (method, args) = call(n)?;
        (method.kind() == "field_expression"
            && receiver.is_some()
            && ident(method.child_by_field_name("value")?, self.src) == receiver
            && text(method.child_by_field_name("field")?, self.src) == name)
            .then_some(args)
    }

    fn valid_prefix(&self, n: Node) -> bool {
        self.method(n, self.error, "valid_up_to")
            .is_some_and(|args| args.is_empty())
    }

    fn error_len(&self, n: Node) -> bool {
        self.method(n, self.error, "error_len")
            .is_some_and(|args| args.is_empty())
    }

    fn inert(&self, n: Node) -> bool {
        if changes_control(n) {
            return false;
        }
        match n.kind() {
            "identifier" => ident(n, self.src).is_none_or(|name| !self.protected(name)),
            _ => {
                self.valid_prefix(n)
                    || self
                        .method(n, Some(self.input), "len")
                        .is_some_and(|args| args.is_empty())
                    || nodes(n).into_iter().all(|child| self.inert(child))
            }
        }
    }

    fn split_suffix(&self, decl: Node) -> Option<&'s str> {
        if decl.kind() != "let_declaration" || self.advance.is_some() {
            return None;
        }
        let pattern = decl.child_by_field_name("pattern")?;
        let [valid, after] = nodes(pattern)[..] else {
            return None;
        };
        let (valid, after) = (ident(valid, self.src)?, ident(after, self.src)?);
        let [offset] = self.method(
            decl.child_by_field_name("value")?,
            Some(self.input),
            "split_at",
        )?[..] else {
            return None;
        };
        (pattern.kind() == "tuple_pattern"
            && !self.protected(valid)
            && !self.protected(after)
            && self.valid_prefix(offset))
        .then_some(after)
    }

    fn suffix_advance(&self, rhs: Node) -> Option<Assumptions> {
        let (slice, range) = suffix_index(rhs)?;
        let slice = ident(slice, self.src)?;
        let from_split = self.suffix == Some(slice);
        if slice != self.input && !from_split {
            return None;
        }
        let [offset] = nodes(range)[..] else {
            return None;
        };
        if !text(range, self.src).ends_with("..") {
            return None;
        }
        let mut facts = Assumptions::new();
        if from_split {
            facts.extend([PREFIX, SPLIT]);
        }
        let positive = |n| self.positive.is_some() && ident(n, self.src) == self.positive;
        if offset.kind() == "integer_literal"
            && text(offset, self.src)
                .replace('_', "")
                .trim_end_matches("usize")
                .parse::<usize>()
                .is_ok_and(|n| n > 0)
        {
            return Some(facts);
        }
        if positive(offset) {
            facts.insert(INVALID);
            return Some(facts);
        }
        if !from_split
            && offset.kind() == "binary_expression"
            && text(offset.child_by_field_name("operator")?, self.src) == "+"
        {
            let left = offset.child_by_field_name("left")?;
            let right = offset.child_by_field_name("right")?;
            if (self.valid_prefix(left) && positive(right))
                || (positive(left) && self.valid_prefix(right))
            {
                facts.extend([PREFIX, INVALID]);
                return Some(facts);
            }
        }
        if from_split {
            let (callee, args) = call(offset)?;
            let [fallback] = args[..] else { return None };
            if callee.kind() == "field_expression"
                && text(callee.child_by_field_name("field")?, self.src) == "unwrap_or"
                && self.error_len(callee.child_by_field_name("value")?)
                && self
                    .method(fallback, self.suffix, "len")
                    .is_some_and(|args| args.is_empty())
            {
                facts.extend([INVALID, TAIL]);
                return Some(facts);
            }
        }
        None
    }

    fn edges(mut self, expr: Node) -> Option<Edges> {
        if expr.kind() == "block" {
            let statements = nodes(expr);
            // Writes on a path with an unconditional exit cannot affect the next iteration.
            if let Some((&last, before)) = statements.split_last()
                && exits_loop(statement(last))
                && before.iter().copied().all(falls_through)
            {
                return Some(Edges::Exit);
            }
            for (i, &stmt) in statements.iter().enumerate() {
                let n = statement(stmt);
                if let Some(after) = self.split_suffix(n) {
                    self.suffix = Some(after);
                } else if n.kind() == "assignment_expression"
                    && ident(n.child_by_field_name("left")?, self.src) == Some(self.input)
                {
                    if self.advance.is_some() {
                        return None;
                    }
                    self.advance = Some(self.suffix_advance(n.child_by_field_name("right")?)?);
                } else if i + 1 == statements.len() {
                    return self.edges(n);
                } else if !self.inert(n) {
                    return None;
                }
            }
            return Some(Edges::Continue(self.advance?));
        }
        match expr.kind() {
            "return_expression" | "break_expression" if exits_loop(expr) => Some(Edges::Exit),
            "continue_expression" if nodes(expr).is_empty() => Some(Edges::Continue(self.advance?)),
            "match_expression" if self.error_len(expr.child_by_field_name("value")?) => self
                .match_paths(expr, ["Some", "None"], |mut p, kind, binding, value| {
                    if kind == "Some" {
                        p.positive = binding;
                    }
                    p.edges(value)
                }),
            _ if self.inert(expr) => Some(Edges::Continue(self.advance?)),
            _ => None,
        }
    }

    fn match_paths(
        &self,
        expr: Node,
        kinds: [&str; 2],
        mut edge: impl FnMut(Self, &str, Option<&'s str>, Node) -> Option<Edges>,
    ) -> Option<Edges> {
        let mut covered = [false; 2];
        let mut assumptions: Option<Assumptions> = None;
        for arm in nodes(expr.child_by_field_name("body")?) {
            let pattern = arm.child_by_field_name("pattern")?;
            let (variant, binding) = self.variant(nodes(pattern).first().copied()?)?;
            let which = kinds.iter().position(|kind| *kind == variant)?;
            if binding.is_some_and(|name| self.protected(name)) {
                return None;
            }
            if let Some(guard) = pattern.child_by_field_name("condition") {
                if !self.inert(guard)
                    || binding.is_some_and(|name| references(guard, name, self.src))
                {
                    return None;
                }
            } else {
                covered[which] = true;
            }
            if let Edges::Continue(facts) = edge(
                self.clone(),
                variant,
                binding,
                arm.child_by_field_name("value")?,
            )? {
                assumptions
                    .get_or_insert_with(Assumptions::new)
                    .extend(facts);
            }
        }
        covered
            .into_iter()
            .all(|seen| seen)
            .then(|| assumptions.map_or(Edges::Exit, Edges::Continue))
    }

    fn variant(&self, pattern: Node) -> Option<(&'s str, Option<&'s str>)> {
        if pattern.kind() == "tuple_struct_pattern" {
            let tag = pattern.child_by_field_name("type")?;
            let name = ident(tag, self.src)?;
            let children = nodes(pattern);
            if let [_, binding] = children[..] {
                return Some((name, Some(ident(binding, self.src)?)));
            }
            if squash(text(pattern, self.src)) == format!("{name}(_)") {
                return Some((name, None));
            }
            None
        } else if ident(pattern, self.src) == Some("None") {
            Some(("None", None))
        } else {
            None
        }
    }
}
