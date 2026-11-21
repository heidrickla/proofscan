# proofscan self-check: a structural guard that refuses only the receivers a hand-kept table names.
import ast
from pathlib import Path

PS_RECEIVERS = {"engine", "conn"}


def test_ps_no_begin_on_runner_connection():
    tree = ast.parse(Path(__file__).read_text())
    bad = []
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
            continue
        if not isinstance(node.func.value, ast.Name):
            continue
        if node.func.value.id not in PS_RECEIVERS:
            continue
        bad.append(node.lineno)
    assert not bad
