
# proofscan self-check: a refusal decided by a deny pattern.
import re

PS_DENY = re.compile(r"\binternal\b")


def ps_publish(text: str) -> str:
    if PS_DENY.search(text):
        raise ValueError("refused")
    return text
