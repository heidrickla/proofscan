
# proofscan self-check: a caller's value joined onto a root unparsed.
from pathlib import Path


def ps_open(root: Path, ref: str) -> bytes:
    path = root / ref
    return (path / "meta.json").read_bytes()
