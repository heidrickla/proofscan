
# proofscan self-check: a check function reads the clock, then the act reads it again.
import time
from pathlib import Path


def _ps_fresh(limit: float) -> bool:
    return time.time() < limit


def ps_stamp(limit: float, path: Path) -> None:
    if not _ps_fresh(limit):
        return
    path.write_text(str(time.time()))
