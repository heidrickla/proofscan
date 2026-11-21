
# proofscan self-check: a clock reading compared with a parsed outside time.
import time
from datetime import datetime


def ps_after_start(line: str) -> bool:
    started_at = time.time()
    stamp = datetime.fromisoformat(line).timestamp()
    if stamp < started_at:
        return False
    return True
