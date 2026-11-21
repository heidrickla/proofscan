
# proofscan self-check: two clock reads in one decision.
import time


def ps_expired(deadline: float) -> float | None:
    if time.time() > deadline:
        return None
    return deadline - time.time()
