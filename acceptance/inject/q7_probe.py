
# proofscan self-check: liveness by signal 0, which a zombie satisfies.
import os


def ps_running(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True
