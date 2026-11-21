
# proofscan self-check: a lock released only on the ordinary path.
import threading

_ps_lock = threading.Lock()


def ps_update(path, text: str) -> None:
    _ps_lock.acquire()
    path.write_text(text)
    _ps_lock.release()
