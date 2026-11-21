
import json
from pathlib import Path
# proofscan self-check: a store read, a call that writes the store, and the older copy written back.
def ps_read_state() -> dict:
    return json.loads(Path("ps_state.json").read_text())


def ps_save_state(doc: dict) -> None:
    Path("ps_state.json").write_text(json.dumps(doc))


def ps_commit() -> None:
    ps_save_state({"committed": True})


def ps_tick() -> None:
    raw = ps_read_state()
    ps_commit()
    state = dict(raw)
    ps_save_state(state)
