import datetime
import json
from pathlib import Path
# proofscan self-check: a store written with a clock reading before the check that vouches for the clock.
PS_HOST: dict = {}


def ps_clock_unsynced() -> bool:
    return PS_HOST.get("dt_synchronized") is False


def ps_load_state() -> dict:
    p = Path("ps_clock_state.json")
    if not p.exists():
        p.write_text(json.dumps({"lost_at": datetime.datetime.now(datetime.UTC).isoformat()}))
    return json.loads(p.read_text())


def ps_tick() -> list:
    state = ps_load_state()
    if ps_clock_unsynced():
        return []
    return sorted(state)
