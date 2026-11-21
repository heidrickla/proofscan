import datetime
import os
# proofscan self-check: a clock reading taken before the check that vouches for the clock, then acted on.
PS_HOST: dict = {}


def ps_clock_unsynced() -> bool:
    return PS_HOST.get("dt_synchronized") is False


def ps_prune(now: datetime.datetime) -> None:
    for name in os.listdir("ps_backups"):
        if now.timestamp() - os.path.getmtime(name) > 3 * 86400:
            os.unlink(name)


def ps_sweep() -> None:
    now = datetime.datetime.now(datetime.UTC)
    if ps_clock_unsynced():
        return
    ps_prune(now)
