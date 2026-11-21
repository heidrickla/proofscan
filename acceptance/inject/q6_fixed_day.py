

import datetime as ps_dt
from zoneinfo import ZoneInfo

# proofscan self-check: a window of one fixed day back from an aware clock reading, which is 23 or
# 25 hours of wall time across a daylight saving change.
PS_ZONE = ZoneInfo("America/Chicago")


def ps_fetch(since, until):
    return [since, until]


def ps_mine():
    now = ps_dt.datetime.now(PS_ZONE)
    return ps_fetch(now - ps_dt.timedelta(days=1), now)
