
# proofscan self-check: the newest value per key, kept after the key stops producing.
def ps_latest(runs: list[dict]) -> dict:
    newest: dict = {}
    for run in runs:
        key = run["workflow"]
        if key not in newest or run["at"] > newest[key]["at"]:
            newest[key] = run
    return newest
