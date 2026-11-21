
# proofscan self-check: a kept journal pruned by a wall-clock date.
import json
import time
from pathlib import Path


def ps_prune(rows: list[dict], path: Path) -> None:
    cutoff = time.time() - 86400
    kept = [r for r in rows if r["at"] >= cutoff]
    path.write_text(json.dumps(kept))
