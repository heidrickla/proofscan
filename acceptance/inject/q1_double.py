
# proofscan self-check: a production rule and a test double that re-implements it.
def task_state(job: dict) -> str:
    if job["exit"] is None and job["pid"]:
        return "running"
    if job["exit"] == 0:
        return "done"
    if job["exit"] == 75:
        return "retry"
    return "failed"


class FakeRunner:
    def task_state(self, job: dict) -> str:
        if job["exit"] is None and job["pid"]:
            return "running"
        if job["exit"] == 0:
            return "done"
        if job["exit"] == 75:
            return "retry"
        return "failed"
