
import os
# proofscan self-check: a plan held between calls stops the tick, its retry refuses without ending
# it, and the tick's recovery rewrites the plan's journal without reading the plan.
PS_JOURNAL = "ps_journal.jsonl"


class PsScheduler:
    def __init__(self):
        self.ps_plan = None

    def ps_start(self):
        self.ps_plan = {"step": 0}

    def ps_retry(self):
        if not self.ps_in_window():
            return False
        self.ps_commit()
        return True

    def ps_in_window(self):
        return True

    def ps_commit(self):
        with open(os.path.join("data", PS_JOURNAL), "a") as fh:
            fh.write("start\n")
        self.ps_plan = None

    def ps_recover(self):
        with open(os.path.join("data", PS_JOURNAL), "a") as fh:
            fh.write("end interrupted\n")

    def ps_tick(self):
        self.ps_recover()
        if self.ps_plan is not None:
            self.ps_retry()
            if self.ps_plan is not None:
                return
        self.ps_start()
