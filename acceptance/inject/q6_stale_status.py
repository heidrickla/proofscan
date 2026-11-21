

# proofscan self-check: a status set on a refusal and cleared only once an attempt gets through;
# with the plan gone the attempt returns early and the last reason stays.
class PsRunner:
    def __init__(self):
        self.ps_reason = None
        self.ps_plan = None

    def ps_in_window(self) -> bool:
        return bool(self.ps_plan)

    def ps_attempt(self) -> bool:
        if self.ps_plan is None:
            return False
        if not self.ps_in_window():
            self.ps_reason = "outside the window"
            return False
        self.ps_run()
        self.ps_reason = None
        return True

    def ps_run(self) -> None:
        self.ps_plan = None
