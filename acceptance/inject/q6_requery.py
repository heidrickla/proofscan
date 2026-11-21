
# proofscan self-check: a failure handler that runs the query that failed.
class PsWatch:
    def alive(self) -> bool:
        return self.proc.poll() is None

    def stop(self) -> None:
        if self.alive():
            self.proc.kill()

    def check(self) -> bool:
        try:
            return self.alive()
        except OSError:
            self.stop()
            return False
