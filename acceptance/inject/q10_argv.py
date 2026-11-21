
# proofscan self-check: a key passed in a child process's argument list, which ps shows.
import os
import subprocess


def ps_fetch(url: str) -> None:
    key = os.getenv("PS_API_KEY")
    subprocess.run(["curl", "-H", f"Authorization: Bearer {key}", url], check=True)
