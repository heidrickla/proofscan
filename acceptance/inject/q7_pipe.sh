
# proofscan self-check: a test runner piped to tail, so the pipeline's exit is tail's.
python -m pytest -q tests | tail -n 20
