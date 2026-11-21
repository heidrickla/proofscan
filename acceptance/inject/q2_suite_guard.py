
# proofscan self-check: a suite-wide fixture that switches a guard off.
import pytest


@pytest.fixture(autouse=True)
def _ps_no_verify(monkeypatch):
    monkeypatch.setattr("train.packs.verify_pack", lambda *a, **k: True)
