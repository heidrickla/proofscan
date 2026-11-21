

from hypothesis import given, settings, strategies as ps_st


# proofscan self-check: a property test told to draw new examples on every run.
@settings(max_examples=50, derandomize=False)
@given(ps_st.integers())
def test_ps_drawn(x):
    assert x == x
