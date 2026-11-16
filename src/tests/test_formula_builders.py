"""Tests for meanings, state_formula, dnf and cnf: going from states back to formulas.

The postulate checker trusts these to produce, for every set of states, a
formula with exactly those models. So the key test is the round trip:
models(dnf(S)) == S for EVERY S, over two and three variables.
"""

import pytest

from forgetting_revision import (
    BOTTOM,
    TOP,
    Signature,
    cnf,
    dnf,
    meanings,
    models,
    state_formula,
    variables,
)

SIGS = [Signature.of("p"), Signature.of("p q"), Signature.of("p q r")]
SIG_IDS = ["n=1", "n=2", "n=3"]


# ------------------------------------------------------------- meanings

@pytest.mark.parametrize(("sig", "count"), list(zip(SIGS, [4, 16, 256], strict=True)), ids=SIG_IDS)
def test_meanings_lists_every_set_of_states_once(sig, count):
    ms = meanings(sig)
    assert len(ms) == count == 2 ** (2 ** len(sig))
    assert len(set(ms)) == count                       # no repeats
    assert all(m <= frozenset(sig.states()) for m in ms)


def test_meanings_order_is_empty_first_everything_last():
    sig = Signature.of("p q")
    ms = meanings(sig)
    assert ms[0] == frozenset()
    assert ms[-1] == frozenset(sig.states())
    assert ms == meanings(sig)                         # same order every call


# ------------------------------------------------------------- state_formula

@pytest.mark.parametrize("sig", SIGS, ids=SIG_IDS)
def test_state_formula_has_exactly_that_state_as_model(sig):
    for s in sig.states():
        assert models(state_formula(s, sig), sig) == {s}


def test_state_formula_reads_like_the_paper():
    sig = Signature.of("p q")
    assert str(state_formula((True, False), sig)) == "(p ∧ ¬q)"


def test_state_formula_rejects_wrong_width():
    with pytest.raises(ValueError):
        state_formula((True,), Signature.of("p q"))


# ------------------------------------------------------------- dnf / cnf round trip

@pytest.mark.parametrize("build", [dnf, cnf], ids=["dnf", "cnf"])
@pytest.mark.parametrize("sig", SIGS, ids=SIG_IDS)
def test_round_trip_every_meaning(build, sig):
    """The property the whole checker rests on."""
    bad = [m for m in meanings(sig) if models(build(m, sig), sig) != m]
    assert not bad, f"{build.__name__} got these meanings wrong: {bad[:3]}"


@pytest.mark.parametrize("build", [dnf, cnf], ids=["dnf", "cnf"])
def test_builders_use_only_signature_variables(build):
    sig = Signature.of("p q r")
    assert all(variables(build(m, sig)) <= set(sig.names) for m in meanings(sig))


def test_constant_cases():
    sig = Signature.of("p q")
    everything = frozenset(sig.states())
    assert dnf(frozenset(), sig) == BOTTOM
    assert cnf(everything, sig) == TOP


def test_dnf_and_cnf_differ_in_syntax_but_not_meaning():
    """Two spellings per meaning: what the Extensionality check needs."""
    sig = Signature.of("p q")
    xor = frozenset({(True, False), (False, True)})
    assert dnf(xor, sig) != cnf(xor, sig)
    assert models(dnf(xor, sig), sig) == models(cnf(xor, sig), sig) == xor


def test_dnf_ignores_input_order_and_repeats():
    sig = Signature.of("p q")
    states = [(False, True), (True, False), (False, True)]
    assert dnf(states, sig) == dnf(reversed(states), sig) == dnf(set(states), sig)
