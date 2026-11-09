"""Tests for the semantics module."""
import pytest
from forgetting_revision import (
    Signature, entails, equivalent, evaluate, is_tautology, models,
    satisfiable, state_str, states_str, BOTTOM, TOP, Var
)

T, F = True, False
p, q, r = Var("p"), Var("q"), Var("r")
PQ = Signature.of("p q")
PQR = Signature.of("p q r")


# ------------------------------------------------------------- Signature

def test_signature_of_accepts_string_or_list():
    assert Signature.of("p q") == Signature.of(["p", "q"]) == Signature(("p", "q"))


def test_signature_rejects_duplicates():
    with pytest.raises(ValueError):
        Signature.of("p q p")


def test_signature_len():
    assert len(PQ) == 2
    assert len(PQR) == 3


def test_states_order_matches_paper():
    assert PQ.states() == [(T, T), (T, F), (F, T), (F, F)]


def test_states_count_is_2_to_the_n():
    assert len(PQR.states()) == 2 ** 3


def test_assignment():
    assert PQ.assignment((T, F)) == {"p": T, "q": F}


# --------------------------------------------------------------- display

def test_state_str():
    assert state_str((T, F, T)) == "TFT"


def test_states_str_sort_order():
    assert states_str({(F, T), (T, F)}) == "{TF, FT}"


# ------------------------------------------------------------ evaluation

def test_evaluate_constants_and_not():
    assert evaluate(TOP, {}) is True
    assert evaluate(BOTTOM, {}) is False
    assert evaluate(~p, {"p": T}) is False
    assert evaluate(~p, {"p": F}) is True


@pytest.mark.parametrize(
    ("a", "b"),
    [(T, T), (T, F), (F, T), (F, F)],
    ids=["TT", "TF", "FT", "FF"],
)
def test_evaluate_binary_connectives(a, b):
    """Every connective, checked against its truth table in all 4 states."""
    env = {"p": a, "q": b}
    assert evaluate(p & q, env) == (a and b)
    assert evaluate(p | q, env) == (a or b)
    assert evaluate(p >> q, env) == ((not a) or b)
    assert evaluate(p.iff(q), env) == (a == b)


# ---------------------------------------------------------------- models

def test_models_example_1():
    """Doctor-Necklace: Mod(p ∧ ¬q) = {TF}."""
    assert models(p & ~q, PQ) == {(T, F)}


def test_models_example_2():
    """Extended Doctor-Necklace: Mod(p ∧ (¬q → r)) = {TTT, TTF, TFT}."""
    assert states_str(models(p & (~q >> r), PQR)) == "{TTT, TTF, TFT}"


def test_models_of_constants():
    assert models(TOP, PQ) == frozenset(PQ.states())
    assert models(BOTTOM, PQ) == frozenset()


def test_models_allows_unused_signature_variables():
    # p alone over {p, q}: q can be anything
    assert models(p, PQ) == {(T, T), (T, F)}


def test_models_rejects_variables_outside_signature():
    with pytest.raises(ValueError):
        models(p & r, PQ)


# ----------------------------------------------------- logical relations

def test_equivalent_compares_meaning_not_structure():
    assert (p >> q) != (~p | q)                  # different trees...
    assert equivalent(p >> q, ~p | q, PQ)        # ...same meaning
    assert equivalent(~(p & q), ~p | ~q, PQ)     # De Morgan
    assert not equivalent(p >> q, q >> p, PQ)


def test_entails():
    assert entails(p & q, p, PQ)
    assert not entails(p, p & q, PQ)
    assert entails(BOTTOM, q, PQ)                # ⊥ entails everything
    assert entails(p, TOP, PQ)                   # everything entails ⊤


def test_satisfiable():
    assert satisfiable(p & ~q, PQ)
    assert not satisfiable(p & ~p, PQ)


def test_is_tautology():
    assert is_tautology(p | ~p, PQ)
    assert is_tautology((p & q) >> (q & p), PQ)  # the one simplify misses
    assert not is_tautology(p, PQ)