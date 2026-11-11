"""Tests for the syntax module."""
from dataclasses import FrozenInstanceError

import pytest

from forgetting_revision import (
    BOTTOM,
    TOP,
    And,
    Const,
    Iff,
    Implies,
    Not,
    Or,
    Var,
    variables,
)

p, q, r = Var("p"), Var("q"), Var("r")


# ---------------------------------------------------- operator shortcuts

@pytest.mark.parametrize(
    ("shortcut", "explicit"),
    [
        (~p, Not(p)),
        (p & q, And(p, q)),
        (p | q, Or(p, q)),
        (p >> q, Implies(p, q)),
        (p.iff(q), Iff(p, q)),
        (p & (~q >> r), And(p, Implies(Not(q), r))),  # nesting
    ],
    ids=["not", "and", "or", "implies", "iff", "nested"],
)
def test_operators_build_the_right_nodes(shortcut, explicit):
    assert shortcut == explicit


def test_rshift_binds_tighter_than_and():
    """The precedence trap from the Formula docstring."""
    assert (p & q >> r) == p & (q >> r)
    assert (p & q >> r) != (p & q) >> r


# ------------------------------------------------------------- constants

def test_top_and_bottom():
    assert TOP == Const(True)
    assert BOTTOM == Const(False)
    assert TOP != BOTTOM


# ---------------------------------------------------------- immutability

def test_nodes_are_frozen():
    with pytest.raises(FrozenInstanceError):
        p.name = "x"
    f = p & q
    with pytest.raises(FrozenInstanceError):
        f.left = r


# ----------------------------------------------------- equality, hashing

def test_equality_is_structural():
    assert Var("p") == Var("p")
    assert p & q == And(Var("p"), Var("q"))
    assert p & q != q & p                    # same meaning, different tree
    assert (p >> q) != (~p | q)              # equivalent, but == says no


def test_formulas_are_hashable():
    assert len({p & q, p & q, q & p}) == 2   # duplicates collapse
    lookup = {p >> q: "implication"}
    assert lookup[Implies(p, q)] == "implication"


# -------------------------------------------------------------- printing

@pytest.mark.parametrize(
    ("formula", "text"),
    [
        (p, "p"),
        (TOP, "⊤"),
        (BOTTOM, "⊥"),
        (~p, "¬p"),
        (p & q, "(p ∧ q)"),
        (p | q, "(p ∨ q)"),
        (p >> q, "(p → q)"),
        (p.iff(q), "(p ↔ q)"),
        (p & (~q >> r), "(p ∧ (¬q → r))"),
    ],
    ids=["var", "top", "bottom", "not", "and", "or", "implies", "iff", "nested"],
)
def test_str(formula, text):
    assert str(formula) == text


# ------------------------------------------------------------- variables

def test_variables():
    assert variables(TOP) == frozenset()
    assert variables(p) == frozenset({"p"})
    assert variables(p & (~q >> r)) == frozenset({"p", "q", "r"})
    assert variables(p & ~p) == frozenset({"p"})   # no duplicates


def test_variables_rejects_non_formulas():
    with pytest.raises(TypeError):
        variables("p")