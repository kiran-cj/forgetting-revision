"""Tests for the transform module."""
import pytest

from forgetting_revision import BOTTOM, TOP, Var, simplify, substitute

p, q, r = Var("p"), Var("q"), Var("r")
f = p & (~q >> r)


# ------------------------------------------------------------- substitute

def test_substitute_with_constants():
    assert substitute(f, {"q": TOP}) == p & (~TOP >> r)
    assert substitute(f, {"q": BOTTOM}) == p & (~BOTTOM >> r)


def test_substitute_leaves_original_untouched():
    before = f
    substitute(f, {"q": TOP})
    assert f is before
    assert f == p & (~q >> r)


def test_substitute_ignores_unmapped_variables():
    assert substitute(f, {"z": TOP}) == f


def test_substitute_with_formula():
    assert substitute(f, {"p": q | r}) == (q | r) & (~q >> r)


def test_substitute_is_simultaneous():
    # a clean swap, not p -> q -> p
    assert substitute(p & q, {"p": q, "q": p}) == q & p


def test_substitute_then_simplify():
    assert simplify(substitute(f, {"q": TOP})) == p
    assert simplify(substitute(f, {"q": BOTTOM})) == p & r


# --------------------------------------------------------------- simplify

'''Parameteized test cases for simplify, each case runs independently and a failure
tells exactly while rule broke.'''
@pytest.mark.parametrize(
    ("formula", "expected"),
    [
        # Implies
        (BOTTOM >> p, TOP),       # ⊥ → b  ≡ ⊤
        (p >> TOP, TOP),          # a → ⊤  ≡ ⊤
        (p >> p, TOP),            # a → a  ≡ ⊤
        (TOP >> p, p),            # ⊤ → b  ≡ b
        (p >> BOTTOM, ~p),        # a → ⊥  ≡ ¬a
        (~p >> BOTTOM, p),        # ¬¬p cleaned up by the recursive call
        (p >> q, p >> q),         # no rule applies
        # Not
        (~TOP, BOTTOM),
        (~~p, p),
        # And / Or with constants
        (p & TOP, p),
        (p & BOTTOM, BOTTOM),
        (p | BOTTOM, p),
        (p | TOP, TOP),
        # bottom-up: children simplified first
        (p & (~TOP >> r), p),
    ],
    ids=str,
)
def test_simplify(formula, expected):
    assert simplify(formula) == expected


def test_simplify_misses_non_structural_tautology():
    """Known limit: == is structural, so commuted sides aren't recognised."""
    g = (p & q) >> (q & p)
    assert simplify(g) == g