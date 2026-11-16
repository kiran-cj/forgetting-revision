"""Property tests for simplify: checked over every small formula, not hand-picked ones.

test_transform.py checks individual rewrite rules (p ∧ ⊤ -> p, ...). This file
checks the promises simplify makes about EVERY input:

  1. it preserves meaning      simplify(f) ≡ f
  2. it adds no variables      vars(simplify(f)) ⊆ vars(f)
  3. it folds every constant   the result is ⊤, ⊥, or contains no ⊤/⊥
  4. it is idempotent          simplify(simplify(f)) == simplify(f)
  5. it never grows a formula  size(simplify(f)) <= size(f)

Two sources of formulas:
  - EXHAUSTIVE: every formula of depth <= 2 over {p, q, ⊤, ⊥} (20,812 formulas).
    Depth 2 is enough to hit every rule with every kind of child, including
    nested constants such as ¬⊤ ∧ p, which is where folding bugs hide.
  - RANDOM: deeper formulas over three variables, from a FIXED seed, so a
    failure is reproducible and the test never flickers.
"""

import random
from collections.abc import Iterator

import pytest

from forgetting_revision import (
    BOTTOM,
    TOP,
    And,
    Const,
    Formula,
    Iff,
    Implies,
    Not,
    Or,
    Signature,
    Var,
    equivalent,
    simplify,
    variables,
)

BINARY = (And, Or, Implies, Iff)


# ------------------------------------------------------------- generators

def all_formulas(leaves: list[Formula], depth: int) -> list[Formula]:
    """Every formula whose tree is at most `depth` connectives deep.

    Built level by level: level d+1 = ¬x for every x so far, plus every
    binary connective over every pair so far. The count grows fast
    (4 -> 72 -> 20,812 for four leaves, after removing repeats), so keep depth at 2.
    """
    formulas = list(leaves)
    for _ in range(depth):
        formulas = (
            formulas
            + [Not(a) for a in formulas]
            + [op(a, b) for op in BINARY for a in formulas for b in formulas]
        )
        formulas = list(dict.fromkeys(formulas))  # frozen nodes hash, so dedupe
    return formulas


def random_formula(rng: random.Random, leaves: list[Formula], depth: int) -> Formula:
    """A random tree. Leaves become more likely as depth runs out."""
    if depth == 0 or rng.random() < 0.2:
        return rng.choice(leaves)
    if rng.random() < 0.2:
        return Not(random_formula(rng, leaves, depth - 1))
    op = rng.choice(BINARY)
    return op(random_formula(rng, leaves, depth - 1), random_formula(rng, leaves, depth - 1))


def subformulas(f: Formula) -> Iterator[Formula]:
    """f and every node beneath it."""
    yield f
    match f:
        case Not(a):
            yield from subformulas(a)
        case And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b):
            yield from subformulas(a)
            yield from subformulas(b)


def size(f: Formula) -> int:
    return sum(1 for _ in subformulas(f))


# ------------------------------------------------------------- formula sets

SIG2 = Signature.of("p q")
SMALL = all_formulas([Var("p"), Var("q"), TOP, BOTTOM], depth=2)

SIG3 = Signature.of("p q r")
_rng = random.Random(2026)
DEEP = [
    random_formula(_rng, [Var("p"), Var("q"), Var("r"), TOP, BOTTOM], depth=5)
    for _ in range(3000)
]

CASES = [pytest.param(SMALL, SIG2, id="exhaustive-depth2"),
         pytest.param(DEEP, SIG3, id="random-depth5")]


def first_failure(formulas, check):
    """Return the first formula that fails `check`, or None.

    Looping inside one test (instead of parametrising 20,000 cases) keeps the
    run fast; returning the formula makes the assert message show exactly
    which input broke.
    """
    return next((f for f in formulas if not check(f)), None)


# ------------------------------------------------------------- the properties

def test_generator_sizes():
    """Guards the generator itself: if this count changes, the exhaustive
    test is silently covering a different set of formulas."""
    assert len(SMALL) == 20_812


@pytest.mark.parametrize(("formulas", "sig"), CASES)
def test_simplify_preserves_meaning(formulas, sig):
    bad = first_failure(formulas, lambda f: equivalent(simplify(f), f, sig))
    assert bad is None, f"{bad}  simplified to  {simplify(bad)}, which means something else"


@pytest.mark.parametrize(("formulas", "sig"), CASES)
def test_simplify_adds_no_variables(formulas, sig):
    bad = first_failure(formulas, lambda f: variables(simplify(f)) <= variables(f))
    assert bad is None, f"{bad}  simplified to  {simplify(bad)}"


@pytest.mark.parametrize(("formulas", "sig"), CASES)
def test_simplify_folds_every_constant(formulas, sig):
    def folded(f):
        g = simplify(f)
        return isinstance(g, Const) or not any(isinstance(s, Const) for s in subformulas(g))

    bad = first_failure(formulas, folded)
    assert bad is None, f"{bad}  simplified to  {simplify(bad)}, which still contains ⊤ or ⊥"


@pytest.mark.parametrize(("formulas", "sig"), CASES)
def test_simplify_is_idempotent(formulas, sig):
    bad = first_failure(formulas, lambda f: simplify(simplify(f)) == simplify(f))
    assert bad is None, (
        f"{bad}: one pass gives {simplify(bad)}, a second gives {simplify(simplify(bad))}"
    )


@pytest.mark.parametrize(("formulas", "sig"), CASES)
def test_simplify_never_grows(formulas, sig):
    bad = first_failure(formulas, lambda f: size(simplify(f)) <= size(f))
    assert bad is None, f"{bad}  grew into  {simplify(bad)}"
