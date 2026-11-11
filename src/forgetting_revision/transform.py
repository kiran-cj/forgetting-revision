"""
Transformation layer: building new trees from old ones.

  substitute(α, {"q": TOP})   substitutes the truth value 'TOP' to Var('q')- α[q/⊤]
  simplify(f)                 folds away ⊤ and ⊥ so results are readable

Both return NEW formulas; the input is never modified (nodes are frozen).
"""

from collections.abc import Mapping

from .syntax import BOTTOM, TOP, And, Const, Formula, Iff, Implies, Not, Or, Var


def substitute(f: Formula, mapping: Mapping[str, Formula]) -> Formula:
    """Replace every occurrence of each variable named in `mapping` with
    the formula it maps to. Rebuilds the tree bottom-up."""
    match f:
        case Const():
            return f
        case Var(name):
            return mapping.get(name, f)
        case Not(a):
            return Not(substitute(a, mapping))
        case And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b):
            # type(f) is the node's own class, so And stays And, Or stays Or...
            return type(f)(substitute(a, mapping), substitute(b, mapping))
    raise TypeError(f"Not a formula: {f!r}")

def simplify(f: Formula) -> Formula:
    """Constant folding: removes ⊤/⊥ and a few trivial patterns.

    This is COSMETIC. It makes (p ∧ ¬⊤) ∨ (p ∧ ¬⊥) print as p, but it is not
    a full minimiser: it will not, for example, reduce p ∨ (p ∧ r) to p.
    Never test correctness with == on simplified trees; use
    semantics.equivalent().
    """
    match f:
        case Var() | Const():
            return f

        case Not(a):
            a = simplify(a)
            match a:
                case Const(v):
                    return Const(not v)
                case Not(inner):           # ¬¬x = x
                    return inner
            return Not(a)

        case And(a, b):
            a, b = simplify(a), simplify(b)
            if a == BOTTOM or b == BOTTOM:
                return BOTTOM
            if a == TOP:
                return b
            if b == TOP or a == b:
                return a
            return And(a, b)

        case Or(a, b):
            a, b = simplify(a), simplify(b)
            if a == TOP or b == TOP:
                return TOP
            if a == BOTTOM:
                return b
            if b == BOTTOM or a == b:
                return a
            return Or(a, b)

        case Implies(a, b):
            a, b = simplify(a), simplify(b)
            if a == BOTTOM or b == TOP or a == b:
                return TOP
            if a == TOP:
                return b
            if b == BOTTOM:
                return simplify(Not(a))
            return Implies(a, b)

        case Iff(a, b):
            a, b = simplify(a), simplify(b)
            if a == b:
                return TOP
            if a == TOP:
                return b
            if b == TOP:
                return a
            if a == BOTTOM:
                return simplify(Not(b))
            if b == BOTTOM:
                return simplify(Not(a))
            return Iff(a, b)

    raise TypeError(f"Not a formula: {f!r}")