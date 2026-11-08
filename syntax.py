"""
SYNTAX layer : what a formula IS

The formula is to be stored as a tree - Abstract Syntax Tree (AST) - where each
node is a formula and the children of a node are the sub-formulas of that formula. 
The root of the tree is the formula itself.

    p ∧ ~q is stored as And(p, Not(q))
            And
          /    \\
        p       Not
                 |
                 q
                 
Every node is a *frozen* dataclass, which gives us three things for free:
  - immutability: a formula can never be changed after creation, so
    operations like Forget always build a NEW formula instead of editing one
  - __eq__: two trees with identical structure compare equal
  - __hash__: formulas can be put in sets and used as dict keys

"""

from dataclasses import dataclass

class Formula:
    """
    Base class for all nodes. Overloads operations to allow for easy construction of
    formulas and they can be written naturally in Python.
      
        ~p        Not(p)
        p & q     And(p, q)
        p | q     Or(p, q)
        p >> q    Implies(p, q)
        p.iff(q)  Iff(p, q)
      
    WARNING about precedence: >> binds TIGHTER than & and |.
    So  p & q >> r  means  p & (q >> r).  Always bracket implications.
    
    """

    __slots__ = () # this class adds no attribute of its own -- restricts it from creating a __dict__ for each instance, saving memory

    def __invert__(self) -> Formula:
        return Not(self)

    def __and__(self, other: Formula) -> Formula:
        return And(self, other)

    def __or__(self, other: Formula) -> Formula:
        return Or(self, other)

    def __rshift__(self, other: Formula) -> Formula:
        return Implies(self, other)

    def iff(self, other: Formula) -> Formula:
        return Iff(self, other)

    def __str__(self) -> str:
        return to_str(self)

# Connectives of the trees are the operators and the leaves are either variables or constants.


# ------------------------ Leafs ---------------------------- #

@dataclass(frozen=True, slots=True)
class Var(Formula):
    """A propositional variable, e.g. Var("p")."""
    name: str


@dataclass(frozen=True, slots=True)
class Const(Formula):
    """A truth constant: Const(True) is ⊤, Const(False) is ⊥."""
    value: bool

TOP = Const(True)
BOTTOM = Const(False)

# ------------------------ Connectives ------------------------ #
@dataclass(frozen=True, slots=True)
class Not(Formula):
    operand: Formula


@dataclass(frozen=True, slots=True)
class And(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True, slots=True)
class Or(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True, slots=True)
class Implies(Formula):
    left: Formula
    right: Formula


@dataclass(frozen=True, slots=True)
class Iff(Formula):
    left: Formula
    right: Formula


_SYMBOLS = {And: "∧", Or: "∨", Implies: "→", Iff: "↔"}


def to_str(f: Formula) -> str:
    """Retuns a formula with logic symbols. Binary connectives are always
    bracketed, so the printed form is never ambiguous."""
    match f:
        case Const(value):
            return "⊤" if value else "⊥"
        case Var(name):
            return name
        case Not(operand):
            return f"¬{to_str(operand)}"
        case And(l, r) | Or(l, r) | Implies(l, r) | Iff(l, r):
            return f"({to_str(l)} {_SYMBOLS[type(f)]} {to_str(r)})"
    raise TypeError(f"Not a formula: {f!r}")


def variables(f: Formula) -> frozenset[str]:
    """The set of variable names that occur in f."""
    match f:
        case Const():
            return frozenset()
        case Var(name):
            return frozenset({name})
        case Not(operand):
            return variables(operand)
        case And(l, r) | Or(l, r) | Implies(l, r) | Iff(l, r):
            return variables(l) | variables(r)
    raise TypeError(f"Not a formula: {f!r}")


    
    