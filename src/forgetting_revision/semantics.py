"""
Semantics layer: what a formula MEANS.

Terminology:
  - Signature  F      : the fixed, ordered set of variables, e.g. (p, q)
  - State / valuation : one truth assignment to every variable in F.
                        Stored as a tuple of bools in signature order,
                        so (True, False) is the state "TF" (p=T, q=F).
  - 2^F               : Signature.states(), all 2^n (n is the number of 
                        variables in the signature) states
  - Mod(α)            : models(α, sig), the set of states where α is true
  - meaning           : a set of states. Every formula has exactly one meaning,
                        Mod(α), and there are only 2^(2^n) meanings, so
                        meanings(sig) lists every formula up to equivalence.
"""

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from itertools import chain, combinations, product

from .syntax import (
    BOTTOM,
    TOP,
    And,
    Const,
    Formula,
    Iff,
    Implies,
    Not,
    Or,
    Var,
    variables,
)

State = tuple[bool, ...]

@dataclass(frozen=True, slots=True)
class Signature:
    names: tuple[str, ...]
    
    def __post_init__(self) -> None:
        if isinstance(self.names, str):
            raise TypeError(
                f"names must be a tuple of strings; use Signature.of({self.names!r}) "
                "to split a space-separated string"
            )
        if len(set(self.names)) != len(self.names):
            # keep your existing message text so any `match=` in your tests still passes
            raise ValueError(f"Duplicate variable names in signature: {self.names}")

    @classmethod
    def of(cls, names: str | Iterable[str]) -> Signature:
        """Signature.of("p q r") or Signature.of(["p", "q", "r"])"""
        if isinstance(names, str):
            names = names.split()
        names = tuple(names)
        if len(set(names)) != len(names):
            raise ValueError(f"Duplicate variable names in {names}")
        return cls(names)
    
    def __len__(self) -> int:
        return len(self.names)
      
    def states(self) -> list[State]:
        """All 2^n states, ordered TT..T first and FF..F last"""
        return list(product((True, False), repeat=len(self.names)))

    def assignment(self, state: State) -> dict[str, bool]:
        """Turn a state tuple into a {variable: value} lookup"""
        return dict(zip(self.names, state, strict=True))

def state_str(state: State) -> str:
      return "".join("T" if v else "F" for v in state)

def states_str(states: Iterable[State]) -> str:
    """A set of states -> {TF, TT}"""
    return "{" + ", ".join(sorted((state_str(s) for s in states), reverse=True)) + "}"


# ------------------------- EVALUATION ------------------------- #

def evaluate(f: Formula, assignment: Mapping[str, bool]) -> bool:
    """Is f true under this assignment? A recursive walk down the tree:
    each node asks its children for their values, and variables (the base
    case) look themselves up in the assignment."""
    match f:
        case Const(value):
            return value
        case Var(name):
            return assignment[name]
        case Not(a):
            return not evaluate(a, assignment)
        case And(a, b):
            return evaluate(a, assignment) and evaluate(b, assignment)
        case Or(a, b):
            return evaluate(a, assignment) or evaluate(b, assignment)
        case Implies(a, b):
            return (not evaluate(a, assignment)) or evaluate(b, assignment)
        case Iff(a, b):
            return evaluate(a, assignment) == evaluate(b, assignment)
    raise TypeError(f"Not a formula: {f!r}")

def _check(f: Formula, sig: Signature) -> None:
    """Raise ValueError if f uses variables not in sig."""
    missing = variables(f) - set(sig.names)
    if missing:
        raise ValueError(f"{f} uses variables {sorted(missing)} not in signature {sig.names}")


def models(f: Formula, sig: Signature) -> frozenset[State]:
    """Mod(f): every state of the signature in which f is true."""
    _check(f, sig)
    return frozenset(s for s in sig.states() if evaluate(f, sig.assignment(s)))


# ------------------------- Logical Operations ------------------------- #

def entails(a: Formula, b: Formula, sig: Signature) -> bool:
    """a ⊢ b  iff  Mod(a) ⊆ Mod(b)"""
    return models(a, sig) <= models(b, sig)


def equivalent(a: Formula, b: Formula, sig: Signature) -> bool:
    """a ≡ b  iff  Mod(a) = Mod(b)"""
    return models(a, sig) == models(b, sig)


def satisfiable(f: Formula, sig: Signature) -> bool:
    """Checks if at least one model exists"""
    return bool(models(f, sig))


def is_tautology(f: Formula, sig: Signature) -> bool:
    """Checks if all states are models"""
    return models(f, sig) == frozenset(sig.states())


# ------------------------- From states back to formulas ------------------------- #
# models() goes formula -> states. These go the other way: given a set of
# states, build a formula whose models are exactly that set. The postulate
# checker needs this because it quantifies over meanings (sets of states) but
# operators only accept formulas.

def meanings(sig: Signature) -> list[frozenset[State]]:
    """Every set of states over sig: 2^(2^n) of them (16 for two variables).

    Ordered by size, then by state order, so the list is the same on every run:
    ∅ first, all states last.
    """
    states = sig.states()
    return [
        frozenset(c)
        for c in chain.from_iterable(combinations(states, r) for r in range(len(states) + 1))
    ]


def _literal(name: str, value: bool) -> Formula:
    return Var(name) if value else Not(Var(name))


def state_formula(state: State, sig: Signature) -> Formula:
    """prop(s), B&H Definition 5: the conjunction of literals true in s.

    For sig (p, q), the state TF becomes p ∧ ¬q. Its only model is s itself.
    """
    literals = [_literal(n, v) for n, v in zip(sig.names, state, strict=True)]
    formula: Formula = literals[0]
    for lit in literals[1:]:
        formula = And(formula, lit)
    return formula


def dnf(states: Iterable[State], sig: Signature) -> Formula:
    """A formula whose models are exactly `states` (B&H Definitions 6-7).

    Disjunctive normal form: one conjunction per state, OR-ed together.
    The empty set gives ⊥. States are taken TT..T first, so output is stable.
    """
    terms = [state_formula(s, sig) for s in sorted(set(states), reverse=True)]
    if not terms:
        return BOTTOM
    formula: Formula = terms[0]
    for term in terms[1:]:
        formula = Or(formula, term)
    return formula


def cnf(states: Iterable[State], sig: Signature) -> Formula:
    """The same meaning as dnf(states), written differently.

    Conjunctive normal form: for every state OUTSIDE the set, add "not that
    state". The full set of states gives ⊤. Having two syntactically different
    formulas per meaning is what lets the checker test Extensionality.
    """
    inside = set(states)
    excluded = [s for s in sig.states() if s not in inside]
    if not excluded:
        return TOP
    clauses = [Not(state_formula(s, sig)) for s in excluded]
    formula: Formula = clauses[0]
    for clause in clauses[1:]:
        formula = And(formula, clause)
    return formula
