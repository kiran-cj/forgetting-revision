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
"""

from itertools import product
from dataclasses import dataclass
from collections.abc import Iterable, Mapping
from .syntax import Formula, Var, Const, Not, And, Or, Implies, Iff, variables

State = tuple[bool, ...]

@dataclass(frozen=True, slots=True)
class Signature:
    names: tuple[str, ...]
    
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
        return dict(zip(self.names, state))

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
    return len(models(f, sig)) == 2 ** len(sig)
