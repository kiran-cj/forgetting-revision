"""Postulate checker, part 1: the foundations.

How the checker works
---------------------
There are infinitely many formulas, but over n variables only 2^(2^n)
meanings (sets of states). So instead of trying formulas, the checker:

  1. builds one formula per meaning (its DNF),
  2. asks the REAL operator to revise by each one, once,
  3. stores the answers in an OutcomeTable:  meaning φ  ->  R(φ) = Mod(K ◦ φ),
  4. checks each postulate as a few set operations on that table.

Step 4 is only valid if the operator gives the same answer for every
formula with the same meaning. That is the Extensionality postulate, which
gets its own check on several syntactic variants per meaning.

Belief level vs state level
---------------------------
Postulates are written about beliefs (K ⊢ φ, K₁ ⊆ K₂, ...); the table holds
states. Some translations REVERSE direction: more beliefs = fewer states.
Getting that backwards is the easiest mistake to make, so every postulate
uses the named helpers below instead of writing <= directly.

    Belief level           State level            helper
    K ⊢ φ                  k ⊆ φ                  believes(k, φ)
    K ⊬ ¬φ                 k ∩ φ ≠ ∅              consistent_with(k, φ)
    K is consistent        k ≠ ∅                  is_consistent(k)
    K₁ ⊆ K₂                k₂ ⊆ k₁   (reversed)   belief_subset(k₁, k₂)
    K₁ ∩ K₂                k₁ ∪ k₂   (reversed)   belief_meet(k₁, k₂)
    Cn(K ∪ {φ})            k ∩ φ                  expansion(k, φ)
    φ ∨ ψ, φ ∧ ψ, ¬φ       φ ∪ ψ, φ ∩ ψ, 2^F − φ   disj, conj, OutcomeTable.neg
"""

from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from functools import cached_property
from types import MappingProxyType
from typing import Protocol

from .semantics import Signature, State, dnf, meanings
from .syntax import Formula

StateSet = frozenset[State]


class BeliefChangeOperator(Protocol):
    """Anything the checker can test: it has beliefs, and it revises by formulas.

    SelectiveRevision already fits, so AGM, TSR and VFR all qualify without
    any changes. So would a future operator that is not selective revision.
    """

    def belief_states(self) -> StateSet:
        """Mod(K)."""
        ...

    def revise(self, alpha: Formula) -> StateSet:
        """Mod(K ◦ α)."""
        ...


# ------------------------------------------------------------ outcome table

@dataclass(frozen=True)
class OutcomeTable:
    """Every revision result of one operator, indexed by meaning.

    Usage inside a postulate:
        R = OutcomeTable.build(op, sig)
        R.k            Mod(K)
        R(phi)         Mod(K ◦ φ), where phi is a set of states
        R.meanings     every φ to quantify over
        R.neg(phi)     the meaning of ¬φ
    """

    signature: Signature
    k: StateSet
    outcomes: Mapping[StateSet, StateSet]

    @classmethod
    def build(cls, op: BeliefChangeOperator, sig: Signature) -> OutcomeTable:
        """Call op.revise once per meaning, on that meaning's DNF formula."""
        outcomes = {m: op.revise(dnf(m, sig)) for m in meanings(sig)}
        return cls(sig, op.belief_states(), MappingProxyType(outcomes))

    def __call__(self, phi: StateSet) -> StateSet:
        """R(φ) = Mod(K ◦ φ)."""
        return self.outcomes[phi]

    @cached_property
    def universe(self) -> StateSet:
        """2^F, the meaning of ⊤."""
        return frozenset(self.signature.states())

    @property
    def meanings(self) -> list[StateSet]:
        return list(self.outcomes)

    def neg(self, phi: StateSet) -> StateSet:
        """The meaning of ¬φ."""
        return self.universe - phi

    def supersets(self, phi: StateSet) -> Iterator[StateSet]:
        """Every ψ with φ ⊆ ψ.

        As ψ ranges over ALL meanings, φ ∨ ψ ranges over exactly the
        supersets of φ. Looping over these instead of over every ψ gives the
        same answer for postulates about φ ∨ ψ, with far fewer cases.
        """
        return (m for m in self.outcomes if phi <= m)


# ------------------------------------------------------------ translation helpers
# One function per row of the table in the module docstring. Arguments are
# sets of states; the NAMES say what they mean at the belief level.

def believes(k: StateSet, phi: StateSet) -> bool:
    """K ⊢ φ   ⇔   k ⊆ φ   (every state the agent considers possible satisfies φ)"""
    return k <= phi


def consistent_with(k: StateSet, phi: StateSet) -> bool:
    """K ⊬ ¬φ   ⇔   k ∩ φ ≠ ∅   (φ is compatible with what the agent believes)"""
    return bool(k & phi)


def is_consistent(k: StateSet) -> bool:
    """K ⊬ ⊥   ⇔   k ≠ ∅"""
    return bool(k)


def belief_subset(k1: StateSet, k2: StateSet) -> bool:
    """K₁ ⊆ K₂   ⇔   k₂ ⊆ k₁   REVERSED: believing more means ruling out more states."""
    return k2 <= k1


def belief_meet(k1: StateSet, k2: StateSet) -> StateSet:
    """Mod(K₁ ∩ K₂)   =   k₁ ∪ k₂   REVERSED: shared beliefs allow the states of either."""
    return k1 | k2


def expansion(k: StateSet, phi: StateSet) -> StateSet:
    """Mod(Cn(K ∪ {φ}))   =   k ∩ φ   (add φ to K without any revision)"""
    return k & phi


def disj(phi: StateSet, psi: StateSet) -> StateSet:
    """Mod(φ ∨ ψ) = φ ∪ ψ"""
    return phi | psi


def conj(phi: StateSet, psi: StateSet) -> StateSet:
    """Mod(φ ∧ ψ) = φ ∩ ψ"""
    return phi & psi
