"""
AGM belief revision is represented via a plausibility ranking over states.

Katsuno & Mendelzon (1992) showed that every AGM revision operator for a
belief set K corresponds to a total preorder over states in which the models
of K are the most plausible ("faithful"). Revising by beta then means:

    Mod(K * beta) = the most plausible states among Mod(beta)

This module represents that preorder as a stack of *tiers*: tier 0 holds the
most plausible states, tier 1 the next, and so on. Everything is done on sets
of states, so revision never has to look at formula syntax.
"""

from collections.abc import Iterable
from dataclasses import dataclass
from functools import cached_property
from itertools import product
from typing import Protocol

from .semantics import State


class RevisionOperator(Protocol):
    """A revision operator holds the agent's current beliefs and, given the
    states of a new piece of information, returns the most plausible of them."""

    def belief_states(self) -> frozenset[State]:
        """Mod(K): the states the agent currently considers possible."""
        ...

    def revise(self, candidates: frozenset[State]) -> frozenset[State]:
        """Mod(K ∗ β), given candidates = Mod(β)."""
        ...


@dataclass(frozen=True)
class AGMRevision:
    """An AGM revision operator given by an explicit total preorder over states."""

    tiers: tuple[frozenset[State], ...]

    def __post_init__(self) -> None:
        """Does several validation checks on the tiers after initialization.
            1. There is at least one tier.
            2. No tier is empty.
            3. All states have the same length.
            4. No state appears in more than one tier.
            5. Every state of the signature appears in some tier.
        """
        if not self.tiers:
            raise ValueError("a ranking needs at least one tier")
        if any(not tier for tier in self.tiers):
            raise ValueError("tiers must be non-empty")

        widths = {len(s) for tier in self.tiers for s in tier}
        if len(widths) != 1:
            raise ValueError(f"all states must have the same length, got {sorted(widths)}")

        seen: set[State] = set()
        for tier in self.tiers:
            overlap = seen & tier
            if overlap:
                raise ValueError(f"states ranked more than once: {sorted(overlap)}")
            seen |= tier

        (width,) = widths
        missing = set(product((True, False), repeat=width)) - seen
        if missing:
            raise ValueError(f"ranking is not total, unranked states: {sorted(missing)}")

    @classmethod
    def from_tiers(cls, tiers: Iterable[Iterable[State]]) -> AGMRevision:
        """Build from any nested iterables, e.g. a list of lists of states."""
        return cls(tuple(frozenset(tier) for tier in tiers))

    @classmethod
    def from_dalal(cls, k_states: Iterable[State]) -> AGMRevision:
        """
        Dalal's operator: rank each state by its Hamming distance to Mod(K).
            example: K = p ∧ q, Mod(K) = {TT}:
            then rank(TT)=0, rank(TF)=1, rank(FT)=1, rank(FF)=2

        Only Mod(K) is needed; the ordering is derived from it. States that
        differ from some model of K in fewer variables are more plausible.
        """
        k = frozenset(k_states)
        if not k:
            raise ValueError("Dalal revision needs a consistent K (non-empty Mod(K))")
        widths = {len(s) for s in k}
        if len(widths) != 1:
            raise ValueError("all states in K must have the same length")
        (width,) = widths #width is the number of variables in the signature

        def distance(s: State) -> int:
            """Calculates the hamming distance of a state s to the closest model in k."""
            return min(sum(a != b for a, b in zip(s, m)) for m in k)

        buckets: dict[int, set[State]] = {}
        for s in product((True, False), repeat=width):
            buckets.setdefault(distance(s), set()).add(s)
        return cls.from_tiers(buckets[d] for d in sorted(buckets))

    @cached_property
    def universe(self) -> frozenset[State]:
        """All states the ranking covers (= every state of the signature)."""
        return frozenset().union(*self.tiers)

    @property
    def width(self) -> int:
        """Number of variables in the signature."""
        return len(next(iter(self.tiers[0])))

    def rank(self, state: State) -> int:
        """Tier index of a state: 0 is the most plausible."""
        for i, tier in enumerate(self.tiers):
            if state in tier:
                return i
        raise ValueError(f"state {state} is not ranked")

    def belief_states(self) -> frozenset[State]:
        """Mod(K) is the bottom tier, so the ranking is faithful by construction."""
        return self.tiers[0]

    def revise(self, candidates: frozenset[State]) -> frozenset[State]:
        """Return the most plausible candidates: Mod(K * beta).

        Walk up from the bottom tier and stop at the first tier that contains
        any candidate. If there are no candidates (beta is inconsistent), the
        result is empty, i.e. an inconsistent belief set, which in-turn performs no
        revision and the belief set remains unchanged.
        """
        unknown = candidates - self.universe
        if unknown:
            raise ValueError(f"candidates contain unranked states: {sorted(unknown)}")
        for tier in self.tiers:
            hit = tier & candidates
            if hit:
                return hit
        return frozenset()