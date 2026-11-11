"""Booth & Hunter's domain-specific trust as a partition of the state space.

Agent A associates a partition of 2^F with each source B. Two states share a
cell exactly when A does not trust B to tell them apart.

An information alpha from B is then read as evidence for every state in any cell that
contains a model of alpha:
    Pi[alpha] = union of the cells that intersect Mod(alpha)

Trust-sensitive revision is ordinary AGM revision by that expanded set of states.
"""

from dataclasses import dataclass
from functools import cached_property
from itertools import product
from typing import Callable, Hashable, Iterable

from .semantics import Signature, State


def _all_states(width: int) -> frozenset[State]:
    return frozenset(product((True, False), repeat=width))


@dataclass(frozen=True)
class StatePartition:
    """A partition of all states over a signature into trust cells.
    Cells are unordered (unlike ranking tiers), so they live in a frozenset."""

    cells: frozenset[frozenset[State]]

    # The post_init constructor needs to be implemented as a reusable code later on.
    def __post_init__(self) -> None:
        if not self.cells:
            raise ValueError("a partition needs at least one cell")
        if any(not cell for cell in self.cells):
            raise ValueError("cells must be non-empty")

        widths = {len(s) for cell in self.cells for s in cell}
        if len(widths) != 1:
            raise ValueError(f"all states must have the same length, got {sorted(widths)}")

        seen: set[State] = set()
        for cell in self.cells:
            overlap = seen & cell
            if overlap:
                raise ValueError(f"states in more than one cell: {sorted(overlap)}")
            seen |= cell

        (width,) = widths
        missing = _all_states(width) - seen
        if missing:
            raise ValueError(f"partition does not cover all states, missing: {sorted(missing)}")

    @classmethod
    def from_cells(cls, cells: Iterable[Iterable[State]]) -> StatePartition:
        """Build from any nested iterables, e.g. a list of lists of states."""
        return cls(frozenset(frozenset(cell) for cell in cells))

    @classmethod
    def from_key(cls, sig: Signature, key: Callable[[State], Hashable]) -> StatePartition:
        """States with equal key(s) share a cell.

        This is the equivalence relation ~B written as a function: s ~B t
        iff key(s) == key(t). Any key gives a valid partition.
        """
        groups: dict[Hashable, set[State]] = {}
        for s in sig.states():
            groups.setdefault(key(s), set()).add(s)
        return cls.from_cells(groups.values())

    @classmethod
    def from_untrusted(cls, sig: Signature, untrusted: str | Iterable[str]) -> StatePartition:
        """The partition induced by forgetting the untrusted variables.

        Two states are indistinguishable iff they agree on every *trusted*
        variable, i.e. they differ only on untrusted ones."""
        if isinstance(untrusted, str):       # same guard as BooleForget
            untrusted = [untrusted]
        untrusted = frozenset(untrusted)
        unknown = untrusted - set(sig.names)
        if unknown:
            raise ValueError(f"variables {sorted(unknown)} not in signature {sig.names}")
        trusted = [i for i, name in enumerate(sig.names) if name not in untrusted]
        return cls.from_key(sig, lambda s: tuple(s[i] for i in trusted))

    @classmethod
    def trivial(cls, sig: Signature) -> StatePartition:
        """One cell: the source is trusted on nothing."""
        return cls.from_cells([sig.states()])

    @classmethod
    def unit(cls, sig: Signature) -> StatePartition:
        """Singleton cells: the source is trusted on everything."""
        return cls.from_cells([s] for s in sig.states())

    @cached_property
    def _cell_index(self) -> dict[State, frozenset[State]]:
        """Lookup table from each state to its cell, built once."""
        return {s: cell for cell in self.cells for s in cell}

    @property
    def width(self) -> int:
        return len(next(iter(next(iter(self.cells)))))

    def cell_of(self, state: State) -> frozenset[State]:
        """Pi(s): the cell containing a state (Definition 1)."""
        try:
            return self._cell_index[state]
        except KeyError:
            raise ValueError(f"state {state} is not in this partition") from None

    def expand(self, candidates: frozenset[State]) -> frozenset[State]:
        """Pi[alpha]: union of the cells containing a candidate.
        This is the trust expansion: the states of alpha_K^A(B)."""
        return frozenset().union(*(self.cell_of(s) for s in candidates))