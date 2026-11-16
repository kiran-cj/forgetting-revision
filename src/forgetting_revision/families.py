"""Every configuration of AGM, TSR and VFR revision over a signature.

AGM, TSR and VFR are three METHODS of revision. A CONFIGURATION is one
concrete instance of a method, with all its settings fixed: a plausibility
ordering, plus a trust setting for TSR and VFR. (Booth & Hunter call each such
instance "an operator"; this package says "configuration" so that "the TSR
operator" can keep meaning the method.)

A postulate is a property of ONE configuration. To say "TSR satisfies
Deficit makeup" we have to check every TSR configuration, so we generate them all.

A configuration is fixed by its settings:

    AGM   one per ordering                      (identity transform)
    TSR   one per (ordering, state partition)
    VFR   one per (ordering, untrusted set)

The building blocks:

    orderings(sig)       every total preorder over states, as tiers.
                         These are "ordered set partitions" of 2^F; their
                         number is the Fubini number: 3, 75, 545,835 for n = 1, 2, 3.
    partitions(sig)      every partition of 2^F into cells (unordered).
                         Their number is the Bell number: 2, 15, 4,140.
    untrusted_sets(sig)  every subset of the variables: 2^n of them.

Everything is a generator, so nothing is built until it is asked for. That
matters at n = 3, where the orderings alone number half a million.
"""

from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from itertools import chain, combinations

from .agm_revision import AGMRevision
from .selective_revision import SelectiveRevision
from .semantics import Signature, State, states_str
from .trust import StatePartition

Ordering = tuple[frozenset[State], ...]


# ------------------------------------------------------------ building blocks

def _nonempty_subsets(items: Sequence[State]) -> Iterator[frozenset[State]]:
    return (
        frozenset(c)
        for c in chain.from_iterable(combinations(items, r) for r in range(1, len(items) + 1))
    )


def _ordered_partitions(items: Sequence[State]) -> Iterator[Ordering]:
    """Every way to split `items` into a sequence of non-empty tiers.

    Recursive idea: pick any non-empty subset as the bottom tier, then
    order whatever is left in every possible way.
    """
    if not items:
        yield ()
        return
    for bottom in _nonempty_subsets(items):
        rest = [s for s in items if s not in bottom]
        for higher in _ordered_partitions(rest):
            yield (bottom, *higher)


def _set_partitions(items: Sequence[State]) -> Iterator[list[frozenset[State]]]:
    """Every way to split `items` into unordered non-empty cells.

    Recursive idea: partition everything except the first item, then either
    add the first item to one of the existing cells, or give it a cell of
    its own. Each partition is produced exactly once.
    """
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for cells in _set_partitions(rest):
        for i in range(len(cells)):
            yield [*cells[:i], cells[i] | {first}, *cells[i + 1:]]
        yield [frozenset({first}), *cells]


def orderings(sig: Signature) -> Iterator[Ordering]:
    """Every total preorder over the states of sig, bottom tier first.

    The bottom tier is Mod(K), so this also covers every consistent belief
    set K, each with every faithful ordering for it.
    """
    return _ordered_partitions(sig.states())


def partitions(sig: Signature) -> Iterator[StatePartition]:
    """Every state partition over sig, from the unit partition to the trivial one."""
    return (StatePartition.from_cells(cells) for cells in _set_partitions(sig.states()))


def untrusted_sets(sig: Signature) -> Iterator[frozenset[str]]:
    """Every subset of the variables, from ∅ (full trust) to F (no trust)."""
    names = sig.names
    return (
        frozenset(c)
        for c in chain.from_iterable(combinations(names, r) for r in range(len(names) + 1))
    )


# ------------------------------------------------------------ labelled operators

@dataclass(frozen=True)
class Member:
    """One configuration of a method, together with the settings that built it.

    The parameters are kept so a counterexample can say exactly which
    configuration failed, e.g. "VFR, ordering {TT} < {TF, FT} < {FF}, untrusted {p}".
    """

    family: str
    signature: Signature
    ordering: Ordering
    operator: SelectiveRevision
    partition: StatePartition | None = None
    untrusted: frozenset[str] | None = None

    def describe(self) -> str:
        parts = [self.family, "ordering " + format_ordering(self.ordering)]
        if self.partition is not None:
            parts.append("partition " + format_partition(self.partition))
        if self.untrusted is not None:
            parts.append("untrusted " + ("{" + ", ".join(sorted(self.untrusted)) + "}" if self.untrusted else "∅"))
        return ", ".join(parts)


def format_ordering(ordering: Ordering) -> str:
    """{TT} < {TF, FT} < {FF}: most plausible tier first."""
    return " < ".join(states_str(tier) for tier in ordering)


def format_partition(partition: StatePartition) -> str:
    """{TT, FF} | {TF, FT}: cells in a fixed order, so output is reproducible."""
    cells = sorted((states_str(c) for c in partition.cells), reverse=True)
    return " | ".join(cells)


def agm_family(sig: Signature) -> Iterator[Member]:
    """Plain AGM: one configuration per ordering."""
    for ordering in orderings(sig):
        op = SelectiveRevision.agm(AGMRevision(ordering), sig)
        yield Member("AGM", sig, ordering, op)


def tsr_family(sig: Signature) -> Iterator[Member]:
    """Trust-sensitive revision: one configuration per (ordering, partition)."""
    all_partitions = list(partitions(sig))      # reused for every ordering
    for ordering in orderings(sig):
        revision = AGMRevision(ordering)
        for partition in all_partitions:
            op = SelectiveRevision.tsr(revision, sig, partition)
            yield Member("TSR", sig, ordering, op, partition=partition)


def vfr_family(sig: Signature) -> Iterator[Member]:
    """Variable forgetting revision: one configuration per (ordering, untrusted set)."""
    all_untrusted = list(untrusted_sets(sig))
    for ordering in orderings(sig):
        revision = AGMRevision(ordering)
        for untrusted in all_untrusted:
            op = SelectiveRevision.vfr(revision, sig, untrusted)
            yield Member("VFR", sig, ordering, op, untrusted=untrusted)


FAMILIES = {"AGM": agm_family, "TSR": tsr_family, "VFR": vfr_family}
