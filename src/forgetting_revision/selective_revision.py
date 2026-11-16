"""Selective revision: K ◦ α = K ∗ f(α)  (Fermé & Hansson, 1999).

Both operators of VFR and TSR are selective revision operators. They
share the same AGM revision ∗ and differ only in the transformation f:

  Variable Forgetting Revision:  f(α) = Forget(α, T_B)      syntactic: rewrite α, then take models
  Trust Sensitive Revision:  f(α) = Π_B[α]                  semantic:  take models, then expand
  plain AGM revision:        f(α) = α                       IdentityTransform
  any f you can tabulate:    f(α) = table[Mod(α)]           TableTransform (for counterexamples)

Each f is wrapped in an adapter that takes a formula and returns the
candidate states Mod(f(α)), so SelectiveRevision can use either one.
"""

from collections.abc import Callable, Iterable, Mapping
from dataclasses import dataclass, field
from types import MappingProxyType
from typing import Protocol

from .agm_revision import RevisionOperator
from .forget import BooleForget, ForgetOperator
from .semantics import Signature, State, meanings, models
from .syntax import Formula
from .trust import StatePartition


class Transformation(Protocol):
    """A transformation takes a formula and returns the states of a filtered
    version of it, Mod(f(α)), keeping only the parts of α that are trusted."""
    def __call__(self, alpha: Formula) -> frozenset[State]: ...


@dataclass(frozen=True)
class ForgetTransform:
    """VFR's f: forget the untrusted variables, then take models."""

    signature: Signature
    untrusted: str | Iterable[str]
    forget: ForgetOperator = field(default_factory=BooleForget)

    def __post_init__(self) -> None:
        untrusted = (
            frozenset([self.untrusted])
            if isinstance(self.untrusted, str)
            else frozenset(self.untrusted)
        )
        unknown = untrusted - set(self.signature.names)
        if unknown:
            raise ValueError(f"variables {sorted(unknown)} not in signature {self.signature.names}")
        object.__setattr__(self, "untrusted", untrusted)

    def __call__(self, alpha: Formula) -> frozenset[State]:
        return models(self.forget(alpha, self.untrusted), self.signature)


@dataclass(frozen=True)
class TrustExpansion:
    """TSR's f: take models, then expand to whole partition cells."""

    signature: Signature
    partition: StatePartition

    def __post_init__(self) -> None:
        if self.partition.width != len(self.signature):
            raise ValueError(
                f"partition is over {self.partition.width} variables, "
                f"signature has {len(self.signature)}"
            )

    def __call__(self, alpha: Formula) -> frozenset[State]:
        return self.partition.expand(models(alpha, self.signature))


@dataclass(frozen=True)
class IdentityTransform:
    """f(α) = α: no filtering at all.

    Selective revision with the identity transform IS plain AGM revision.
    It lets AGM run through the same SelectiveRevision pipeline as VFR and
    TSR, so the postulate checker treats all three families identically.
    """

    signature: Signature

    def __call__(self, alpha: Formula) -> frozenset[State]:
        return models(alpha, self.signature)


@dataclass(frozen=True)
class TableTransform:
    """f given directly as a lookup table: meaning of α -> meaning of f(α).

    Over a small signature you can write ANY transformation this way,
    including ones that are not Kuratowski functions or not partition-based.
    That is what Booth & Hunter's counterexamples need (Example 5, §7), and
    it is how the checker proves it can actually report a failure.

    The table must give a value for every one of the 2^(2^n) meanings.
    """

    signature: Signature
    table: Mapping[frozenset[State], frozenset[State]]

    def __post_init__(self) -> None:
        universe = frozenset(self.signature.states())
        # Normalise keys and values to frozensets, then freeze the mapping.
        table = {frozenset(k): frozenset(v) for k, v in self.table.items()}
        for meaning, image in table.items():
            if not meaning <= universe:
                raise ValueError(f"table key {sorted(meaning)} has states outside the signature")
            if not image <= universe:
                raise ValueError(f"table value {sorted(image)} has states outside the signature")
        if len(table) != 2 ** len(universe):
            # Keys are distinct subsets of the universe, so this count check
            # is the same as "every meaning has an entry".
            raise ValueError(
                f"table covers {len(table)} meanings, needs all {2 ** len(universe)}"
            )
        object.__setattr__(self, "table", MappingProxyType(table))

    @classmethod
    def from_function(
        cls,
        sig: Signature,
        f: Callable[[frozenset[State]], frozenset[State]],
    ) -> TableTransform:
        """Tabulate a function on meanings, e.g. lambda a: ALL if a == P else a."""
        return cls(sig, {m: f(m) for m in meanings(sig)})

    def __call__(self, alpha: Formula) -> frozenset[State]:
        return self.table[models(alpha, self.signature)]


@dataclass(frozen=True)
class SelectiveRevision:
    """K ◦ α = K ∗ f(α): transform the report, then revise by the result."""

    revision: RevisionOperator
    transform: Transformation

    @classmethod
    def vfr(
        cls,
        revision: RevisionOperator,
        sig: Signature,
        untrusted: str | Iterable[str],
        forget: ForgetOperator | None = None,
    ) -> SelectiveRevision:
        """Variable Forgetting Revision (Boole forgetting unless told otherwise)."""
        transform = ForgetTransform(sig, untrusted, forget or BooleForget())
        return cls(revision, transform)

    @classmethod
    def agm(cls, revision: RevisionOperator, sig: Signature) -> SelectiveRevision:
        """Plain AGM revision, written as selective revision with f(α) = α."""
        return cls(revision, IdentityTransform(sig))

    @classmethod
    def tsr(cls, revision: RevisionOperator, sig: Signature, partition: StatePartition) -> SelectiveRevision:
        """Booth & Hunter's Trust-Sensitive Revision."""
        return cls(revision, TrustExpansion(sig, partition))

    def belief_states(self) -> frozenset[State]:
        """Mod(K), the agent's beliefs before any report."""
        return self.revision.belief_states()

    def revise(self, alpha: Formula) -> frozenset[State]:
        """Mod(K ◦ α)."""
        return self.revision.revise(self.transform(alpha))