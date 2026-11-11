"""Selective revision: K ◦ α = K ∗ f(α)  (Fermé & Hansson, 1999).

Both operators of VFR and TSR are selective revision operators. They
share the same AGM revision ∗ and differ only in the transformation f:

  Variable Forgetting Revision:  f(α) = Forget(α, T_B)      syntactic: rewrite α, then take models
  Trust Sensitive Revision:  f(α) = Π_B[α]                  semantic:  take models, then expand

Each f is wrapped in an adapter that takes a formula and returns the
candidate states Mod(f(α)), so SelectiveRevision can use either one.
"""

from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Protocol

from .agm_revision import RevisionOperator
from .forget import BooleForget, ForgetOperator
from .semantics import Signature, State, models
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
    def tsr(cls, revision: RevisionOperator, sig: Signature, partition: StatePartition) -> SelectiveRevision:
        """Booth & Hunter's Trust-Sensitive Revision."""
        return cls(revision, TrustExpansion(sig, partition))

    def belief_states(self) -> frozenset[State]:
        """Mod(K), the agent's beliefs before any report."""
        return self.revision.belief_states()

    def revise(self, alpha: Formula) -> frozenset[State]:
        """Mod(K ◦ α)."""
        return self.revision.revise(self.transform(alpha))