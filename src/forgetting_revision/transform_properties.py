"""Properties of a transformation function f, checked on f alone.

Selective revision is K ◦ α = K ∗ f(α). The postulates in postulates.py are
about the whole operator ◦; the properties here are about f by itself, with
no ordering and no K. Booth & Hunter (§4.2) and the dissertation (§6.2) use
them to say which postulates ◦ inherits:

    f1-f5  Kuratowski properties   ->  ◦ satisfies B&H Props 3, 4 and 15
    f6     Monotonicity             (follows from f4 + f5)
    f7     Pawlak                  ->  with f1-f5: f comes from a state partition
    f8     Conjunctive weakening    (B&H: with f1-f5, equivalent to Pawlak)
    f9     Trust symmetry           (B&H: with f1-f5, equivalent to Pawlak)

Yao's theorem (B&H Prop 8): f is f_Π for some partition Π  iff  f satisfies
f1-f5 and Pawlak. induced_partition() recovers that Π. Running it on every
ForgetTransform is a computational check of the dissertation's main claim,
VFR ⊆ TSR, for the signature tested.

Same pattern as postulates.py: f is tabulated once per meaning, every
property is a generator of (holds, witness) cases, and a decorator registers
each property with its metadata.
"""

from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from functools import cached_property
from types import MappingProxyType

from .postulates import Witness, format_witness, variants
from .selective_revision import Transformation
from .semantics import Signature, State, dnf, meanings
from .trust import StatePartition

StateSet = frozenset[State]
Cases = Iterator[tuple[bool, Witness]]


# ------------------------------------------------------------ the table of f

@dataclass(frozen=True)
class TransformTable:
    """f on every meaning: φ -> Mod(f(φ)), computed once from φ's DNF.

        F = TransformTable.build(f, sig)
        F(phi)        Mod(f(φ))
        F.neg(phi)    the meaning of ¬φ
    """

    signature: Signature
    images: Mapping[StateSet, StateSet]

    @classmethod
    def build(cls, f: Transformation, sig: Signature) -> TransformTable:
        return cls(sig, MappingProxyType({m: f(dnf(m, sig)) for m in meanings(sig)}))

    def __call__(self, phi: StateSet) -> StateSet:
        return self.images[phi]

    @cached_property
    def universe(self) -> StateSet:
        return frozenset(self.signature.states())

    @property
    def meanings(self) -> list[StateSet]:
        return list(self.images)

    def neg(self, phi: StateSet) -> StateSet:
        return self.universe - phi

    def supersets(self, phi: StateSet) -> Iterator[StateSet]:
        return (m for m in self.images if phi <= m)


# ------------------------------------------------------------ registry

CheckFn = Callable[[TransformTable, Transformation], Cases]

KURATOWSKI = "Kuratowski"
DERIVED = "derived"
PARTITION = "partition-induced"


@dataclass(frozen=True)
class TransformPropertyResult:
    prop: TransformProperty
    triggered: int
    counterexample: Witness | None

    @property
    def holds(self) -> bool:
        return self.counterexample is None

    def explain(self) -> str:
        if self.counterexample is None:
            return f"{self.prop.code} {self.prop.name}: holds on {self.triggered} cases"
        return f"{self.prop.code} {self.prop.name}: FAILS at {format_witness(self.counterexample)}"


@dataclass(frozen=True)
class TransformProperty:
    code: str               # "f1" .. "f9", as in the catalogue
    name: str
    kind: str               # KURATOWSKI, DERIVED or PARTITION
    source: str
    statement: str
    check: CheckFn

    def __call__(self, table: TransformTable, f: Transformation) -> TransformPropertyResult:
        triggered = 0
        for ok, witness in self.check(table, f):
            triggered += 1
            if not ok:
                return TransformPropertyResult(self, triggered, witness)
        return TransformPropertyResult(self, triggered, None)


PROPERTIES: dict[str, TransformProperty] = {}


def transform_property(code: str, name: str, kind: str, source: str, statement: str) -> Callable[[CheckFn], CheckFn]:
    def register(check: CheckFn) -> CheckFn:
        if name in PROPERTIES or any(p.code == code for p in PROPERTIES.values()):
            raise ValueError(f"property {code} / {name!r} registered twice")
        PROPERTIES[name] = TransformProperty(code, name, kind, source, statement, check)
        return check
    return register


def check_transform(
    f: Transformation,
    sig: Signature,
    properties: Iterable[TransformProperty] | None = None,
) -> dict[str, TransformPropertyResult]:
    """Check f against the given properties (default: all nine)."""
    table = TransformTable.build(f, sig)
    chosen = PROPERTIES.values() if properties is None else properties
    return {p.name: p(table, f) for p in chosen}


# ------------------------------------------------------------ f1-f5: Kuratowski

@transform_property("f1", "Falsity preservation", KURATOWSKI, "B&H §4.2; dissertation §6.2",
                    "f(⊥) ≡ ⊥")
def falsity_preservation(F: TransformTable, f: Transformation) -> Cases:
    empty: StateSet = frozenset()
    yield F(empty) == empty, (("f(⊥)", F(empty)),)


@transform_property("f2", "Implication", KURATOWSKI, "B&H §4.2; dissertation §6.2",
                    "φ ⊢ f(φ)")
def implication(F: TransformTable, f: Transformation) -> Cases:
    for phi in F.meanings:
        yield phi <= F(phi), (("φ", phi), ("f(φ)", F(phi)))


@transform_property("f3", "Idempotence", KURATOWSKI, "B&H §4.2; dissertation §6.2",
                    "f(f(φ)) ≡ f(φ)")
def idempotence(F: TransformTable, f: Transformation) -> Cases:
    for phi in F.meanings:
        yield F(F(phi)) == F(phi), (("φ", phi), ("f(φ)", F(phi)), ("f(f(φ))", F(F(phi))))


@transform_property("f4", "Extensionality", KURATOWSKI, "B&H §4.2; dissertation §6.2",
                    "if φ ≡ ψ then f(φ) ≡ f(ψ)")
def extensionality(F: TransformTable, f: Transformation) -> Cases:
    # Like postulate #6, the one property that calls f again: on five
    # spellings of each meaning. For ForgetTransform this exercises the
    # syntactic machinery (substitute, simplify) on many shapes of input.
    for phi in F.meanings:
        for formula in variants(phi, F.signature):
            image = f(formula)
            yield image == F(phi), (("φ", phi), ("spelt as", formula),
                                    ("f via DNF", F(phi)), ("f via this", image))


@transform_property("f5", "Disjunctive distribution", KURATOWSKI, "B&H §4.2; dissertation §6.2",
                    "f(φ ∨ ψ) ≡ f(φ) ∨ f(ψ)")
def disjunctive_distribution(F: TransformTable, f: Transformation) -> Cases:
    for phi in F.meanings:
        for psi in F.meanings:
            yield (F(phi | psi) == F(phi) | F(psi),
                   (("φ", phi), ("ψ", psi), ("f(φ∨ψ)", F(phi | psi)), ("f(φ) ∨ f(ψ)", F(phi) | F(psi))))


# ------------------------------------------------------------ f6: derived

@transform_property("f6", "Monotonicity", DERIVED, "B&H §4.2",
                    "if φ ⊢ ψ then f(φ) ⊢ f(ψ)")
def monotonicity(F: TransformTable, f: Transformation) -> Cases:
    for phi in F.meanings:
        for psi in F.supersets(phi):            # φ ⊢ ψ  ⇔  φ ⊆ ψ
            yield F(phi) <= F(psi), (("φ", phi), ("ψ", psi), ("f(φ)", F(phi)), ("f(ψ)", F(psi)))


# ------------------------------------------------------------ f7-f9: partition-induced

@transform_property("f7", "Pawlak", PARTITION, "B&H §4.2, Prop 8 (Yao); dissertation §6.2",
                    "f(¬f(φ)) ≡ ¬f(φ)")
def pawlak(F: TransformTable, f: Transformation) -> Cases:
    for phi in F.meanings:
        not_f = F.neg(F(phi))
        yield F(not_f) == not_f, (("φ", phi), ("¬f(φ)", not_f), ("f(¬f(φ))", F(not_f)))


@transform_property("f8", "Conjunctive weakening", PARTITION, "B&H §4.2 (used in Prop 9)",
                    "f(φ) ∧ f(ψ) ⊢ f(φ ∧ f(ψ))")
def conjunctive_weakening(F: TransformTable, f: Transformation) -> Cases:
    for phi in F.meanings:
        for psi in F.meanings:
            left = F(phi) & F(psi)
            right = F(phi & F(psi))
            yield left <= right, (("φ", phi), ("ψ", psi), ("f(φ) ∧ f(ψ)", left), ("f(φ ∧ f(ψ))", right))


@transform_property("f9", "Trust symmetry", PARTITION, "B&H §4.2 (cf. Liau 2003, Axiom C3)",
                    "f(φ) ≡ φ iff f(¬φ) ≡ ¬φ")
def trust_symmetry(F: TransformTable, f: Transformation) -> Cases:
    # "A trusts B on φ iff A trusts B on ¬φ."
    for phi in F.meanings:
        not_phi = F.neg(phi)
        yield ((F(phi) == phi) == (F(not_phi) == not_phi),
               (("φ", phi), ("f(φ)", F(phi)), ("¬φ", not_phi), ("f(¬φ)", F(not_phi))))


# ------------------------------------------------------------ Yao's theorem

def is_kuratowski(results: Mapping[str, TransformPropertyResult]) -> bool:
    """f1-f5 all hold (B&H Definition 8)."""
    return all(r.holds for r in results.values() if r.prop.kind == KURATOWSKI)


def induced_partition(f: Transformation, sig: Signature) -> StatePartition | None:
    """The partition Π with f = f_Π, or None if f is not partition-based.

    By Yao's theorem such a Π exists iff f is Kuratowski and Pawlak. Its
    cells are then f({s}) for each state s: the states the source cannot
    tell apart from s.
    """
    needed = [p for p in PROPERTIES.values() if p.kind == KURATOWSKI or p.name == "Pawlak"]
    if not all(r.holds for r in check_transform(f, sig, needed).values()):
        return None
    F = TransformTable.build(f, sig)
    return StatePartition.from_cells({F(frozenset({s})) for s in sig.states()})
