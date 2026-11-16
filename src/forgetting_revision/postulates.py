"""Postulate checker: the 24 operator postulates and the machinery they run on.

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
    Cn(K₁ ∪ K₂)            k₁ ∩ k₂                belief_join(k₁, k₂)
    Cn(K ∪ {φ})            k ∩ φ                  expansion(k, φ)
    φ ∨ ψ, φ ∧ ψ, ¬φ       φ ∪ ψ, φ ∩ ψ, 2^F − φ   disj, conj, OutcomeTable.neg
"""

from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass
from functools import cached_property
from types import MappingProxyType
from typing import Protocol

from .semantics import Signature, State, cnf, dnf, meanings, states_str
from .syntax import BOTTOM, TOP, And, Formula, Not, Or

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


def belief_join(k1: StateSet, k2: StateSet) -> StateSet:
    """Mod(Cn(K₁ ∪ K₂))   =   k₁ ∩ k₂   (pool two belief sets: only states allowed by both survive)"""
    return k1 & k2


def expansion(k: StateSet, phi: StateSet) -> StateSet:
    """Mod(Cn(K ∪ {φ}))   =   k ∩ φ   (add φ to K without any revision)"""
    return k & phi


def disj(phi: StateSet, psi: StateSet) -> StateSet:
    """Mod(φ ∨ ψ) = φ ∪ ψ"""
    return phi | psi


def conj(phi: StateSet, psi: StateSet) -> StateSet:
    """Mod(φ ∧ ψ) = φ ∩ ψ"""
    return phi & psi


# ============================================================ the registry
#
# Every postulate is a generator of CASES. A case is one choice of inputs
# (φ, or φ and ψ, ...) for which the postulate's premise holds. For each case
# the generator yields:
#
#     (conclusion_holds, witness)
#
# where witness is a tuple of ("label", value) pairs describing the case,
# e.g. (("φ", {TT}), ("K◦φ", {TF})). The runner counts the cases (that is the
# premise count), and stops at the first case whose conclusion fails: its
# witness IS the counterexample.
#
# Cases where the premise is false are simply not yielded, so a postulate
# with no premise (like Success) yields one case per input.

Witness = tuple[tuple[str, object], ...]
Cases = Iterator[tuple[bool, Witness]]
CheckFn = Callable[[OutcomeTable, BeliefChangeOperator], Cases]


def format_witness(witness: Witness) -> str:
    """("φ", {TT, TF}), ("K◦φ", {FT})  ->  φ = {TT, TF}, K◦φ = {FT}"""
    def show(value: object) -> str:
        if isinstance(value, frozenset):
            return states_str(value) if value else "∅"
        return str(value)
    return ", ".join(f"{label} = {show(value)}" for label, value in witness)


@dataclass(frozen=True)
class PostulateResult:
    """The outcome of checking ONE postulate on ONE operator."""

    postulate: Postulate
    triggered: int                       # how many cases met the premise
    counterexample: Witness | None       # None when the postulate holds

    @property
    def holds(self) -> bool:
        return self.counterexample is None

    @property
    def vacuous(self) -> bool:
        """Held only because the premise never came up, so nothing was tested."""
        return self.holds and self.triggered == 0

    def explain(self) -> str:
        if self.counterexample is None:
            note = " (vacuously: premise never triggered)" if self.vacuous else ""
            return f"{self.postulate.name}: holds on {self.triggered} cases{note}"
        return f"{self.postulate.name}: FAILS at {format_witness(self.counterexample)}"


@dataclass(frozen=True)
class Postulate:
    """A postulate plus everything a report needs to say about it."""

    number: int
    name: str
    group: str
    source: str
    statement: str          # belief-level, as written in the papers
    check: CheckFn

    def __call__(self, table: OutcomeTable, op: BeliefChangeOperator) -> PostulateResult:
        triggered = 0
        for ok, witness in self.check(table, op):
            triggered += 1
            if not ok:
                return PostulateResult(self, triggered, witness)
        return PostulateResult(self, triggered, None)


POSTULATES: dict[str, Postulate] = {}


def postulate(number: int, name: str, group: str, source: str, statement: str) -> Callable[[CheckFn], CheckFn]:
    """Decorator: register a check function under its metadata.

    The function itself is returned unchanged, so it can still be called
    directly in tests. Registration happens once, at import time.
    """
    def register(check: CheckFn) -> CheckFn:
        if name in POSTULATES or any(p.number == number for p in POSTULATES.values()):
            raise ValueError(f"postulate {number} / {name!r} registered twice")
        POSTULATES[name] = Postulate(number, name, group, source, statement, check)
        return check
    return register


def check(
    op: BeliefChangeOperator,
    sig: Signature,
    postulates: Iterable[Postulate] | None = None,
) -> dict[str, PostulateResult]:
    """Check one operator against the given postulates (default: all of them).

    The outcome table is built once and shared by every postulate.
    """
    table = OutcomeTable.build(op, sig)
    chosen = POSTULATES.values() if postulates is None else postulates
    return {p.name: p(table, op) for p in chosen}


def variants(phi: StateSet, sig: Signature) -> list[Formula]:
    """Five syntactically different formulas with the same meaning φ.

    Used by Extensionality: if an operator answers differently for any of
    them, it depends on syntax, and the meaning-based table is not enough.
    """
    d, c = dnf(phi, sig), cnf(phi, sig)
    return [d, c, Not(Not(d)), Or(d, BOTTOM), And(TOP, c)]


# Group names, so the report can print the postulates in sections
AGM_BASIC = "AGM basic (K*1-K*6)"
AGM_SUPPLEMENTARY = "AGM supplementary (K*7-K*8)"
SELECTIVE = "Selective revision (B&H Prop 3)"
BOOTH_HUNTER = "Booth & Hunter (Props 4, 6, 9)"
SUCCESS_FAMILY = "Success and its weakenings"
MANIPULABILITY = "Manipulability"


# ============================================================ A. AGM basic postulates

@postulate(1, "Closure", AGM_BASIC, "AGM K*1",
           "K ◦ φ = Cn(K ◦ φ)")
def closure(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    # Every set of states is a deductively closed theory, so this only checks
    # that each result really is a set of states over the signature.
    for phi in R.meanings:
        yield R(phi) <= R.universe, (("φ", phi), ("K◦φ", R(phi)))


@postulate(2, "Success", AGM_BASIC, "AGM K*2",
           "φ ∈ K ◦ φ")
def success(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        yield believes(R(phi), phi), (("φ", phi), ("K◦φ", R(phi)))


@postulate(3, "Inclusion", AGM_BASIC, "AGM K*3; B&H Prop 3",
           "K ◦ φ ⊆ Cn(K ∪ {φ})")
def inclusion(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        yield (belief_subset(R(phi), expansion(R.k, phi)),
               (("K", R.k), ("φ", phi), ("K◦φ", R(phi))))


@postulate(4, "Vacuity", AGM_BASIC, "AGM K*4; dissertation §6.3.2",
           "if K ⊬ ¬φ then Cn(K ∪ {φ}) ⊆ K ◦ φ")
def vacuity(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        if consistent_with(R.k, phi):
            yield (belief_subset(expansion(R.k, phi), R(phi)),
                   (("K", R.k), ("φ", phi), ("K◦φ", R(phi))))


@postulate(5, "Consistency", AGM_BASIC, "AGM K*5 (B&H 'iff' form, Prop 3)",
           "K ◦ φ is consistent iff φ is consistent")
def consistency(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        yield is_consistent(R(phi)) == is_consistent(phi), (("φ", phi), ("K◦φ", R(phi)))


@postulate(6, "Extensionality", AGM_BASIC, "AGM K*6; B&H Prop 3",
           "if φ ≡ ψ then K ◦ φ = K ◦ ψ")
def extensionality(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    # The only postulate that calls the operator again: it revises by several
    # spellings of each meaning and compares them with the table (built from DNF).
    for phi in R.meanings:
        for formula in variants(phi, R.signature):
            result = op.revise(formula)
            yield result == R(phi), (("φ", phi), ("spelt as", formula),
                                     ("K◦φ via DNF", R(phi)), ("K◦φ via this", result))


# ============================================================ B. AGM supplementary

@postulate(7, "Superexpansion", AGM_SUPPLEMENTARY, "AGM K*7; dissertation §3.1",
           "K ◦ (φ ∧ ψ) ⊆ Cn(K ◦ φ ∪ {ψ})")
def superexpansion(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        for psi in R.meanings:
            both = conj(phi, psi)
            yield (belief_subset(R(both), expansion(R(phi), psi)),
                   (("φ", phi), ("ψ", psi), ("K◦φ", R(phi)), ("K◦(φ∧ψ)", R(both))))


@postulate(8, "Subexpansion", AGM_SUPPLEMENTARY, "AGM K*8; dissertation §3.1",
           "if K ◦ φ ⊬ ¬ψ then Cn(K ◦ φ ∪ {ψ}) ⊆ K ◦ (φ ∧ ψ)")
def subexpansion(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        for psi in R.meanings:
            if consistent_with(R(phi), psi):
                both = conj(phi, psi)
                yield (belief_subset(expansion(R(phi), psi), R(both)),
                       (("φ", phi), ("ψ", psi), ("K◦φ", R(phi)), ("K◦(φ∧ψ)", R(both))))


# ============================================================ C. Selective revision (B&H Prop 3)

@postulate(9, "Identity", SELECTIVE, "B&H Prop 3",
           "K ◦ ⊤ = K")
def identity(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    yield R(R.universe) == R.k, (("K", R.k), ("K◦⊤", R(R.universe)))


@postulate(10, "Proxy success", SELECTIVE, "Fermé & Hansson; B&H Prop 3; dissertation §6.3.1",
           "there is ψ with K ◦ φ ⊢ ψ, φ ⊢ ψ and K ◦ φ = K ◦ ψ")
def proxy_success(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    # K ◦ φ ⊢ ψ and φ ⊢ ψ  means  ψ ⊇ R(φ) ∪ φ, so only those ψ are candidates.
    for phi in R.meanings:
        found = any(R(psi) == R(phi) for psi in R.supersets(disj(R(phi), phi)))
        yield found, (("φ", phi), ("K◦φ", R(phi)))


@postulate(11, "Consistent expansion", SELECTIVE, "B&H Prop 3",
           "if K ⊄ K ◦ φ then K ∪ (K ◦ φ) ⊢ ⊥")
def consistent_expansion(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        if not belief_subset(R.k, R(phi)):
            yield (not is_consistent(belief_join(R.k, R(phi))),
                   (("K", R.k), ("φ", phi), ("K◦φ", R(phi))))


@postulate(12, "Disjunctive overlap", SELECTIVE, "B&H Prop 3",
           "(K ◦ φ) ∩ (K ◦ ψ) ⊆ K ◦ (φ ∨ ψ)")
def disjunctive_overlap(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        for psi in R.meanings:
            either = disj(phi, psi)
            yield (belief_subset(belief_meet(R(phi), R(psi)), R(either)),
                   (("φ", phi), ("ψ", psi), ("K◦φ", R(phi)), ("K◦ψ", R(psi)), ("K◦(φ∨ψ)", R(either))))


@postulate(13, "Disjunctive inclusion", SELECTIVE, "B&H Prop 3",
           "if K ◦ (φ ∨ ψ) ⊬ ¬φ then K ◦ (φ ∨ ψ) ⊆ K ◦ φ")
def disjunctive_inclusion(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        for either in R.supersets(phi):              # either = φ ∨ ψ, for every ψ
            if consistent_with(R(either), phi):
                yield (belief_subset(R(either), R(phi)),
                       (("φ", phi), ("φ∨ψ", either), ("K◦φ", R(phi)), ("K◦(φ∨ψ)", R(either))))


@postulate(14, "Disjunctive factoring", SELECTIVE, "B&H Prop 3",
           "K ◦ (φ ∨ ψ) is one of K ◦ φ, K ◦ ψ, or (K ◦ φ) ∩ (K ◦ ψ)")
def disjunctive_factoring(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        for psi in R.meanings:
            either = disj(phi, psi)
            allowed = (R(phi), R(psi), belief_meet(R(phi), R(psi)))
            yield (R(either) in allowed,
                   (("φ", phi), ("ψ", psi), ("K◦φ", R(phi)), ("K◦ψ", R(psi)), ("K◦(φ∨ψ)", R(either))))


# ============================================================ D. Booth & Hunter Props 4, 6, 9

@postulate(15, "Disjunctive extension", BOOTH_HUNTER, "B&H Prop 4; dissertation §6.2",
           "if K ◦ (φ ∨ ψ) ⊢ ¬φ then K ◦ (φ ∨ ψ ∨ θ) ⊢ ¬φ")
def disjunctive_extension(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        not_phi = R.neg(phi)
        for mid in R.supersets(phi):                 # mid   = φ ∨ ψ
            if believes(R(mid), not_phi):
                for wide in R.supersets(mid):        # wide  = φ ∨ ψ ∨ θ
                    yield (believes(R(wide), not_phi),
                           (("φ", phi), ("φ∨ψ", mid), ("φ∨ψ∨θ", wide),
                            ("K◦(φ∨ψ)", R(mid)), ("K◦(φ∨ψ∨θ)", R(wide))))


@postulate(16, "Disjunctive equivalence", BOOTH_HUNTER, "B&H Prop 4; dissertation §6.2",
           "if K ◦ φ₁ = K ◦ φ₂ and K ◦ ψ₁ = K ◦ ψ₂ then K ◦ (φ₁ ∨ ψ₁) = K ◦ (φ₂ ∨ ψ₂)")
def disjunctive_equivalence(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    # Four quantifiers, checked in two: the postulate says R(φ ∨ ψ) depends
    # only on the PAIR (R(φ), R(ψ)). Remember the first (φ, ψ) seen for each
    # pair of outcomes; every later (φ, ψ) with the same outcomes must agree.
    first: dict[tuple[StateSet, StateSet], tuple[StateSet, StateSet]] = {}
    for phi in R.meanings:
        for psi in R.meanings:
            key = (R(phi), R(psi))
            phi1, psi1 = first.setdefault(key, (phi, psi))
            yield (R(disj(phi, psi)) == R(disj(phi1, psi1)),
                   (("φ₁", phi1), ("ψ₁", psi1), ("φ₂", phi), ("ψ₂", psi),
                    ("K◦(φ₁∨ψ₁)", R(disj(phi1, psi1))), ("K◦(φ₂∨ψ₂)", R(disj(phi, psi)))))


@postulate(17, "Disjoint outcome basis", BOOTH_HUNTER, "B&H Prop 6",
           "there are λ₁..λₘ with pairwise inconsistent K ◦ λᵢ, and every K ◦ φ "
           "is an intersection of some of them")
def disjoint_outcome_basis(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    # Searching for λ₁..λₘ directly is expensive; there is a constructive test.
    # At state level the basis outcomes must be disjoint sets, and every outcome
    # a union of them. So the basis cell containing a state s can only be the
    # intersection of all outcomes containing s. Compute those cells; the basis
    # exists iff each cell is itself an outcome and the cells never overlap.
    outcomes = set(R.outcomes.values())
    covered = frozenset().union(*outcomes)
    cells = {frozenset.intersection(*(o for o in outcomes if s in o)) for s in covered}
    not_outcome = next((c for c in cells if c not in outcomes), None)
    overlap = next(((a, b) for a in cells for b in cells if a != b and a & b), None)
    witness: Witness = (("candidate cells", " | ".join(sorted(states_str(c) for c in cells))),)
    if not_outcome is not None:
        witness += (("cell that is no outcome", not_outcome),)
    if overlap is not None:
        witness += (("overlapping cells", f"{states_str(overlap[0])} and {states_str(overlap[1])}"),)
    yield not_outcome is None and overlap is None, witness


@postulate(18, "Deficit makeup", BOOTH_HUNTER, "B&H Prop 9",
           "if K ◦ φ ⊆ K ◦ ψ then there is θ ⊢ φ with K ◦ θ = K ◦ ψ")
def deficit_makeup(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        for psi in R.meanings:
            if belief_subset(R(phi), R(psi)):
                found = any(believes(theta, phi) and R(theta) == R(psi) for theta in R.meanings)
                yield found, (("φ", phi), ("ψ", psi), ("K◦φ", R(phi)), ("K◦ψ", R(psi)))


# ============================================================ E. Success and its weakenings

@postulate(19, "Weak success", SUCCESS_FAMILY, "Hansson 1997; B&H §6; dissertation §6.3.1",
           "if K ⊬ ¬φ then K ◦ φ ⊢ φ")
def weak_success(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        if consistent_with(R.k, phi):
            yield believes(R(phi), phi), (("K", R.k), ("φ", phi), ("K◦φ", R(phi)))


@postulate(20, "Very weak success", SUCCESS_FAMILY, "B&H Prop 10; dissertation §6.3.1",
           "if K ⊬ ¬φ and K ◦ ¬φ ⊢ ¬φ then K ◦ φ ⊢ φ")
def very_weak_success(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        not_phi = R.neg(phi)
        if consistent_with(R.k, phi) and believes(R(not_phi), not_phi):
            yield (believes(R(phi), phi),
                   (("K", R.k), ("φ", phi), ("K◦¬φ", R(not_phi)), ("K◦φ", R(phi))))


@postulate(21, "Negation invariance", SUCCESS_FAMILY, "B&H §6 (equivalent form of Very weak success)",
           "if K ⊬ ¬φ and K ⊬ φ then [K ◦ φ ⊢ φ iff K ◦ ¬φ ⊢ ¬φ]")
def negation_invariance(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        not_phi = R.neg(phi)
        if consistent_with(R.k, phi) and consistent_with(R.k, not_phi):
            yield (believes(R(phi), phi) == believes(R(not_phi), not_phi),
                   (("K", R.k), ("φ", phi), ("K◦φ", R(phi)), ("K◦¬φ", R(not_phi))))


@postulate(22, "Feeble success", SUCCESS_FAMILY, "B&H Prop 11; dissertation §6.3.1",
           "if K ⊬ ¬φ and K ◦ ¬φ ⊢ ¬φ then there is a consistent ψ ⊢ φ with K ◦ ψ ⊢ φ")
def feeble_success(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        not_phi = R.neg(phi)
        if consistent_with(R.k, phi) and believes(R(not_phi), not_phi):
            found = any(is_consistent(psi) and believes(psi, phi) and believes(R(psi), phi)
                        for psi in R.meanings)
            yield found, (("K", R.k), ("φ", phi), ("K◦¬φ", R(not_phi)), ("K◦φ", R(phi)))


# ============================================================ F. Manipulability

@postulate(23, "Non-manipulability", MANIPULABILITY, "B&H Prop 14; dissertation §6.5.3",
           "if K ◦ φ ⊬ φ and ψ is consistent then K ◦ ψ ⊬ φ")
def non_manipulability(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        if not believes(R(phi), phi):
            for psi in R.meanings:
                if is_consistent(psi):
                    yield (not believes(R(psi), phi),
                           (("φ", phi), ("K◦φ", R(phi)), ("ψ", psi), ("K◦ψ", R(psi))))


@postulate(24, "Weak non-manipulability", MANIPULABILITY, "B&H Prop 15",
           "if K ◦ φ ⊬ φ then K ◦ (φ ∨ ψ) ⊬ φ")
def weak_non_manipulability(R: OutcomeTable, op: BeliefChangeOperator) -> Cases:
    for phi in R.meanings:
        if not believes(R(phi), phi):
            for either in R.supersets(phi):          # either = φ ∨ ψ, for every ψ
                yield (not believes(R(either), phi),
                       (("φ", phi), ("K◦φ", R(phi)), ("φ∨ψ", either), ("K◦(φ∨ψ)", R(either))))
