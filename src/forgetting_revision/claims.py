"""Instance claims and negative controls: the specific results the papers state.

The postulates are FAMILY claims ("every TSR operator satisfies X"). The
claims here are about particular settings or examples, and so cannot be
written as a postulate:

  i-claims  INSTANCE claims: results for one trust setting or one worked
            example, e.g. "with no trust, K never changes" (Postulate 1).
  c-claims  NEGATIVE CONTROLS: operators built to break a postulate. Each must
            be REPORTED as failing it. If the checker could not do that, its
            "holds" verdicts would mean nothing.

Each claim is a function returning a ClaimResult: whether it holds, plus a
one-line detail for the report. They are registered with a decorator, like
the postulates, so `check-postulates` prints them and the README can list them.
All claims use two variables (p, q) unless they say otherwise.
"""

from collections.abc import Callable
from dataclasses import dataclass
from functools import cache

from .agm_revision import AGMRevision
from .families import format_partition, orderings, partitions, untrusted_sets
from .postulates import POSTULATES, OutcomeTable, check, variants
from .selective_revision import (
    ForgetTransform,
    IdentityTransform,
    SelectiveRevision,
    TableTransform,
    TrustExpansion,
)
from .semantics import Signature, State, dnf, meanings, models, states_str
from .syntax import Formula, Not, Var
from .transform_properties import (
    PROPERTIES,
    check_transform,
    induced_partition,
    is_kuratowski,
)
from .trust import StatePartition

SIG = Signature.of("p q")
SIG3 = Signature.of("p q r")
ALL = frozenset(SIG.states())
TT, TF, FT, FF = (True, True), (True, False), (False, True), (False, False)

INSTANCE = "instance"
CONTROL = "control"


@dataclass(frozen=True)
class ClaimResult:
    holds: bool
    detail: str


@dataclass(frozen=True)
class Claim:
    code: str
    title: str
    source: str
    kind: str                                   # INSTANCE or CONTROL
    check: Callable[[], ClaimResult]

    def __call__(self) -> ClaimResult:
        return self.check()


CLAIMS: dict[str, Claim] = {}


def claim(code: str, title: str, source: str, kind: str) -> Callable[[Callable[[], ClaimResult]], Callable[[], ClaimResult]]:
    def register(fn: Callable[[], ClaimResult]) -> Callable[[], ClaimResult]:
        if code in CLAIMS:
            raise ValueError(f"claim {code} registered twice")
        CLAIMS[code] = Claim(code, title, source, kind, fn)
        return fn
    return register


@cache
def _evaluate(c: Claim) -> ClaimResult:
    return c.check()


def run_claims() -> dict[str, ClaimResult]:
    """Run every registered claim.

    Claims are deterministic, so each result is cached for the life of the
    process: the report and the tests can ask repeatedly at no extra cost.
    The cache key is the Claim object itself (frozen dataclasses are hashable).
    """
    return {code: _evaluate(c) for code, c in CLAIMS.items()}


def _vfr(ordering: tuple[frozenset[State], ...], untrusted: frozenset[str] | set[str] | str) -> SelectiveRevision:
    return SelectiveRevision.vfr(AGMRevision(ordering), SIG, untrusted)


# ============================================================ instance claims

@claim("i1", "No trust ⇒ K ◦ α = K, for every consistent α",
       "dissertation Postulate 1 (§6.3); B&H Prop 1", INSTANCE)
def no_trust_changes_nothing() -> ClaimResult:
    everything = frozenset(SIG.names)
    consistent = [m for m in meanings(SIG) if m]
    for ordering in orderings(SIG):
        for op in (_vfr(ordering, everything),
                   SelectiveRevision.tsr(AGMRevision(ordering), SIG, StatePartition.trivial(SIG))):
            if any(op.revise(dnf(m, SIG)) != op.belief_states() for m in consistent):
                return ClaimResult(False, "some consistent report changed K")
    # The stated form ("for any α") fails at α = ⊥: Forget(⊥) = ⊥ and K ◦ ⊥ = ∅.
    at_bottom = _vfr(next(orderings(SIG)), everything).revise(dnf(frozenset(), SIG))
    return ClaimResult(True, f"all 75 orderings, VFR and TSR; at α = ⊥ the result is "
                             f"{states_str(at_bottom) if at_bottom else '∅'} (inconsistent), "
                             f"so the postulate needs 'consistent α'")


@claim("i2", "Full trust ⇒ ◦ = ∗ (plain AGM)",
       "dissertation Postulate 2 (§6.3); B&H Prop 2", INSTANCE)
def full_trust_is_agm() -> ClaimResult:
    for ordering in orderings(SIG):
        agm = AGMRevision(ordering)
        vfr = _vfr(ordering, set())
        tsr = SelectiveRevision.tsr(agm, SIG, StatePartition.unit(SIG))
        for m in meanings(SIG):
            if not (vfr.revise(dnf(m, SIG)) == tsr.revise(dnf(m, SIG)) == agm.revise(m)):
                return ClaimResult(False, f"differs from AGM at φ = {states_str(m)}")
    return ClaimResult(True, "all 75 orderings × 16 meanings, VFR (U = ∅) and TSR (unit partition)")


@claim("i3", "Non-manipulability holds at both extremes of trust",
       "dissertation §6.5.3; B&H §7", INSTANCE)
def extremes_are_not_manipulable() -> ClaimResult:
    non_manip = POSTULATES["Non-manipulability"]
    settings = {"no trust": frozenset(SIG.names), "full trust": frozenset()}
    for label, untrusted in settings.items():
        for ordering in orderings(SIG):
            if not check(_vfr(ordering, untrusted), SIG, [non_manip])["Non-manipulability"].holds:
                return ClaimResult(False, f"manipulable under {label}")
    return ClaimResult(True, "all 75 orderings at U = ∅ and U = {p, q}; it fails in between")


@claim("i4", "VFR ⊆ TSR: Forget(·, U) is the trust expansion of the forgetting partition",
       "dissertation §6.1; B&H Prop 8 (Yao)", INSTANCE)
def vfr_is_tsr() -> ClaimResult:
    checked = 0
    for sig in (SIG, SIG3):
        for untrusted in untrusted_sets(sig):
            forget = ForgetTransform(sig, untrusted)
            expand = TrustExpansion(sig, StatePartition.from_untrusted(sig, untrusted))
            for m in meanings(sig):
                for formula in variants(m, sig):
                    checked += 1
                    if forget(formula) != expand(formula):
                        return ClaimResult(False, f"differ on {formula}, U = {sorted(untrusted)}")
            if induced_partition(forget, sig) != StatePartition.from_untrusted(sig, untrusted):
                return ClaimResult(False, f"wrong induced partition for U = {sorted(untrusted)}")
    return ClaimResult(True, f"{checked:,} formulas over 2 and 3 variables, every U; "
                             f"induced partition = forgetting partition")


@claim("i5", "VFR is strictly weaker: only 4 of the 15 partitions come from forgetting",
       "dissertation §6.5.4", INSTANCE)
def vfr_strictly_weaker() -> ClaimResult:
    reachable = {StatePartition.from_untrusted(SIG, u) for u in untrusted_sets(SIG)}
    alarm = StatePartition.from_cells([[TT, FF], [TF, FT]])
    total = sum(1 for _ in partitions(SIG))
    ok = len(reachable) == 4 and total == 15 and alarm not in reachable
    return ClaimResult(ok, f"{len(reachable)} of {total}; unreachable includes the alarm "
                           f"partition {format_partition(alarm)}")


@claim("i6", "Alarm example: TSR can weaken 'alarm 1 rang' to 'exactly one rang'; no VFR can",
       "dissertation §6.5.4 (corrected report, see detail)", INSTANCE)
def alarm_example() -> ClaimResult:
    alarm = TrustExpansion(SIG, StatePartition.from_cells([[TT, FF], [TF, FT]]))
    p, q = Var("p"), Var("q")
    named = p & ~q                                         # the officer names alarm 1
    exactly_one = frozenset({TF, FT})
    vfr_results = {ForgetTransform(SIG, u)(named) for u in untrusted_sets(SIG)}
    as_written = alarm(p | q)                               # the dissertation's α = p ∨ q
    ok = alarm(named) == exactly_one and exactly_one not in vfr_results and as_written == ALL
    return ClaimResult(ok, "f(p ∧ ¬q) = p ⊕ q under TSR, never under VFR. As written in §6.5.4 "
                           f"(α = p ∨ q) TSR gives {states_str(as_written)} = ⊤, i.e. it ignores the "
                           "report, because TT shares a cell with FF")


@claim("i7", "Very weak success fails for VFR: K = p ⊕ q, U = {p}, α = ¬(p ∧ ¬q)",
       "dissertation §6.3.1 (with K ⊬ ¬α, not K ⊢ ¬α)", INSTANCE)
def xor_counterexample() -> ClaimResult:
    xor = frozenset({TF, FT})
    alpha = ALL - {TF}
    faithful = [o for o in orderings(SIG) if o[0] == xor]
    for ordering in faithful:
        R = OutcomeTable.build(_vfr(ordering, "p"), SIG)
        premise = bool(R.k & alpha) and R(R.neg(alpha)) <= R.neg(alpha)
        if not premise or R(alpha) <= alpha:
            return ClaimResult(False, "not a counterexample under some ordering")
    return ClaimResult(True, f"a counterexample under all {len(faithful)} faithful orderings for K = p ⊕ q")


@claim("i8", "Doctor-Necklace: forgetting diam weakens the report to 'sick' (Examples 1-2)",
       "dissertation §5; B&H Examples 1-3", INSTANCE)
def doctor_necklace() -> ClaimResult:
    sick, diam, repl = Var("sick"), Var("diam"), Var("repl")
    s2, s3 = Signature.of("sick diam"), Signature.of("sick diam repl")
    ex1 = ForgetTransform(s2, "diam")(sick & ~diam) == models(sick, s2)
    ex2 = ForgetTransform(s3, {"diam", "repl"})(sick & (~diam >> repl)) == models(sick, s3)
    # B&H Example 3: ordering {diam} < {sick, diam}, ∅ < {sick}
    k3 = AGMRevision.from_tiers([[FT], [TT, FF], [TF]])
    op = SelectiveRevision.vfr(k3, s2, "diam")
    ex3 = (op.revise(sick) == {TT}, op.revise(~diam) == {FT}, op.revise(sick & ~diam) == {TT})
    ok = ex1 and ex2 and all(ex3)
    return ClaimResult(ok, "Ex 1: Forget(sick ∧ ¬diam) ≡ sick; Ex 2: ≡ sick over 3 variables; "
                           "B&H Ex 3 results (1)-(3) reproduced")


# ============================================================ negative controls

def _ex5() -> TableTransform:
    sig1 = Signature.of("p")
    t, f = (True,), (False,)
    return TableTransform(sig1, {frozenset(): frozenset(), frozenset({t}): frozenset({t, f}),
                                 frozenset({f}): frozenset({f}), frozenset({t, f}): frozenset({t, f})})


@claim("c1", "B&H Example 5: Kuratowski but not Pawlak ⇒ fails Disjoint outcome basis and Feeble success",
       "B&H Props 7, 12", CONTROL)
def example_5() -> ClaimResult:
    f = _ex5()
    props = check_transform(f, f.signature)
    op = SelectiveRevision(AGMRevision.from_tiers([f.signature.states()]), f)
    results = check(op, f.signature)
    failed_f = sorted(n for n, r in props.items() if not r.holds)
    ok = (is_kuratowski(props) and failed_f == ["Conjunctive weakening", "Pawlak", "Trust symmetry"]
          and not results["Disjoint outcome basis"].holds and not results["Feeble success"].holds)
    return ClaimResult(ok, f"f fails {', '.join(failed_f)}; ◦ fails Disjoint outcome basis and Feeble success")


@claim("c2", "A non-monotone f breaks Weak non-manipulability",
       "B&H §7 (after Prop 15)", CONTROL)
def non_monotone() -> ClaimResult:
    p = frozenset({TT, TF})
    f = TableTransform.from_function(SIG, lambda a: ALL if a == p else a)
    op = SelectiveRevision(AGMRevision.from_tiers([[FF], [TF], [FT, TT]]), f)
    R = OutcomeTable.build(op, SIG)
    monotone = check_transform(f, SIG, [PROPERTIES["Monotonicity"]])["Monotonicity"].holds
    fails = not check(op, SIG, [POSTULATES["Weak non-manipulability"]])["Weak non-manipulability"].holds
    ok = not monotone and fails and R(p) == {FF} and R(frozenset({TT, TF, FT})) == {TF}
    return ClaimResult(ok, f"K ◦ p = {states_str(R(p))} ⊬ p, but K ◦ (p ∨ q) = "
                           f"{states_str(R(frozenset({TT, TF, FT})))} ⊢ p")


@claim("c3", "Dead battery: TSR fails Very weak success but keeps Feeble success",
       "B&H Example 4, Props 10-11", CONTROL)
def dead_battery() -> ClaimResult:
    op = SelectiveRevision.tsr(AGMRevision.from_tiers([[TT, FT], [TF, FF]]), SIG,
                               StatePartition.from_cells([[TT], [TF, FT], [FF]]))
    R = OutcomeTable.build(op, SIG)
    p = frozenset({TT, TF})
    paper = R(R.neg(p)) == {FT} and R(p) == {TT, FT} and R(frozenset({TT})) == {TT}
    results = check(op, SIG)
    ok = paper and not results["Very weak success"].holds and results["Feeble success"].holds
    return ClaimResult(ok, "K ◦ ¬p = Cn(¬p ∧ q), K ◦ p = Cn(q), K ◦ (p ∧ q) = Cn(p ∧ q), as in the paper")


class _SyntaxSensitive(IdentityTransform):
    """Deliberately broken: treats ¬¬α differently from α."""

    def __call__(self, alpha: Formula) -> frozenset[State]:
        if isinstance(alpha, Not) and isinstance(alpha.operand, Not):
            return frozenset(self.signature.states())
        return models(alpha, self.signature)


@claim("c4", "A syntax-dependent operator is caught by Extensionality",
       "AGM K*6; dissertation §6.2", CONTROL)
def syntax_dependence_detected() -> ClaimResult:
    op = SelectiveRevision(AGMRevision.from_tiers([[TT], [TF, FT, FF]]), _SyntaxSensitive(SIG))
    postulate = check(op, SIG, [POSTULATES["Extensionality"]])["Extensionality"]
    prop = check_transform(_SyntaxSensitive(SIG), SIG, [PROPERTIES["Extensionality"]])["Extensionality"]
    return ClaimResult(not postulate.holds and not prop.holds,
                       "both the postulate (#6) and the f-property (f4) report it")

