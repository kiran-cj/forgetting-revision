"""Tests for the 24 operator postulates.

Three kinds of test:

  1. The VERDICT MATRIX: every postulate on every operator of every family
     (75 AGM, 1,125 TSR, 300 VFR over two variables), against the verdicts
     claimed by AGM, Booth & Hunter and the dissertation.
  2. KNOWN COUNTEREXAMPLES from the papers, checked one by one, so a failure
     is reported for the right reason and not just "somewhere".
  3. NEGATIVE CONTROLS: operators built to break a postulate. A checker that
     never says "fails" proves nothing, so these show it can.
"""

from functools import cache

import pytest

from forgetting_revision import (
    FAMILIES,
    AGMRevision,
    IdentityTransform,
    Not,
    SelectiveRevision,
    Signature,
    StatePartition,
    TableTransform,
    agm_family,
    dnf,
    models,
    tsr_family,
    vfr_family,
)
from forgetting_revision.postulates import (
    POSTULATES,
    OutcomeTable,
    PostulateResult,
    check,
    format_witness,
    postulate,
)

SIG = Signature.of("p q")
ALL = frozenset(SIG.states())
TT, TF, FT, FF = (True, True), (True, False), (False, True), (False, False)

P = frozenset({TT, TF})                 # p
XOR = frozenset({TF, FT})               # p ⊕ q


# ============================================================ 1. registry

def test_all_24_postulates_registered_in_order():
    assert [p.number for p in POSTULATES.values()] == list(range(1, 25))


def test_every_postulate_has_its_metadata():
    for p in POSTULATES.values():
        assert p.name and p.group and p.source and p.statement


def test_registering_a_duplicate_is_an_error():
    with pytest.raises(ValueError, match="registered twice"):
        @postulate(2, "Success again", "test", "test", "test")
        def dup(R, op):
            yield True, ()


# ============================================================ 2. verdict matrix

# What the literature claims (True = every operator in the family satisfies it).
# AGM satisfies everything; TSR and VFR fail exactly these eight.
FAILS_FOR_TSR_AND_VFR = {
    "Success", "Vacuity", "Superexpansion", "Subexpansion",
    "Weak success", "Very weak success", "Negation invariance", "Non-manipulability",
}
EXPECTED = {
    (name, family): family == "AGM" or name not in FAILS_FOR_TSR_AND_VFR
    for name in POSTULATES
    for family in FAMILIES
}


@cache
def family_results(family: str) -> list[dict[str, PostulateResult]]:
    """Every operator of the family checked once, then shared by all 72 tests."""
    return [check(member.operator, SIG) for member in FAMILIES[family](SIG)]


@pytest.mark.parametrize(("name", "family"), sorted(EXPECTED), ids=lambda x: str(x))
def test_verdict_matrix(name, family):
    results = [r[name] for r in family_results(family)]
    holds_everywhere = all(r.holds for r in results)
    if EXPECTED[name, family]:
        failure = next((r for r in results if not r.holds), None)
        assert holds_everywhere, failure.explain() if failure else ""
    else:
        assert not holds_everywhere, f"{name} was expected to fail somewhere in {family}"


def test_agm_passes_non_manipulability_only_vacuously():
    """Under Success, 'K ◦ φ ⊬ φ' never happens, so nothing is ever tested."""
    assert all(r["Non-manipulability"].vacuous for r in family_results("AGM"))
    assert any(r["Non-manipulability"].triggered for r in family_results("TSR"))


def test_premises_are_actually_triggered():
    """Guards against a pass that only means 'premise never came up'."""
    for name in ("Vacuity", "Subexpansion", "Disjunctive inclusion", "Deficit makeup",
                 "Very weak success", "Feeble success", "Weak non-manipulability"):
        assert any(r[name].triggered for r in family_results("VFR")), name


def test_failing_success_forces_failing_superexpansion():
    """With Consistency, Superexpansion at ψ = ¬φ forces Success (catalogue §7.4).
    So every TSR/VFR operator that fails Success must fail Superexpansion too."""
    for family in ("TSR", "VFR"):
        for r in family_results(family):
            if not r["Success"].holds:
                assert not r["Superexpansion"].holds


def test_very_weak_success_and_negation_invariance_always_agree():
    """B&H call them equivalent; check it operator by operator."""
    for family in FAMILIES:
        for r in family_results(family):
            assert r["Very weak success"].holds == r["Negation invariance"].holds


# ============================================================ 3. counterexamples from the papers

def tiers(*levels):
    return AGMRevision.from_tiers(levels)


def test_vfr_subexpansion_counterexample():
    """Catalogue §7.4: untrust p, ordering TT < TF < FT < FF (so K = p ∧ q).
    Forgetting p from p ⊕ q leaves ⊤, so K ◦ (p ⊕ q) = K, consistent with p.
    But (p ⊕ q) ∧ p = p ∧ ¬q; forgetting p leaves ¬q, so K ◦ (p ∧ ¬q) = {TF}."""
    op = SelectiveRevision.vfr(tiers([TT], [TF], [FT], [FF]), SIG, "p")
    R = OutcomeTable.build(op, SIG)
    assert R(XOR) == {TT}
    assert R(XOR & P) == {TF}
    result = check(op, SIG, [POSTULATES["Subexpansion"]])["Subexpansion"]
    assert not result.holds


def test_booth_hunter_example_4_dead_battery():
    """K = Cn(q); Π = {TT} | {TF, FT} | {FF}. K ◦ ¬p ⊢ ¬p but K ◦ p ⊬ p,
    so Very weak success fails, while Feeble success holds (via p ∧ q)."""
    op = SelectiveRevision.tsr(tiers([TT, FT], [TF, FF]), SIG,
                               StatePartition.from_cells([[TT], [TF, FT], [FF]]))
    R = OutcomeTable.build(op, SIG)
    assert R(R.neg(P)) == {FT}            # paper: Cn(¬p ∧ q)
    assert R(P) == {TT, FT}               # paper: Cn(q)
    assert R(frozenset({TT})) == {TT}     # paper: Cn(p ∧ q)

    results = check(op, SIG)
    assert not results["Very weak success"].holds
    assert not results["Negation invariance"].holds
    assert results["Feeble success"].holds


@pytest.mark.parametrize("ordering", [
    ([TF, FT], [TT, FF]),
    ([TF, FT], [TT], [FF]),
    ([TF, FT], [FF], [TT]),
], ids=["2 tiers", "TT below FF", "FF below TT"])
def test_dissertation_xor_counterexample(ordering):
    """§6.3.1: K = XOR, untrust p, α = ¬(p ∧ ¬q). Fails Very weak success
    under every faithful ordering with K = XOR."""
    op = SelectiveRevision.vfr(tiers(*ordering), SIG, "p")
    alpha = ALL - {TF}
    R = OutcomeTable.build(op, SIG)
    assert R.k & alpha                          # K ⊬ ¬α (the dissertation's typo says ⊢)
    assert R(R.neg(alpha)) <= R.neg(alpha)      # K ◦ ¬α ⊢ ¬α
    assert not R(alpha) <= alpha                # K ◦ α ⊬ α
    assert not check(op, SIG)["Very weak success"].holds


def test_fully_distrusted_source_fails_weak_success():
    """B&H §6: with the trivial partition nothing is ever accepted.

    K needs at least two states here. If K = {TT}, then 'K consistent with φ'
    means TT satisfies φ, so K ⊢ φ already and K ◦ φ = K ⊢ φ: Weak success
    would hold even though the source is ignored. With K = Cn(p) and φ = p ∧ q,
    K ⊬ ¬φ, but K ◦ φ = K ⊬ φ.
    """
    op = SelectiveRevision.tsr(tiers([TT, TF], [FT, FF]), SIG, StatePartition.trivial(SIG))
    assert not check(op, SIG)["Weak success"].holds

    single = SelectiveRevision.tsr(tiers([TT], [TF, FT, FF]), SIG, StatePartition.trivial(SIG))
    assert check(single, SIG)["Weak success"].holds


# ============================================================ 4. negative controls

SIG1 = Signature.of("p")
T, F = (True,), (False,)


def ex5_operator():
    """B&H Example 5 / Props 7 and 12: f(p) = ⊤, f(¬p) = ¬p, K = Cn(⊤).
    Kuratowski, but not from any partition."""
    f = TableTransform(SIG1, {frozenset(): frozenset(), frozenset({T}): frozenset({T, F}),
                              frozenset({F}): frozenset({F}), frozenset({T, F}): frozenset({T, F})})
    return SelectiveRevision(AGMRevision.from_tiers([[T, F]]), f)


def test_example_5_fails_disjoint_outcome_basis_and_feeble_success():
    results = check(ex5_operator(), SIG1)
    assert not results["Disjoint outcome basis"].holds        # B&H Prop 7
    assert not results["Feeble success"].holds                 # B&H Prop 12
    assert results["Weak non-manipulability"].holds            # still Kuratowski (Prop 15)


def test_non_kuratowski_function_fails_weak_non_manipulability():
    """B&H §7: ordering FF < TF < {FT, TT}, f(p) = ⊤ and f = identity otherwise.
    K ◦ p = {FF} ⊬ p, yet K ◦ (p ∨ q) = {TF} ⊢ p."""
    f = TableTransform.from_function(SIG, lambda a: ALL if a == P else a)
    op = SelectiveRevision(tiers([FF], [TF], [FT, TT]), f)
    R = OutcomeTable.build(op, SIG)
    assert R(P) == {FF} and R(frozenset({TT, TF, FT})) == {TF}
    assert not check(op, SIG)["Weak non-manipulability"].holds


class SyntaxSensitive(IdentityTransform):
    """A deliberately broken f: treats ¬¬α differently from α."""
    def __call__(self, alpha):
        if isinstance(alpha, Not) and isinstance(alpha.operand, Not):
            return frozenset(SIG.states())
        return models(alpha, self.signature)


def test_syntax_dependent_operator_fails_extensionality():
    op = SelectiveRevision(tiers([TT], [TF, FT, FF]), SyntaxSensitive(SIG))
    result = check(op, SIG)["Extensionality"]
    assert not result.holds
    assert "spelt as" in format_witness(result.counterexample)


# ============================================================ 5. reporting

def test_explain_and_witness_formatting():
    op = SelectiveRevision.vfr(tiers([TT], [TF], [FT], [FF]), SIG, "p")
    results = check(op, SIG)
    assert results["Success"].explain().startswith("Success: FAILS at φ = ")
    assert "holds on" in results["Inclusion"].explain()
    assert format_witness((("φ", P), ("note", "x"))) == "φ = {TT, TF}, note = x"


def test_check_can_run_a_subset():
    results = check(next(agm_family(SIG)).operator, SIG,
                    [POSTULATES["Success"], POSTULATES["Identity"]])
    assert set(results) == {"Success", "Identity"}


def test_table_built_from_real_revise_matches_dnf_input():
    op = next(vfr_family(SIG)).operator
    R = OutcomeTable.build(op, SIG)
    assert R(P) == op.revise(dnf(P, SIG))


def test_tsr_family_contains_plain_agm_behaviour():
    """TSR with the unit partition IS AGM, so it must pass Success."""
    unit = StatePartition.unit(SIG)
    member = next(m for m in tsr_family(SIG) if m.partition == unit)
    assert check(member.operator, SIG)["Success"].holds
