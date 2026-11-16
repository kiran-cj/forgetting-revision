"""Tests for OutcomeTable and the belief-to-state translation helpers."""

import pytest

from forgetting_revision import (
    AGMRevision,
    OutcomeTable,
    SelectiveRevision,
    Signature,
    agm_family,
    cnf,
    meanings,
    vfr_family,
)
from forgetting_revision.postulates import (
    belief_meet,
    belief_subset,
    believes,
    conj,
    consistent_with,
    disj,
    expansion,
    is_consistent,
)

SIG = Signature.of("p q")
ALL = frozenset(SIG.states())
TT, TF, FT, FF = (True, True), (True, False), (False, True), (False, False)

# Meanings of some formulas, by hand
P = frozenset({TT, TF})             # p
Q = frozenset({TT, FT})             # q
P_AND_Q = frozenset({TT})           # p ∧ q
P_OR_Q = frozenset({TT, TF, FT})    # p ∨ q


# ------------------------------------------------------------- OutcomeTable

def k3_vfr():
    """Doctor-Necklace ordering (B&H Ex 3), forgetting diam (= q)."""
    agm = AGMRevision.from_tiers([[FT], [TT, FF], [TF]])
    return SelectiveRevision.vfr(agm, SIG, "q")


def test_table_has_one_entry_per_meaning():
    R = OutcomeTable.build(k3_vfr(), SIG)
    assert len(R.outcomes) == 16
    assert R.meanings == meanings(SIG)
    assert R.k == {FT}


def test_table_entries_are_the_real_revision_results():
    """R(φ) must be what revise() returns, here checked on a different spelling (CNF)."""
    op = k3_vfr()
    R = OutcomeTable.build(op, SIG)
    for m in meanings(SIG):
        assert R(m) == op.revise(cnf(m, SIG))


def test_table_matches_paper_example():
    """B&H Example 3: the doctor saying sick gives sick ∧ diam."""
    R = OutcomeTable.build(k3_vfr(), SIG)
    assert R(P) == {TT}


def test_revising_by_top_gives_k_for_every_agm_operator():
    for member in agm_family(SIG):
        R = OutcomeTable.build(member.operator, SIG)
        assert R(R.universe) == R.k


def test_table_is_read_only():
    R = OutcomeTable.build(k3_vfr(), SIG)
    with pytest.raises(TypeError):
        R.outcomes[P] = frozenset()


def test_neg_and_supersets():
    R = OutcomeTable.build(next(vfr_family(SIG)).operator, SIG)
    assert R.neg(P) == {FT, FF}
    assert R.neg(frozenset()) == ALL
    assert set(R.supersets(P_OR_Q)) == {P_OR_Q, ALL}
    for m in meanings(SIG):                    # a set of size j has 2^(4-j) supersets
        assert sum(1 for _ in R.supersets(m)) == 2 ** (4 - len(m))


# ------------------------------------------------------------- translation helpers
# Each test states the BELIEF-level fact in its name and checks the helper agrees.

def test_believes():
    assert believes(P_AND_Q, P)             # Cn(p ∧ q) ⊢ p
    assert not believes(P, P_AND_Q)         # Cn(p) ⊬ p ∧ q
    assert believes(frozenset(), P)         # the inconsistent belief set entails everything


def test_consistent_with():
    assert consistent_with(P, Q)                    # Cn(p) ⊬ ¬q
    assert not consistent_with(P, frozenset({FT}))  # Cn(p) ⊢ ¬(¬p ∧ q)


def test_is_consistent():
    assert is_consistent(P)
    assert not is_consistent(frozenset())


def test_belief_subset_is_reversed():
    """Cn(p) ⊆ Cn(p ∧ q): the stronger belief set has FEWER states."""
    assert belief_subset(P, P_AND_Q)
    assert not belief_subset(P_AND_Q, P)


def test_belief_meet_is_reversed():
    """Cn(p) ∩ Cn(q) = Cn(p ∨ q): shared beliefs allow MORE states."""
    assert belief_meet(P, Q) == P_OR_Q


def test_expansion():
    """Cn(Cn(p) ∪ {q}) = Cn(p ∧ q)."""
    assert expansion(P, Q) == P_AND_Q


def test_connectives():
    assert disj(P, Q) == P_OR_Q
    assert conj(P, Q) == P_AND_Q
