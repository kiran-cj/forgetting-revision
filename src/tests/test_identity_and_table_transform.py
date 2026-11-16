"""Tests for IdentityTransform (plain AGM) and TableTransform (any f at all)."""

import pytest

from forgetting_revision import (
    AGMRevision,
    IdentityTransform,
    SelectiveRevision,
    Signature,
    StatePartition,
    TableTransform,
    TrustExpansion,
    cnf,
    dnf,
    meanings,
    orderings,
)

SIG = Signature.of("p q")
ALL = frozenset(SIG.states())
TT, TF, FT, FF = (True, True), (True, False), (False, True), (False, False)

SIG1 = Signature.of("p")
T, F = (True,), (False,)


# ------------------------------------------------------------- IdentityTransform

def test_identity_returns_the_models():
    f = IdentityTransform(SIG)
    for m in meanings(SIG):
        assert f(dnf(m, SIG)) == f(cnf(m, SIG)) == m


def test_agm_constructor_is_plain_agm_for_every_ordering():
    """SelectiveRevision.agm must behave exactly like AGMRevision itself."""
    for ordering in orderings(SIG):
        agm = AGMRevision(ordering)
        op = SelectiveRevision.agm(agm, SIG)
        assert op.belief_states() == agm.belief_states()
        for m in meanings(SIG):
            assert op.revise(dnf(m, SIG)) == agm.revise(m)


# ------------------------------------------------------------- TableTransform

def ex5_table():
    """Booth & Hunter Example 5, over the single variable p:
    f(⊥) = ⊥, f(p) = ⊤, f(¬p) = ¬p, f(⊤) = ⊤.
    A Kuratowski function that does NOT come from any partition."""
    return {frozenset(): frozenset(), frozenset({T}): frozenset({T, F}),
            frozenset({F}): frozenset({F}), frozenset({T, F}): frozenset({T, F})}


def test_table_transform_looks_up_the_meaning():
    f = TableTransform(SIG1, ex5_table())
    p = dnf({T}, SIG1)
    not_p = dnf({F}, SIG1)
    assert f(p) == {T, F}            # p is weakened to ⊤
    assert f(not_p) == {F}           # ¬p is kept


def test_table_transform_is_extensional_by_construction():
    """It looks up Mod(α), so any two spellings of α give the same answer."""
    f = TableTransform.from_function(SIG, lambda a: ALL if a == {TT, TF} else a)
    for m in meanings(SIG):
        assert f(dnf(m, SIG)) == f(cnf(m, SIG))


def test_from_function_matches_a_real_transform():
    """Tabulating TrustExpansion gives back the same transformation."""
    partition = StatePartition.from_cells([[TT, FF], [TF, FT]])
    real = TrustExpansion(SIG, partition)
    table = TableTransform.from_function(SIG, partition.expand)
    for m in meanings(SIG):
        assert table(dnf(m, SIG)) == real(dnf(m, SIG))


def test_keys_and_values_are_normalised_to_frozensets():
    f = TableTransform(SIG1, {k: set(v) for k, v in ex5_table().items()})
    assert all(isinstance(v, frozenset) for v in f.table.values())


def test_table_is_read_only():
    f = TableTransform(SIG1, ex5_table())
    with pytest.raises(TypeError):
        f.table[frozenset()] = frozenset({T})


def test_incomplete_table_rejected():
    table = ex5_table()
    del table[frozenset({F})]
    with pytest.raises(ValueError, match="needs all 4"):
        TableTransform(SIG1, table)


def test_value_outside_signature_rejected():
    table = ex5_table()
    table[frozenset({T})] = frozenset({(True, True)})      # a two-variable state
    with pytest.raises(ValueError, match="outside the signature"):
        TableTransform(SIG1, table)


def test_table_plugs_into_selective_revision():
    """B&H Example 5 with K = Cn(⊤): K ◦ p = Cn(⊤), K ◦ ¬p = Cn(¬p)."""
    op = SelectiveRevision(AGMRevision.from_tiers([[T, F]]), TableTransform(SIG1, ex5_table()))
    assert op.revise(dnf({T}, SIG1)) == {T, F}
    assert op.revise(dnf({F}, SIG1)) == {F}
