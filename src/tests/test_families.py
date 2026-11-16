"""Tests for the family generators: are we really checking EVERY operator?

If a generator silently missed some orderings or partitions, every
postulate verdict would still say "holds", but over fewer operators than
claimed. So these tests pin the counts to known sequences:

    orderings   Fubini numbers   3, 75, 545,835     (n = 1, 2, 3)
    partitions  Bell numbers     2, 15, 4,140
    untrusted   powers of two    2, 4, 8
"""

import pytest

from forgetting_revision import (
    FAMILIES,
    AGMRevision,
    IdentityTransform,
    Signature,
    StatePartition,
    agm_family,
    dnf,
    meanings,
    orderings,
    partitions,
    tsr_family,
    untrusted_sets,
    vfr_family,
)

SIG1, SIG2, SIG3 = Signature.of("p"), Signature.of("p q"), Signature.of("p q r")
TT, TF, FT, FF = (True, True), (True, False), (False, True), (False, False)


# ------------------------------------------------------------- counts

@pytest.mark.parametrize(("sig", "fubini"), [(SIG1, 3), (SIG2, 75), (SIG3, 545_835)],
                         ids=["n=1", "n=2", "n=3"])
def test_ordering_count_is_fubini(sig, fubini):
    assert sum(1 for _ in orderings(sig)) == fubini


@pytest.mark.parametrize(("sig", "bell"), [(SIG1, 2), (SIG2, 15), (SIG3, 4_140)],
                         ids=["n=1", "n=2", "n=3"])
def test_partition_count_is_bell(sig, bell):
    assert sum(1 for _ in partitions(sig)) == bell


@pytest.mark.parametrize("sig", [SIG1, SIG2, SIG3], ids=["n=1", "n=2", "n=3"])
def test_untrusted_count_is_power_of_two(sig):
    assert len(list(untrusted_sets(sig))) == 2 ** len(sig)


def test_family_sizes_for_two_variables():
    assert sum(1 for _ in agm_family(SIG2)) == 75
    assert sum(1 for _ in tsr_family(SIG2)) == 75 * 15
    assert sum(1 for _ in vfr_family(SIG2)) == 75 * 4
    assert set(FAMILIES) == {"AGM", "TSR", "VFR"}


# ------------------------------------------------------------- no repeats, all valid

def test_orderings_are_distinct_and_valid():
    all_orderings = list(orderings(SIG2))
    assert len(set(all_orderings)) == len(all_orderings)
    for ordering in all_orderings:
        AGMRevision(ordering)          # raises if a tier is empty, repeated or missing


def test_partitions_are_distinct_and_include_both_extremes():
    all_partitions = list(partitions(SIG2))
    assert len(set(all_partitions)) == len(all_partitions)
    assert StatePartition.unit(SIG2) in all_partitions
    assert StatePartition.trivial(SIG2) in all_partitions


def test_untrusted_sets_run_from_full_trust_to_none():
    sets = list(untrusted_sets(SIG2))
    assert sets[0] == frozenset()
    assert sets[-1] == frozenset({"p", "q"})


def test_every_consistent_belief_set_appears_as_a_bottom_tier():
    """Every consistent K is covered, each with all its faithful orderings."""
    bottoms = {ordering[0] for ordering in orderings(SIG2)}
    assert bottoms == {m for m in meanings(SIG2) if m}


# ------------------------------------------------------------- members are what they say

def test_agm_members_are_plain_agm_revision():
    for member in agm_family(SIG2):
        assert isinstance(member.operator.transform, IdentityTransform)
        agm = AGMRevision(member.ordering)
        for m in meanings(SIG2):
            assert member.operator.revise(dnf(m, SIG2)) == agm.revise(m)


def test_members_carry_their_parameters():
    tsr = next(tsr_family(SIG2))
    assert tsr.partition is not None and tsr.untrusted is None
    assert tsr.operator.transform.partition == tsr.partition

    vfr = next(vfr_family(SIG2))
    assert vfr.untrusted is not None and vfr.partition is None
    assert vfr.operator.transform.untrusted == vfr.untrusted


def test_describe_names_the_operator():
    member = next(
        m for m in vfr_family(SIG2)
        if m.ordering == (frozenset({TT}), frozenset({TF, FT}), frozenset({FF}))
        and m.untrusted == {"p"}
    )
    assert member.describe() == "VFR, ordering {TT} < {TF, FT} < {FF}, untrusted {p}"

    trusted_fully = next(m for m in vfr_family(SIG2) if not m.untrusted)
    assert trusted_fully.describe().endswith("untrusted ∅")

    alarm = StatePartition.from_cells([[TT, FF], [TF, FT]])
    member = next(m for m in tsr_family(SIG2) if m.partition == alarm)
    assert member.describe().endswith("partition {TT, FF} | {TF, FT}")
