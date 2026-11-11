"""Tests for forgetting_revision.trust (Booth & Hunter's trust partitions)."""

from itertools import chain, combinations

import pytest

from forgetting_revision import (
    AGMRevision,
    Signature,
    StatePartition,
    Var,
    models,
    states_str,
)

"""
Booth & Hunter (2018), Example 3: a patient visits a doctor, who says
"you have a viral infection, and the jewel in your necklace is not a
diamond". The patient should trust the medical claim but not the
jewellery one.
Two variables, in signature order (sick, diam):
  sick = the patient has an infection
  diam = the necklace jewel is a diamond
"""

SIG = Signature.of("sick diam")
sick, diam = Var("sick"), Var("diam")

SD = (True, True)     # {sick, diam}
S = (True, False)     # {sick}
D = (False, True)     # {diam}
E = (False, False)    # {}
ALL = frozenset(SIG.states())


@pytest.fixture
def ranking() -> AGMRevision:
    # The patient's prior plausibility ordering: {diam} < {sick, diam} ~ {} < {sick}
    return AGMRevision.from_tiers([[D], [SD, E], [S]])


@pytest.fixture
def doctor() -> StatePartition:
    # Trusted on sick, not on diam: {sick, diam}, {sick} | {diam}, {}
    return StatePartition.from_untrusted(SIG, "diam")


def tsr(ranking, partition, candidates):
    """Trust-sensitive revision: AGM revision by the trust expansion."""
    return ranking.revise(partition.expand(frozenset(candidates)))


def subsets(xs):
    xs = list(xs)
    return [frozenset(c) for c in chain.from_iterable(combinations(xs, r) for r in range(len(xs) + 1))]


# ---------------------------------------------------------------------- #
# Booth & Hunter Examples 2 and 3
# ---------------------------------------------------------------------- #

def test_doctor_partition_matches_paper(doctor):
    assert doctor == StatePartition.from_cells([[SD, S], [D, E]])


def test_jeweller_partition_matches_paper():
    jeweller = StatePartition.from_untrusted(SIG, "sick")
    assert jeweller == StatePartition.from_cells([[SD, D], [S, E]])


def test_cell_of(doctor):
    assert doctor.cell_of(S) == {SD, S}
    assert doctor.cell_of(E) == {D, E}


@pytest.mark.parametrize(
    "alpha, expanded, result",
    [
        (sick, {SD, S}, {SD}),          # (1) sick and diam
        (~diam, ALL, {D}),              # (2) unchanged: not sick, diam
        (sick & ~diam, {SD, S}, {SD}),  # (3) sick and diam
    ],
)
def test_example3(ranking, doctor, alpha, expanded, result):
    candidates = models(alpha, SIG)
    assert doctor.expand(candidates) == expanded, states_str(doctor.expand(candidates))
    assert tsr(ranking, doctor, candidates) == result


# ---------------------------------------------------------------------- #
# Booth & Hunter Propositions 1 and 2 (extreme cases)
# ---------------------------------------------------------------------- #

NONEMPTY = [x for x in subsets(ALL) if x]


@pytest.mark.parametrize("candidates", NONEMPTY, ids=states_str)
def test_trivial_partition_ignores_consistent_reports(ranking, candidates):
    assert tsr(ranking, StatePartition.trivial(SIG), candidates) == ranking.belief_states()


def test_trivial_partition_on_inconsistent_report(ranking):
    # Prop 1 says "for all phi", but Pi[bottom] is empty, so the result is
    # inconsistent rather than K. The claim needs phi to be consistent.
    assert tsr(ranking, StatePartition.trivial(SIG), set()) == frozenset()


@pytest.mark.parametrize("candidates", subsets(ALL), ids=states_str)
def test_unit_partition_is_plain_agm(ranking, candidates):
    unit = StatePartition.unit(SIG)
    assert unit.expand(candidates) == candidates
    assert tsr(ranking, unit, candidates) == ranking.revise(candidates)


# ---------------------------------------------------------------------- #
# Partitions produced by forgetting
# ---------------------------------------------------------------------- #

SIG3 = Signature.of("p q r")


@pytest.mark.parametrize("untrusted", subsets(SIG3.names), ids=lambda t: ",".join(sorted(t)) or "none")
def test_forgetting_gives_equal_sized_cells(untrusted):
    # 2^(trusted) cells, each holding 2^(untrusted) states
    pi = StatePartition.from_untrusted(SIG3, untrusted)
    trusted = len(SIG3) - len(untrusted)
    assert len(pi.cells) == 2 ** trusted
    assert all(len(cell) == 2 ** len(untrusted) for cell in pi.cells)


def test_extremes_of_forgetting():
    assert StatePartition.from_untrusted(SIG3, []) == StatePartition.unit(SIG3)
    assert StatePartition.from_untrusted(SIG3, SIG3.names) == StatePartition.trivial(SIG3)


def test_cells_differ_only_on_untrusted_variables():
    pi = StatePartition.from_untrusted(SIG3, "r")
    for cell in pi.cells:
        assert len({s[:2] for s in cell}) == 1     # every state agrees on p and q


# ---------------------------------------------------------------------- #
# Kuratowski properties + Pawlak, for every partition of 2 variables
# (Booth & Hunter Propositions 5 and 8)
# ---------------------------------------------------------------------- #

def set_partitions(items):
    """Yield every way to split items into non-empty groups (Bell number many)."""
    if not items:
        yield []
        return
    first, *rest = items
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | {first}] + p[i + 1:]
        yield p + [{first}]


ALL_PARTITIONS = [StatePartition.from_cells(p) for p in set_partitions(sorted(ALL))]


def test_there_are_15_partitions_of_4_states():
    assert len(set(ALL_PARTITIONS)) == 15   # Bell(4)


@pytest.mark.parametrize("pi", ALL_PARTITIONS)
def test_kuratowski_and_pawlak(pi):
    f = pi.expand
    assert f(frozenset()) == frozenset()                  # falsity preservation
    for a in subsets(ALL):
        assert a <= f(a)                                  # implication
        assert f(f(a)) == f(a)                            # idempotence
        assert f(ALL - f(a)) == ALL - f(a)                # Pawlak
        for b in subsets(ALL):
            assert f(a | b) == f(a) | f(b)                # disjunctive distribution


# ---------------------------------------------------------------------- #
# Dissertation §6.5: forgetting partitions are a strict subset
# ---------------------------------------------------------------------- #

def test_alarm_partition_cannot_come_from_forgetting():
    # Both-or-neither alarms vs exactly one: {TT, FF} | {TF, FT}
    alarm = StatePartition.from_key(SIG, lambda s: s[0] == s[1])
    assert alarm == StatePartition.from_cells([[SD, E], [S, D]])

    forgetting = {StatePartition.from_untrusted(SIG, t) for t in subsets(SIG.names)}
    assert alarm not in forgetting
    assert len(forgetting) == 4     # only 4 of the 15 partitions are reachable


def test_unequal_cells_are_legal_for_tsr():
    # A legal Booth & Hunter partition that forgetting can never produce
    lopsided = StatePartition.from_cells([[SD], [S, D, E]])
    forgetting = {StatePartition.from_untrusted(SIG, t) for t in subsets(SIG.names)}
    assert lopsided not in forgetting


# ---------------------------------------------------------------------- #
# Validation
# ---------------------------------------------------------------------- #

@pytest.mark.parametrize(
    "cells",
    [
        [],                             # no cells
        [[SD, S], [], [D, E]],          # empty cell
        [[SD, S], [D]],                 # E missing
        [[SD, S], [S, D, E]],           # S in two cells
        [[SD, (True,)], [S, D, E]],     # mixed lengths
    ],
)
def test_invalid_partitions_rejected(cells):
    with pytest.raises(ValueError):
        StatePartition.from_cells(cells)


def test_unknown_untrusted_variable_rejected():
    with pytest.raises(ValueError):
        StatePartition.from_untrusted(SIG, "jewel")


def test_single_name_is_not_split_into_characters():
    assert StatePartition.from_untrusted(SIG, "diam") == StatePartition.from_untrusted(SIG, ["diam"])


def test_unknown_state_rejected(doctor):
    with pytest.raises(ValueError):
        doctor.expand(frozenset({(True, True, True)}))