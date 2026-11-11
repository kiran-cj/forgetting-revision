"""Tests for beliefrev.revision.

States use signature order (sick, diam), as in Booth & Hunter Example 3.
"""

import pytest

from forgetting_revision import AGMRevision

"""
Booth & Hunter (2018), Example 3: a patient visits a doctor, who says
"you have a viral infection, and the jewel in your necklace is not a
diamond". The patient should trust the medical claim but not the
jewellery one.
Two variables, in signature order (sick, diam):
  sick = the patient has an infection
  diam = the necklace jewel is a diamond
"""
SD = (True, True)    # {sick, diam}
S = (True, False)    # {sick}
D = (False, True)    # {diam}
E = (False, False)   # {} (empty set of true variables)
ALL = frozenset({SD, S, D, E})


@pytest.fixture
def example3() -> AGMRevision:
    # {diam} < {sick, diam} ~ {} < {sick}
    return AGMRevision.from_tiers([[D], [SD, E], [S]])


def test_belief_states_are_bottom_tier(example3):
    assert example3.belief_states() == {D}


@pytest.mark.parametrize(
    "candidates, expected",
    [
        ({SD, S}, {SD}),        # beta = sick
        ({S, E}, {E}),          # beta = not diam
        ({S}, {S}),             # beta = sick and not diam
        (ALL, {D}),             # beta = top: Identity, nothing changes
        ({SD, E}, {SD, E}),     # beta = sick <-> diam: tie, both survive
        (set(), set()),         # beta = bottom: inconsistent result
    ],
    ids=[
        "sick", "not diam", "sick and not diam", "top", "tie", "bottom",
    ],
)
def test_example3_revisions(example3, candidates, expected):
    assert example3.revise(frozenset(candidates)) == expected


def test_rank(example3):
    assert [example3.rank(s) for s in (D, SD, E, S)] == [0, 1, 1, 2]


@pytest.mark.parametrize(
    "tiers",
    [
        [],                          # no tiers
        [[D], [], [SD, E, S]],       # empty tier
        [[D], [SD, E]],              # S missing: not total
        [[D, SD], [SD, E, S]],       # SD ranked twice
        [[D, (True,)], [SD, E, S]],  # mixed state lengths
    ],
    ids=["no tiers", "empty tier", "not total", "duplicate state", "mixed lengths"],
)
def test_invalid_rankings_rejected(tiers):
    with pytest.raises(ValueError):
        AGMRevision.from_tiers(tiers)


def test_unknown_candidate_rejected(example3):
    with pytest.raises(ValueError):
        example3.revise(frozenset({(True, True, True)}))


def test_dalal_reproduces_example3_ordering(example3):
    # K = not sick and diam. Hamming distances: D=0, SD=1, E=1, S=2.
    assert AGMRevision.from_dalal({D}) == example3


def test_dalal_rejects_inconsistent_k():
    with pytest.raises(ValueError):
        AGMRevision.from_dalal(set())