"""Tests for forgetting_revision.selective_revision.

VFR and TSR are both selective revision operators, K ◦ α = K ∗ f(α).
They share the AGM revision ∗ and differ only in the transformation f.
"""

import random
from functools import reduce
from itertools import chain, combinations

import pytest

from forgetting_revision import (
    BOTTOM,
    TOP,
    AGMRevision,
    And,
    ForgetTransform,
    Formula,
    Iff,
    Implies,
    Not,
    Or,
    SelectiveRevision,
    Signature,
    State,
    StatePartition,
    TrustExpansion,
    Var,
    models,
    states_str,
)

# ---------------------------------------------------------------------- #
# Helpers
# ---------------------------------------------------------------------- #

def subsets(xs):
    xs = list(xs)
    return [frozenset(c) for c in chain.from_iterable(combinations(xs, r) for r in range(len(xs) + 1))]


def formula_with_models(states, sig: Signature) -> Formula:
    """A DNF formula whose models are exactly `states` (B&H Defs 5-6).

    Each state becomes a conjunction of literals, and the conjunctions are
    OR-ed together. One formula per set of states covers every formula up
    to logical equivalence.
    """
    def literal(name: str, value: bool) -> Formula:
        return Var(name) if value else ~Var(name)

    def conjunction(state: State) -> Formula:
        return reduce(And, (literal(n, v) for n, v in zip(sig.names, state)))

    states = sorted(states)
    return reduce(Or, (conjunction(s) for s in states)) if states else BOTTOM


def random_formula(rng: random.Random, names, depth: int = 4) -> Formula:
    """A random formula, so the tests also see non-DNF syntax."""
    if depth == 0 or rng.random() < 0.25:
        return rng.choice([Var(n) for n in names] + [TOP, BOTTOM])
    op = rng.choice([Not, And, Or, Implies, Iff])
    if op is Not:
        return ~random_formula(rng, names, depth - 1)
    return op(random_formula(rng, names, depth - 1), random_formula(rng, names, depth - 1))


# ---------------------------------------------------------------------- #
# Booth & Hunter Example 3, driven by formulas
# ---------------------------------------------------------------------- #

"""
Booth & Hunter (2018), Example 3: a patient visits a doctor, who says
"you have a viral infection, and the jewel in your necklace is not a
diamond". The patient should trust the medical claim but not the
jewellery one.
Two variables, in signature order (sick, diam):
  sick = the patient has an infection
  diam = the necklace jewel is a diamond
"""
SIG2 = Signature.of("sick diam")
sick, diam = Var("sick"), Var("diam")

SD = (True, True)     # {sick, diam}
S = (True, False)     # {sick}
D = (False, True)     # {diam}
E = (False, False)    # {}


@pytest.fixture
def k3() -> AGMRevision:
    # The patient's prior plausibility ordering: {diam} < {sick, diam} ~ {} < {sick}
    return AGMRevision.from_tiers([[D], [SD, E], [S]])


@pytest.mark.parametrize(
    "alpha, expected",
    [
        (sick, {SD}),            # (1) sick and diam
        (~diam, {D}),            # (2) unchanged: not sick, diam
        (sick & ~diam, {SD}),    # (3) sick and diam
    ],
    ids=str,
)
def test_example3_vfr_and_tsr_agree_with_paper(k3, alpha, expected):
    vfr = SelectiveRevision.vfr(k3, SIG2, untrusted="diam")
    tsr = SelectiveRevision.tsr(k3, SIG2, StatePartition.from_untrusted(SIG2, "diam"))
    assert vfr.revise(alpha) == expected, states_str(vfr.revise(alpha))
    assert tsr.revise(alpha) == expected, states_str(tsr.revise(alpha))


def test_belief_states_pass_through(k3):
    assert SelectiveRevision.vfr(k3, SIG2, "diam").belief_states() == {D}


# ---------------------------------------------------------------------- #
# Dissertation §5: Doctor-Necklace examples
# ---------------------------------------------------------------------- #

def test_doctor_necklace_forgets_to_p():
    sig = Signature.of("p q")
    p, q = Var("p"), Var("q")
    assert ForgetTransform(sig, "q")(p & ~q) == models(p, sig)


def test_extended_doctor_necklace_forgets_to_p():
    sig = Signature.of("p q r")
    p, q, r = Var("p"), Var("q"), Var("r")
    alpha = p & (~q >> r)                  # brackets needed: >> binds tighter than &
    assert ForgetTransform(sig, {"q", "r"})(alpha) == models(p, sig)


# ---------------------------------------------------------------------- #
# Dissertation §6: VFR is a special case of TSR.
# Forget(α, T) and Π_T[α] give the same states for every α and every T.
# ---------------------------------------------------------------------- #

SIGNATURES = [Signature.of("p q"), Signature.of("p q r")]


@pytest.mark.parametrize("sig", SIGNATURES, ids=lambda s: " ".join(s.names))
def test_forgetting_equals_trust_expansion_on_every_formula(sig):
    all_formulas = [formula_with_models(x, sig) for x in subsets(sig.states())]
    for untrusted in subsets(sig.names):
        forget = ForgetTransform(sig, untrusted)
        expand = TrustExpansion(sig, StatePartition.from_untrusted(sig, untrusted))
        for alpha in all_formulas:
            assert forget(alpha) == expand(alpha), f"{alpha}, forgetting {sorted(untrusted)}"


@pytest.mark.parametrize("seed", range(5))
def test_forgetting_equals_trust_expansion_on_random_syntax(seed):
    rng = random.Random(seed)              # fixed seed: any failure is reproducible
    sig = Signature.of("p q r")
    for _ in range(100):
        alpha = random_formula(rng, sig.names)
        untrusted = frozenset(rng.sample(sig.names, rng.randint(0, 3)))
        forget = ForgetTransform(sig, untrusted)
        expand = TrustExpansion(sig, StatePartition.from_untrusted(sig, untrusted))
        assert forget(alpha) == expand(alpha), f"{alpha}, forgetting {sorted(untrusted)}"


def test_mismatched_partition_gives_different_states():
    # Guard against a vacuous equivalence test: the wrong partition must differ.
    sig = Signature.of("p q r")
    p, q, r = Var("p"), Var("q"), Var("r")
    alpha = p & q & r
    forget_q = ForgetTransform(sig, "q")(alpha)
    expand_r = TrustExpansion(sig, StatePartition.from_untrusted(sig, "r"))(alpha)
    assert forget_q != expand_r


# ---------------------------------------------------------------------- #
# Dissertation §6.3: Postulates 1 and 2
# ---------------------------------------------------------------------- #

K_CHOICES = [k for k in subsets(SIG2.states()) if k]
CONSISTENT = [formula_with_models(x, SIG2) for x in subsets(SIG2.states()) if x]


@pytest.mark.parametrize("k", K_CHOICES, ids=states_str)
def test_postulate1_fully_distrusted_source_changes_nothing(k):
    vfr = SelectiveRevision.vfr(AGMRevision.from_dalal(k), SIG2, untrusted=SIG2.names)
    for alpha in CONSISTENT:
        assert vfr.revise(alpha) == k, str(alpha)


def test_postulate1_needs_consistent_input(k3):
    # Forget preserves falsity, so revising by ⊥ gives the inconsistent set.
    vfr = SelectiveRevision.vfr(k3, SIG2, untrusted=SIG2.names)
    assert vfr.revise(BOTTOM) == frozenset()


@pytest.mark.parametrize("k", K_CHOICES, ids=states_str)
def test_postulate2_fully_trusted_source_is_plain_agm(k):
    agm = AGMRevision.from_dalal(k)
    vfr = SelectiveRevision.vfr(agm, SIG2, untrusted=())
    for alpha in CONSISTENT + [BOTTOM]:
        assert vfr.revise(alpha) == agm.revise(models(alpha, SIG2)), str(alpha)


# ---------------------------------------------------------------------- #
# Dissertation §6.3.1: Very Weak Success fails (XOR counterexample)
# ---------------------------------------------------------------------- #

def test_very_weak_success_counterexample():
    sig = Signature.of("p q")
    p, q = Var("p"), Var("q")
    k = models((~p & q) | (p & ~q), sig)        # K = p XOR q
    alpha = ~(p & ~q)

    vfr = SelectiveRevision.vfr(AGMRevision.from_dalal(k), sig, untrusted="p")

    # Antecedent: K ⊬ ¬α  and  K ◦ ¬α ⊢ ¬α
    assert not k <= models(~alpha, sig)
    assert vfr.revise(~alpha) <= models(~alpha, sig)
    # Consequent fails: K ◦ α ⊬ α
    assert not vfr.revise(alpha) <= models(alpha, sig)


# ---------------------------------------------------------------------- #
# The protocols: SelectiveRevision accepts any revision and transformation
# ---------------------------------------------------------------------- #

def test_any_transformation_plugs_in(k3):
    # The identity transformation turns selective revision into plain AGM.
    plain = SelectiveRevision(k3, lambda alpha: models(alpha, SIG2))
    assert plain.revise(sick & ~diam) == {S}


def test_any_revision_operator_plugs_in():
    class Stubborn:
        """A (non-AGM) revision operator that never changes its mind."""
        def belief_states(self) -> frozenset[State]:
            return frozenset({D})

        def revise(self, candidates: frozenset[State]) -> frozenset[State]:
            return self.belief_states()

    op = SelectiveRevision.vfr(Stubborn(), SIG2, untrusted="diam")
    assert op.revise(sick) == {D}


def test_any_forget_operator_plugs_in(k3):
    class NoForget:
        """Forgets nothing, so VFR behaves like plain AGM."""
        def __call__(self, formula, forget):
            return formula

    op = SelectiveRevision.vfr(k3, SIG2, untrusted="diam", forget=NoForget())
    assert op.revise(sick & ~diam) == {S}


# ---------------------------------------------------------------------- #
# Validation
# ---------------------------------------------------------------------- #

def test_unknown_untrusted_variable_rejected():
    with pytest.raises(ValueError):
        ForgetTransform(SIG2, {"jewel"})


def test_single_name_not_split_into_characters():
    assert ForgetTransform(SIG2, "diam").untrusted == frozenset({"diam"})


def test_partition_signature_mismatch_rejected():
    with pytest.raises(ValueError):
        TrustExpansion(Signature.of("p q r"), StatePartition.trivial(SIG2))