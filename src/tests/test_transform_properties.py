"""Tests for the nine transformation-function properties (f1-f9) and Yao's theorem.

The dissertation (§6.2) proves the Kuratowski properties and Pawlak for
Forget() with one example each. Here they are checked on every input, for
every ForgetTransform over two and three variables, and the link to TSR is
made explicit: induced_partition() recovers the partition each f comes from.
"""

from itertools import combinations, product

import pytest

from forgetting_revision import (
    ForgetTransform,
    IdentityTransform,
    Not,
    Signature,
    StatePartition,
    TableTransform,
    TrustExpansion,
    meanings,
    models,
    partitions,
    untrusted_sets,
)
from forgetting_revision.transform_properties import (
    KURATOWSKI,
    PROPERTIES,
    TransformTable,
    check_transform,
    induced_partition,
    is_kuratowski,
    transform_property,
)

SIG1, SIG2, SIG3 = Signature.of("p"), Signature.of("p q"), Signature.of("p q r")
TT, TF, FT, FF = (True, True), (True, False), (False, True), (False, False)
T, F = (True,), (False,)
ALL2 = frozenset(SIG2.states())


def failing(f, sig):
    """Names of the properties f fails."""
    return {name for name, r in check_transform(f, sig).items() if not r.holds}


# ============================================================ registry

def test_nine_properties_registered_in_order():
    assert [p.code for p in PROPERTIES.values()] == [f"f{i}" for i in range(1, 10)]
    assert sum(p.kind == KURATOWSKI for p in PROPERTIES.values()) == 5


def test_every_property_has_its_metadata():
    for p in PROPERTIES.values():
        assert p.name and p.kind and p.source and p.statement


def test_registering_a_duplicate_is_an_error():
    with pytest.raises(ValueError, match="registered twice"):
        @transform_property("f2", "Implication again", KURATOWSKI, "test", "test")
        def dup(F, f):
            yield True, ()


# ============================================================ the real transforms satisfy all nine

def test_identity_satisfies_all_nine():
    assert failing(IdentityTransform(SIG2), SIG2) == set()


@pytest.mark.parametrize("partition", list(partitions(SIG2)), ids=lambda p: str(len(p.cells)) + " cells")
def test_every_trust_expansion_satisfies_all_nine(partition):
    assert failing(TrustExpansion(SIG2, partition), SIG2) == set()


@pytest.mark.parametrize("sig", [SIG2, SIG3], ids=["n=2", "n=3"])
def test_every_forget_transform_satisfies_all_nine(sig):
    """The dissertation's §6.2 claims, checked on every input instead of one example."""
    for untrusted in untrusted_sets(sig):
        bad = failing(ForgetTransform(sig, untrusted), sig)
        assert not bad, f"untrusted {sorted(untrusted)} fails {bad}"


def test_sample_of_three_variable_partitions():
    """4,140 partitions is too many for a quick test; take an even spread."""
    sample = list(partitions(SIG3))[::700]
    assert len(sample) == 6
    for partition in sample:
        assert failing(TrustExpansion(SIG3, partition), SIG3) == set()


# ============================================================ Yao's theorem: VFR ⊆ TSR

@pytest.mark.parametrize("sig", [SIG2, SIG3], ids=["n=2", "n=3"])
def test_forget_transform_comes_from_the_forgetting_partition(sig):
    """The partition behind Forget(·, U) is exactly 'agree on the trusted variables'."""
    for untrusted in untrusted_sets(sig):
        recovered = induced_partition(ForgetTransform(sig, untrusted), sig)
        assert recovered == StatePartition.from_untrusted(sig, untrusted)


def test_trust_expansion_gives_back_its_own_partition():
    for partition in partitions(SIG2):
        assert induced_partition(TrustExpansion(SIG2, partition), SIG2) == partition


def test_only_4_of_15_partitions_come_from_forgetting():
    """§6.5.4: VFR is strictly less expressive than TSR."""
    from_vfr = {induced_partition(ForgetTransform(SIG2, u), SIG2) for u in untrusted_sets(SIG2)}
    assert len(from_vfr) == 4
    alarm = StatePartition.from_cells([[TT, FF], [TF, FT]])
    assert alarm not in from_vfr


def test_every_function_over_one_variable():
    """All 4^4 = 256 maps from meanings to meanings over {p}.
    Exactly 4 are Kuratowski, and exactly 2 (= Bell(2)) are also Pawlak."""
    ms = meanings(SIG1)
    kuratowski = pawlak = 0
    for images in product(ms, repeat=len(ms)):
        results = check_transform(TableTransform(SIG1, dict(zip(ms, images, strict=True))), SIG1)
        if is_kuratowski(results):
            kuratowski += 1
            pawlak += results["Pawlak"].holds
    assert (kuratowski, pawlak) == (4, 2)


def test_every_kuratowski_function_over_two_variables():
    """Every Kuratowski f is fixed by f({s}) for each state s (by disjunctive
    distribution), and f({s}) must contain s (by implication). So the 8^4 =
    4,096 choices of those four sets cover every Kuratowski f.

    Result: 355 Kuratowski functions (the number of preorders on 4 points),
    exactly 15 (= Bell(4)) are Pawlak, and Pawlak, Conjunctive weakening and
    Trust symmetry agree on every one of them, as B&H §4.2 says.
    """
    states = SIG2.states()

    def options(s):
        others = [t for t in states if t != s]
        return [frozenset({s, *c}) for r in range(len(others) + 1) for c in combinations(others, r)]

    idempotence = [PROPERTIES["Idempotence"]]
    kuratowski = pawlak = 0
    for images in product(*(options(s) for s in states)):
        g = dict(zip(states, images, strict=True))
        f = TableTransform.from_function(SIG2, lambda a, g=g: frozenset().union(*(g[s] for s in a)))
        if not check_transform(f, SIG2, idempotence)["Idempotence"].holds:
            continue                          # cheap filter: the only property not built in
        results = check_transform(f, SIG2)
        assert is_kuratowski(results)
        kuratowski += 1
        pawlak += results["Pawlak"].holds
        assert (results["Pawlak"].holds
                == results["Conjunctive weakening"].holds
                == results["Trust symmetry"].holds)
    assert (kuratowski, pawlak) == (355, 15)


# ============================================================ negative controls

def ex5():
    """B&H Example 5 over {p}: f(p) = ⊤, f(¬p) = ¬p."""
    return TableTransform(SIG1, {frozenset(): frozenset(), frozenset({T}): frozenset({T, F}),
                                 frozenset({F}): frozenset({F}), frozenset({T, F}): frozenset({T, F})})


def test_example_5_is_kuratowski_but_not_partition_based():
    assert failing(ex5(), SIG1) == {"Pawlak", "Conjunctive weakening", "Trust symmetry"}
    assert induced_partition(ex5(), SIG1) is None


@pytest.mark.parametrize(("f", "expected"), [
    # f(φ) = ⊥ for everything: never implied by a consistent φ
    (lambda a: frozenset(), {"Implication"}),
    # f(⊥) = ⊤: not falsity preserving
    (lambda a: ALL2, {"Falsity preservation"}),
    # adds one more state each time: grows on every application
    (lambda a: a | {next((s for s in SIG2.states() if s not in a), TT)},
     {"Falsity preservation", "Idempotence"}),
    # B&H §7: only p is weakened, so p ∨ q is not weakened as much as p
    (lambda a: ALL2 if a == {TT, TF} else a,
     {"Disjunctive distribution", "Monotonicity"}),
], ids=["always ⊥", "always ⊤", "keeps growing", "non-monotone"])
def test_broken_functions_fail_the_right_properties(f, expected):
    assert expected <= failing(TableTransform.from_function(SIG2, f), SIG2)


class SyntaxSensitive(IdentityTransform):
    """Treats ¬¬α differently from α."""
    def __call__(self, alpha):
        if isinstance(alpha, Not) and isinstance(alpha.operand, Not):
            return frozenset(SIG2.states())
        return models(alpha, self.signature)


def test_syntax_dependent_transform_fails_extensionality():
    result = check_transform(SyntaxSensitive(SIG2), SIG2)["Extensionality"]
    assert not result.holds
    assert "spelt as" in result.explain()


# ============================================================ table and reporting

def test_transform_table_is_built_from_the_real_transform():
    f = ForgetTransform(SIG2, "q")
    F = TransformTable.build(f, SIG2)
    assert len(F.images) == 16
    assert F(frozenset({TF})) == {TT, TF}           # Forget(p ∧ ¬q, q) = p
    assert F.neg(frozenset({TF})) == ALL2 - {TF}


def test_explain():
    results = check_transform(ex5(), SIG1)
    assert results["Pawlak"].explain().startswith("f7 Pawlak: FAILS at φ = ")
    assert results["Implication"].explain().startswith("f2 Implication: holds on 4 cases")
