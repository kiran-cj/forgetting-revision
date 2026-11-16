# Variable Forgetting Revision

A Python implementation of **Variable Forgetting Revision (VFR)**, a trust-based belief revision operator I defined in my MSc dissertation at Cardiff University, *Forgotten Truths: Exploring Variable Forgetting in Belief Revision* (supervised by Richard Booth).

The goal is to turn the dissertation's pen-and-paper results into code that checks them **exhaustively** on small signatures, rather than through a handful of worked examples.

The package checks **24 postulates** from AGM revision and from Booth & Hunter's *Trust as a Precursor to Belief Revision* (2018) against **every** AGM, Trust-Sensitive (TSR) and Variable Forgetting (VFR) operator over two variables, 1,500 operators in all. It also checks **9 properties** of the transformation functions, and **12 specific claims and counterexamples** from the two papers. All of them match the literature, and along the way the checker found [five corrections](#findings) to the dissertation.


## The idea in one example

A doctor says to the patient: *"You have a viral infection, and the jewel on your necklace is not a diamond."*

The patient naturally accepts the diagnosis but rejects (forgets) the claim on the jewellery, because the doctor is considered to be an expert in the medical field but not on gemstones and jewellery. Classical (AGM) belief revision can't do this, since it must accept the whole input.

VFR handles it in two steps:

1. **Forget** the variables the source isn't trusted on.
2. **Revise** by what's left, using an ordinary AGM revision operator.

```
K ∘ α  =  K ∗ Forget(α, U)
```

where `U` is the set of variables the source is *not* trusted on (written `T_B` in the dissertation).

With `p` = "you have a viral infection", `q` = "the jewel is a diamond", `α = p ∧ ¬q` and `U = {q}`:

```
Forget(p ∧ ¬q, {q})  =  (p ∧ ¬⊤) ∨ (p ∧ ¬⊥)  ≡  p
```

so the patient revises his belief by the fact that he has a viral infection alone.


## Quick start

Needs Python 3.14 and [uv](https://docs.astral.sh/uv/).

```bash
git clone https://github.com/kiran-cj/forgetting-revision.git
cd forgetting-revision
uv run pytest -q              # the test suite
uv run check-postulates       # every postulate, every operator, with counterexamples
```

The doctor example in code:

```python
from forgetting_revision import AGMRevision, SelectiveRevision, Signature, Var, states_str
from forgetting_revision.postulates import check

sig = Signature.of("sick diam")
sick, diam = Var("sick"), Var("diam")

# The patient's plausibility ordering (Booth & Hunter, Example 3), most plausible first
k = AGMRevision.from_tiers([[(False, True)], [(True, True), (False, False)], [(True, False)]])
doctor = SelectiveRevision.vfr(k, sig, untrusted="diam")

states_str(doctor.revise(sick & ~diam))   # '{TT}': now believes sick (and still diam)

results = check(doctor, sig)               # all 24 postulates for this one operator
results["Success"].explain()               # 'Success: FAILS at φ = {TF}, K◦φ = {TT}'
results["Feeble success"].explain()        # 'Feeble success: holds on 3 cases'
```


## How the checker works

- **Meanings, not formulas.** Over n variables there are infinitely many formulas but only 2^(2^n) meanings (sets of states): 16 for two variables. The checker builds one formula per meaning, asks the real operator to revise by it, and stores the 16 results. Each postulate is then a few set operations on that table.
- **Extensionality makes that sound.** Revising by five different spellings of every meaning must give the same answer. For VFR this tests the syntactic forgetting itself (`substitute`, `simplify`).
- **Every operator, not a few.** Orderings over states are counted by the Fubini numbers (75 for two variables) and state partitions by the Bell numbers (15). Each AGM operator is one ordering, each TSR operator an ordering plus a partition, and each VFR operator an ordering plus a set of untrusted variables.
- **Counterexamples, not just verdicts.** A failure names the exact operator and inputs. Each check also counts how often its premise came up, so a pass where the premise never arose is flagged as *vacuous*.
- **Negative controls.** Booth & Hunter's own counterexamples are run through the checker, which must report them as failures. That shows its "✓" verdicts can be trusted.
- **Yao's theorem in code.** `induced_partition(f)` recovers the state partition behind any partition-based transformation. Applied to `Forget(·, U)`, it gives exactly the "agree on the trusted variables" partition, which is the dissertation's main result, VFR ⊆ TSR.


## Results

<!-- verdicts:start -->
Checked exhaustively over 2 variables (p, q): 75 AGM, 1,125 TSR, 300 VFR operators.

#### Postulates

| # | Postulate | Source | AGM | TSR | VFR |
|---:|---|---|---|---|---|
| 1 | Closure | AGM K\*1 | ✓ | ✓ | ✓ |
| 2 | Success | AGM K\*2 | ✓ | ✗ (1,050 fail) | ✗ (225 fail) |
| 3 | Inclusion | AGM K\*3; B&H Prop 3 | ✓ | ✓ | ✓ |
| 4 | Vacuity | AGM K\*4; dissertation §6.3.2 | ✓ | ✗ (304 fail) | ✗ (69 fail) |
| 5 | Consistency | AGM K\*5 (B&H 'iff' form, Prop 3) | ✓ | ✓ | ✓ |
| 6 | Extensionality | AGM K\*6; B&H Prop 3 | ✓ | ✓ | ✓ |
| 7 | Superexpansion | AGM K\*7; dissertation §3.1 | ✓ | ✗ (1,050 fail) | ✗ (225 fail) |
| 8 | Subexpansion | AGM K\*8; dissertation §3.1 | ✓ | ✗ (926 fail) | ✗ (173 fail) |
| 9 | Identity | B&H Prop 3 | ✓ | ✓ | ✓ |
| 10 | Proxy success | Fermé & Hansson; B&H Prop 3; dissertation §6.3.1 | ✓ | ✓ | ✓ |
| 11 | Consistent expansion | B&H Prop 3 | ✓ | ✓ | ✓ |
| 12 | Disjunctive overlap | B&H Prop 3 | ✓ | ✓ | ✓ |
| 13 | Disjunctive inclusion | B&H Prop 3 | ✓ | ✓ | ✓ |
| 14 | Disjunctive factoring | B&H Prop 3 | ✓ | ✓ | ✓ |
| 15 | Disjunctive extension | B&H Prop 4; dissertation §6.2 | ✓ | ✓ | ✓ |
| 16 | Disjunctive equivalence | B&H Prop 4; dissertation §6.2 | ✓ | ✓ | ✓ |
| 17 | Disjoint outcome basis | B&H Prop 6 | ✓ | ✓ | ✓ |
| 18 | Deficit makeup | B&H Prop 9 | ✓ | ✓ | ✓ |
| 19 | Weak success | Hansson 1997; B&H §6; dissertation §6.3.1 | ✓ | ✗ (304 fail) | ✗ (69 fail) |
| 20 | Very weak success | B&H Prop 10; dissertation §6.3.1 | ✓ | ✗ (180 fail) | ✗ (32 fail) |
| 21 | Negation invariance | B&H §6 (equivalent form of Very weak success) | ✓ | ✗ (180 fail) | ✗ (32 fail) |
| 22 | Feeble success | B&H Prop 11; dissertation §6.3.1 | ✓ | ✓ | ✓ |
| 23 | Non-manipulability | B&H Prop 14; dissertation §6.5.3 | ✓ (vacuous) | ✗ (869 fail) | ✗ (150 fail) |
| 24 | Weak non-manipulability | B&H Prop 15 | ✓ (vacuous) | ✓ | ✓ |

✓ every operator in the family satisfies it · ✗ (n fail) n operators have a counterexample · (vacuous) the premise never arises

#### Properties of the transformation f

| # | Property | Kind | identity (1) | TrustExpansion (15) | ForgetTransform (4) |
|---|---|---|---|---|---|
| f1 | Falsity preservation | Kuratowski | ✓ | ✓ | ✓ |
| f2 | Implication | Kuratowski | ✓ | ✓ | ✓ |
| f3 | Idempotence | Kuratowski | ✓ | ✓ | ✓ |
| f4 | Extensionality | Kuratowski | ✓ | ✓ | ✓ |
| f5 | Disjunctive distribution | Kuratowski | ✓ | ✓ | ✓ |
| f6 | Monotonicity | derived | ✓ | ✓ | ✓ |
| f7 | Pawlak | partition-induced | ✓ | ✓ | ✓ |
| f8 | Conjunctive weakening | partition-induced | ✓ | ✓ | ✓ |
| f9 | Trust symmetry | partition-induced | ✓ | ✓ | ✓ |

#### Relationships between postulates

| # | Relationship | Source | Operators violating it |
|---|---|---|---:|
| r1 | Negation invariance ⇔ Very weak success | B&H §6 | 0 |
| r2 | Feeble success ∧ Non-manipulability ⇒ Very weak success | B&H Prop 13 | 0 |
| r3 | Success ⇒ Weak success ⇒ Very weak success | by definition | 0 |

#### Instance claims

| # | Claim | Source | Result | Detail |
|---|---|---|---|---|
| i1 | No trust ⇒ K ◦ α = K, for every consistent α | dissertation Postulate 1 (§6.3); B&H Prop 1 | ✓ | all 75 orderings, VFR and TSR; at α = ⊥ the result is ∅ (inconsistent), so the postulate needs 'consistent α' |
| i2 | Full trust ⇒ ◦ = ∗ (plain AGM) | dissertation Postulate 2 (§6.3); B&H Prop 2 | ✓ | all 75 orderings × 16 meanings, VFR (U = ∅) and TSR (unit partition) |
| i3 | Non-manipulability holds at both extremes of trust | dissertation §6.5.3; B&H §7 | ✓ | all 75 orderings at U = ∅ and U = {p, q}; it fails in between |
| i4 | VFR ⊆ TSR: Forget(·, U) is the trust expansion of the forgetting partition | dissertation §6.1; B&H Prop 8 (Yao) | ✓ | 10,560 formulas over 2 and 3 variables, every U; induced partition = forgetting partition |
| i5 | VFR is strictly weaker: only 4 of the 15 partitions come from forgetting | dissertation §6.5.4 | ✓ | 4 of 15; unreachable includes the alarm partition {TT, FF} \| {TF, FT} |
| i6 | Alarm example: TSR can weaken 'alarm 1 rang' to 'exactly one rang'; no VFR can | dissertation §6.5.4 (corrected report, see detail) | ✓ | f(p ∧ ¬q) = p ⊕ q under TSR, never under VFR. As written in §6.5.4 (α = p ∨ q) TSR gives {TT, TF, FT, FF} = ⊤, i.e. it ignores the report, because TT shares a cell with FF |
| i7 | Very weak success fails for VFR: K = p ⊕ q, U = {p}, α = ¬(p ∧ ¬q) | dissertation §6.3.1 (with K ⊬ ¬α, not K ⊢ ¬α) | ✓ | a counterexample under all 3 faithful orderings for K = p ⊕ q |
| i8 | Doctor-Necklace: forgetting diam weakens the report to 'sick' (Examples 1-2) | dissertation §5; B&H Examples 1-3 | ✓ | Ex 1: Forget(sick ∧ ¬diam) ≡ sick; Ex 2: ≡ sick over 3 variables; B&H Ex 3 results (1)-(3) reproduced |

#### Negative controls (each must be reported as failing its target)

| # | Claim | Source | Result | Detail |
|---|---|---|---|---|
| c1 | B&H Example 5: Kuratowski but not Pawlak ⇒ fails Disjoint outcome basis and Feeble success | B&H Props 7, 12 | ✓ | f fails Conjunctive weakening, Pawlak, Trust symmetry; ◦ fails Disjoint outcome basis and Feeble success |
| c2 | A non-monotone f breaks Weak non-manipulability | B&H §7 (after Prop 15) | ✓ | K ◦ p = {FF} ⊬ p, but K ◦ (p ∨ q) = {TF} ⊢ p |
| c3 | Dead battery: TSR fails Very weak success but keeps Feeble success | B&H Example 4, Props 10-11 | ✓ | K ◦ ¬p = Cn(¬p ∧ q), K ◦ p = Cn(q), K ◦ (p ∧ q) = Cn(p ∧ q), as in the paper |
| c4 | A syntax-dependent operator is caught by Extensionality | AGM K\*6; dissertation §6.2 | ✓ | both the postulate (#6) and the f-property (f4) report it |

**All verdicts match AGM, Booth & Hunter (2018) and the dissertation.**

_Generated by `uv run check-postulates --update-readme`. Do not edit by hand._
<!-- verdicts:end -->


## Findings

Running the dissertation's claims through the checker found five places where the text should change:

1. **Postulate 1 (§6.3), like B&H Proposition 1, needs a consistent α.** Forget(⊥) = ⊥, so revising by ⊥ gives the inconsistent belief set, not K.
2. **§6.3.1 justifies Proxy success by citing Feeble success.** It follows from Fermé & Hansson (B&H Proposition 3). Feeble success also needs the Pawlak property, not just the Kuratowski properties (control c1).
3. **The §6.3.1 Very weak success counterexample says K ⊢ ¬α.** It should say K ⊬ ¬α. With that fixed it is a counterexample under all three orderings that fit (claim i7).
4. **The conclusion says VFR satisfies every AGM postulate except Success and Vacuity.** It also fails Superexpansion and Subexpansion. Any operator that satisfies Consistency but not Success must fail Superexpansion.
5. **The §6.5.4 alarm example doesn't work as written.** For the report "an alarm went off" (p ∨ q), the proposed partition puts TT in the same cell as FF, so TSR ignores the report entirely. With "alarm 1 rang" (p ∧ ¬q) the example works: TSR concludes "exactly one rang", which no choice of forgotten variables can produce (claim i6).

The checker also confirmed two smaller points:
- Weak non-manipulability holds vacuously for AGM, as Non-manipulability does.
- With only one variable, TSR and VFR cannot be manipulated at all. A source must be trusted on one thing and not another, which needs two variables.


## Project layout

```
src/forgetting_revision/
  syntax.py               formulas as immutable trees, with ~ & | >> and .iff
  semantics.py            signatures, states, models, and states back to formulas (DNF/CNF)
  transform.py            substitution and simplification
  forget.py               Boole's forgetting: Forget(α, p) = α[p/⊤] ∨ α[p/⊥]
  agm_revision.py         AGM revision from a ranking of states
  trust.py                Booth & Hunter's state partitions and trust expansion
  selective_revision.py   K ◦ α = K ∗ f(α): VFR, TSR, plain AGM, or any tabulated f
  families.py             every ordering, partition and untrusted set; every operator
  postulates.py           the 24 postulates and the outcome table they run on
  transform_properties.py the 9 properties of f, and Yao's theorem
  claims.py               specific claims and counterexamples from the papers
  checker.py              the runner, the report and `check-postulates`
src/tests/                pytest suite
```


## Limits

- An exhaustive check over two variables is a proof for two variables only. The general proofs are Booth & Hunter's and the dissertation's; the checker confirms them and finds counterexamples.
- Three variables are covered for the transformation properties and claim i4. The full operator families there (545,835 orderings × 4,140 partitions) would need sampling, which is planned.
- The inconsistent belief set K = Cn(⊥) is out of scope, because a ranking of states always has a non-empty most-plausible tier.


## References

- C. E. Alchourrón, P. Gärdenfors and D. Makinson. On the logic of theory change. *Journal of Symbolic Logic* 50(2), 1985.
- E. L. Fermé and S. O. Hansson. Selective revision. *Studia Logica* 63(3), 1999.
- R. Booth and A. Hunter. Trust as a precursor to belief revision. *Journal of Artificial Intelligence Research* 61, 2018.
- Kiran CJ. *Forgotten Truths: Exploring Variable Forgetting in Belief Revision.* MSc dissertation, Cardiff University, 2026.


## License

MIT. See [LICENSE](LICENSE).
