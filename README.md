# Variable Forgetting Revision

A Python implementation of **Variable Forgetting Revision (VFR)**, a trust-based belief revision operator I defined in my MSc dissertation at Cardiff University, *Forgotten Truths: Exploring Variable Forgetting in Belief Revision* (supervised by Richard Booth).

The goal is to turn the dissertation's pen-and-paper results into code that checks them **exhaustively** on small signatures, rather than through a handful of worked examples.

The package checks 24 postulates from AGM revision and from Booth & Hunter's Trust as a Precursor to Belief Revision (2018) against every possible configuration of AGM, Trust-Sensitive (TSR) and Variable Forgetting (VFR) revision over two variables. That means each plausibility ordering paired with each trust setting: 1,500 configurations, giving 489 distinct behaviours. It also checks 9 properties of the transformation functions, and 13 specific claims and counterexamples from the two papers. All of them match the literature.

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


## What is being checked: 1,500 configurations
 
AGM revision, TSR and VFR are three **methods** of revising beliefs. None of them is a single concrete rule until its settings are fixed. A **configuration** is one concrete instance of a method, and it has these settings:
 
1. **A plausibility ordering** over the states: which situations the agent finds more or less likely. Its most plausible tier is the agent's current belief set, Mod(K). Revising picks the most plausible states that fit what is accepted from the report.
2. **A trust setting:** what the agent believes the source can tell apart. For TSR this is a state partition, and for VFR a set U of variables the source is not trusted on. Plain AGM revision has no trust setting, because the source is believed outright.
Booth & Hunter call each such instance "an operator", as in "there exists an AGM revision operator ∗ and a state partition Π such that…". This README says *configuration* instead, so that "the TSR operator" can keep meaning the method.
 
With two variables, p and q, there are four states (TT, TF, FT, FF), and so:
 
| | Settings | How many |
|---|---|---|
| Orderings of 4 states, ties allowed | Fubini number | 75 |
| State partitions of 4 states | Bell number | 15 |
| Untrusted sets U ⊆ {p, q} | 2² | 4 |
| **AGM** configurations | ordering | 75 |
| **TSR** configurations | ordering × partition | 75 × 15 = 1,125 |
| **VFR** configurations | ordering × untrusted set | 75 × 4 = 300 |
 
That is **1,500 configurations**. Not all of them behave differently, though:
 
- An agent that trusts nothing never changes its beliefs, so only the bottom tier of its ordering matters. Orderings that agree on that tier behave identically.
- The methods overlap: every AGM configuration behaves like a VFR one (U = ∅), and every VFR configuration behaves like a TSR one.
Counting what they *do* rather than how they are set up gives **75 AGM ⊂ 144 VFR ⊂ 489 TSR distinct behaviours**, each method strictly inside the next (claim i9). Checking all 1,500 configurations tests each of the 489 behaviours at least once. Repeats simply repeat a verdict, so the results are unaffected.

## How trust is modelled: TSR and VFR
 
Both methods work the same way. First they **widen** the report so that it only says what the source can be trusted on. Then they **revise** by the result with ordinary AGM revision:
 
```
K ◦ α  =  K ∗ f(α)
```
 
The two methods differ only in the widening step f, and in particular in **where the trust information comes from**.
 
### Trust-Sensitive Revision (Booth & Hunter)
 
In Booth & Hunter's framework the agent A has a **trust function** that gives, for each source B and belief set K, a **state partition** Π_B,K. States in the same cell are ones that A does not trust B to tell apart. A report φ from B is replaced by its **trust expansion** Π[φ], the union of every cell that contains a model of φ. A then revises by that: K ∗ᴮ φ is the set of most plausible states in Π[φ].
 
The partition is an **input**. It is part of the agent's set-up, like its plausibility ordering, and it stands for A's judgement of B's expertise. Booth & Hunter do not say how A arrives at it, so any partition is allowed, including ones that do not follow the propositional variables.
 
### Variable Forgetting Revision
 
VFR does not take a partition. It takes the set U of variables the source is **not** trusted on, and forgets them from the report using Boole's syntactic forgetting:
 
```
Forget(α, p)  =  α[p/⊤] ∨ α[p/⊥]
```
 
Forgetting U makes indistinguishable exactly the states that differ only on U. So VFR **generates** a partition, "agree on every trusted variable", where TSR needs one to be given. This answers a question TSR leaves open, namely where the partition comes from. The cost is that forgetting can only produce some partitions: 4 of the 15 over two variables. Therefore, VFR is TSR restricted to those partitions.

## How the checker works

- **Meanings, not formulas.** Over n variables there are infinitely many formulas but only 2^(2^n) meanings (sets of states): 16 for two variables. The checker builds one formula per meaning, asks the real operator to revise by it, and stores the 16 results. Each postulate is then a few set operations on that table.
- **Extensionality makes that sound.** Revising by five different spellings of every meaning must give the same answer. For VFR this tests the syntactic forgetting itself (`substitute`, `simplify`).
- **Every configuration, not a few.** Orderings over states are counted by the Fubini numbers (75 for two variables) and state partitions by the Bell numbers (15). The checker builds every combination of ordering and trust setting, 1,500 configurations in all, covering all 489 distinct behaviours (see "What is being checked" above).
- **Counterexamples, not just verdicts.** A failure names the exact operator and inputs. Each check also counts how often its premise came up, so a pass where the premise never arose is flagged as *vacuous*.
- **Negative controls.** Booth & Hunter's own counterexamples are run through the checker, which must report them as failures. That shows its "✓" verdicts can be trusted.
- **Yao's theorem in code.** `induced_partition(f)` recovers the state partition behind any partition-based transformation. Applied to `Forget(·, U)`, it gives exactly the "agree on the trusted variables" partition, which is the dissertation's main result, VFR ⊆ TSR.


## Results

<!-- verdicts:start -->
Checked exhaustively over 2 variables (p, q): 75 AGM, 1,125 TSR, 300 VFR configurations, i.e. every plausibility ordering paired with every trust setting (claim i9 counts how many distinct behaviours they give).

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

✓ every configuration of the method satisfies it · ✗ (n fail) n configurations have a counterexample · (vacuous) the premise never arises

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

| # | Relationship | Source | Configurations violating it |
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
| i9 | AGM ⊂ VFR ⊂ TSR: 75 ⊂ 144 ⊂ 489 distinct behaviours | dissertation §6.1, §6.5.4; B&H Prop 2 | ✓ | AGM 75 configurations → 75 behaviours, VFR 300 configurations → 144 behaviours, TSR 1,125 configurations → 489 behaviours; each family strictly inside the next, so 1,500 configurations give 489 distinct behaviours |

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

## References

- C. E. Alchourrón, P. Gärdenfors and D. Makinson. On the logic of theory change. *Journal of Symbolic Logic* 50(2), 1985.
- E. L. Fermé and S. O. Hansson. Selective revision. *Studia Logica* 63(3), 1999.
- R. Booth and A. Hunter. Trust as a precursor to belief revision. *Journal of Artificial Intelligence Research* 61, 2018.
- Kiran CJ. *Forgotten Truths: Exploring Variable Forgetting in Belief Revision.* MSc dissertation, Cardiff University, 2026.


## Licence
 
- **Code:** MIT. See [LICENSE](LICENSE).
- **Dissertation** ([`docs/`](docs/)): © 2026 Kiran C. James, licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). You may share and adapt it with credit. See [docs/LICENSE.md](docs/LICENSE.md), and [docs/ERRATA.md](docs/ERRATA.md) for corrections found by the checker.