# Errata

Corrections to *Forgotten Truths: Exploring Variable Forgetting in Belief Revision* (Kiran C. James, MSc dissertation, Cardiff University, 2026), found by running the dissertation's claims through this repository's postulate checker (`uv run check-postulates`). The dissertation in this folder is kept exactly as submitted.

1. **§6.3, Postulate 1** ("if the source is not trusted in any domain, K ◦ α = K for any α") needs **consistent** α. Forget(⊥, T_B) = ⊥, so revising by ⊥ gives the inconsistent belief set, not K. The same applies to Booth & Hunter's Proposition 1. *(Claim i1.)*

2. **§6.3.1, Proxy success** is justified by citing Feeble success. It follows instead from Fermé & Hansson's result for Kuratowski transformation functions (Booth & Hunter, Proposition 3). Feeble success itself needs the Pawlak property, not just the Kuratowski properties (Booth & Hunter, Proposition 12). *(Control c1.)*

3. **§6.3.1, Very weak success counterexample:** "we have K ⊢ ¬α" should read **K ⊬ ¬α**, which is the postulate's premise. With K = Cn((¬p ∧ q) ∨ (p ∧ ¬q)) and α = ¬(p ∧ ¬q), K does not entail ¬α. With this fixed, the counterexample holds under all three plausibility orderings that fit K. *(Claim i7.)*

4. **§7, Conclusion:** VFR satisfies "all the classic AGM properties other than Success and Vacuity" holds for the six basic AGM postulates, but VFR also fails the supplementary postulates **Superexpansion and Subexpansion** introduced in §3.1. Any operator that satisfies Consistency but not Success must fail Superexpansion. *(Verdict matrix, postulates 7 and 8.)*

5. **§6.5.4, alarm example:** with the report α = p ∨ q and the partition {TT, FF} | {TF, FT}, the state TT shares a cell with FF, so the trust expansion of p ∨ q is ⊤ and TSR **ignores** the report. The example works with a report that names an alarm, α = p ∧ ¬q ("alarm 1 rang"): TSR then concludes p ⊕ q ("exactly one rang"), which no choice of forgotten variables produces. The finer partition {TT} | {TF, FT} | {FF} ("the officer can tell how many alarms rang, but not which") also accepts p ∨ q as it is. *(Claims i5 and i6.)*