# Variable Forgetting Revision

A Python implementation of **Variable Forgetting Revision (VFR)**, a trust-based belief revision operator I defined in my MSc dissertation at Cardiff University, *Forgotten Truths: Exploring Variable Forgetting in Belief Revision* (supervised by Richard Booth).

The goal is to turn the dissertation's pen-and-paper results into code that checks them **exhaustively** on small signatures, rather than through a handful of worked examples.

> **Status:**   work in progress


## The idea in one example

A doctor says to the patient: *"You have a viral infection, and the jewel on your necklace is not a diamond."*

The patient naturally accepts the diagnosis but rejects(forgets) the claim on the jewellery, because the doctor is considered to be an expert in the medical field but not on gemstones and jewellery. Classical (AGM) belief revision can't do this, since it must accept the whole input.

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