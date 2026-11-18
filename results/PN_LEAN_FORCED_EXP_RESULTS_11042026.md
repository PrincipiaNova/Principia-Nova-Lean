# Results record: The forced exponential

*Appendix Z-G.5 §A (and Z-G.2)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_FORCED_EXP_PROOF_11042026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 4 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

If sources add and tempo responds multiplicatively, the tempo map must be an exponential. In the statements f is the tempo map as a function of the potential.

## Theorems

- `zero_calibrated`: f(0) = 1. *Named assumptions: f(x + y) = f(x)·f(y) for all x, y; f > 0.*
- `forced_exponential`: f(x) = exp(log f(1)·x) for every x. The form and its constant are determined. *Named assumptions: f(x + y) = f(x)·f(y); f > 0; f continuous.*
- `mu_guarantee`: exp(k·x) > 0 for all k and x. The forced form is never zero.
- `exp_satisfies`: the converse: exp(k·(x + y)) = exp(k·x)·exp(k·y).

## Not certified

- That nature's tempo map satisfies the multiplicative equation. It is a hypothesis here.
- Continuity, which is a named hypothesis. Without it the functional equation has other solutions.
