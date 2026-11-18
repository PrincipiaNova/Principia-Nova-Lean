# Results record: The exponential bias, Tier 2 (martingale form)

*Chapter 4 (the Local Improvement Tendency)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_DOOB_TIER2_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 6 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The same tendency in probability-theoretic form: a discrete-time real process C_n on a probability space with a filtration. The Local Improvement Tendency enters as a hypothesis in conditional form, and mathlib's Doob decomposition is applied to it.

## Theorems

- `submartingale_of_improvement_tendency`: if the conditional expectation of C_j − C_i given the information at time i is nonnegative for all i ≤ j, then C is a submartingale. *Named assumptions: C adapted and integrable; a sigma-finite filtration; the conditional improvement tendency.*
- `doob_split`: C equals its martingale part plus its predictable part.
- `fluctuation_is_fair`: the martingale part is a martingale. *Named assumptions: C adapted and integrable; a sigma-finite filtration.*
- `compensator_monotone`: for a submartingale, the predictable part is almost surely nondecreasing in time. *Named assumptions: C a submartingale.*
- `compensator_nonneg`: for a submartingale, the predictable part is almost surely ≥ 0 at every time. *Named assumptions: C a submartingale.*
- `doob_tower`: the five conclusions above together, from the regularity conditions and the conditional improvement tendency. *Named assumptions: as for `submartingale_of_improvement_tendency`.*

## Not certified

- The improvement tendency itself at this level of generality. It is a hypothesis here; Tier 1 proves it only in its finite model.
- A construction linking Tier 1's finite model to a process of this kind.
- Any identification of the predictable part with the entropy ledger of Chapter 7. The two have the same monotone shape; no theorem connects them.
