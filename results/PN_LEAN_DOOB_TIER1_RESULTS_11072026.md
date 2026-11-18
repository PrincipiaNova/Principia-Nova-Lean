# Results record: The exponential bias, Tier 1 (finite model)

*Chapter 4 (the transition bias and the Local Improvement Tendency)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_DOOB_TIER1_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 6 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

A finite model of Chapter 4's biased step. Proposals come in ± pairs: each magnitude μ ≥ 0 is proposed uphill (+μ) and downhill (−μ) with a common weight w(μ) ≥ 0, and each move is reweighted by exp(β·Δ). The expected-step numerator is Σ w(μ)·(μ·e^(βμ) − μ·e^(−βμ)) and the normalizer is Σ w(μ)·(e^(βμ) + e^(−βμ)).

## Theorems

- `favored_vs_suppressed`: for β ≥ 0, μ ≥ 0 and w ≥ 0: w·e^(−βμ) ≤ w·e^(βμ). The uphill move carries at least the downhill move's weight. *Named assumptions: β ≥ 0; μ ≥ 0; w ≥ 0.*
- `expected_step_nonneg`: the expected-step numerator is ≥ 0. *Named assumptions: β ≥ 0; weights ≥ 0; magnitudes ≥ 0.*
- `zero_selectivity_neutral`: at β = 0 the numerator is exactly 0.
- `expected_step_pos`: for β > 0, if some proposal has μ₀ > 0 and w(μ₀) > 0, the numerator is strictly positive. *Named assumptions: β > 0; weights and magnitudes ≥ 0; one genuinely uphill proposal with positive weight.*
- `partition_pos`: if some proposal has positive weight, the normalizer is positive. *Named assumptions: weights ≥ 0; one proposal with positive weight.*
- `normalized_step_nonneg`: the normalized expected step (numerator divided by normalizer) is ≥ 0. *Named assumptions: β ≥ 0; weights and magnitudes ≥ 0; one proposal with positive weight.*

## Not certified

- That nature's proposals are symmetric. The ± pairing is the shape of the model.
- Continuous time, and any quality measure other than the one summed here.
- A guarantee for any single step. These are statements about the expectation.
