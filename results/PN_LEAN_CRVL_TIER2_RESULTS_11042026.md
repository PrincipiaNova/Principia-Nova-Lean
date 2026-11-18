# Results record: Coherence-Relative Velocity Law, Tier 2 (the cone-slope bridge)

*Appendix Z-G.4 and Chapter 9 §4*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_CRVL_TIER2_PROOF_11042026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 7 new theorems (the file also repeats the 10 of Tier 1) |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Connects the light-cone slope of the Z-G.1 line element, −τ²dt² + τ⁻²dx², to Chapter 9's conversion factor. The file defines the null slope as τ² and the gravitational tempo function as g_grav = τ².

## Theorems

- `nullSlope_isNull`: the slope s = τ² is null: −τ² + τ⁻²·s² = 0. *Named assumptions: τ > 0.*
- `nullSlope_unique`: any slope s ≥ 0 satisfying the null condition equals τ². *Named assumptions: τ > 0; s ≥ 0.*
- `proper_speed_one`: measured with local rulers (dx/τ) and local clocks (τ·dt), the null ray's speed is 1. *Named assumptions: τ > 0; dt ≠ 0.*
- `slope_ratio_is_kfac`: the ratio of null slopes in two regions equals the conversion factor k computed from g_grav. This holds by the definitions.
- `sector_instantiation`: g_grav satisfies the conditions Tier 1 places on a tempo function: it is positive, below 1, and strictly decreasing. So every Tier 1 theorem applies to it. *Named assumptions: 0 < τ² < 1; τ > 0; τ strictly antitone.*
- `sector_order_iff`: for g_grav, k(C_X, C_Y) > 1 exactly when C_X < C_Y. *Named assumptions: as for `sector_instantiation`.*
- `cone_breathes`: if C_X < C_Y then the null slope at C_Y is smaller than at C_X. Higher coherence density, slower cone. *Named assumptions: τ > 0; τ strictly antitone.*

## Also audited in this file (not counted)

- `mu_pair`: repeated unchanged from the Tier 1 file; counted there.
- `k_self`: repeated unchanged from the Tier 1 file; counted there.
- `k_inv`: repeated unchanged from the Tier 1 file; counted there.
- `k_cocycle`: repeated unchanged from the Tier 1 file; counted there.
- `k_gt_one_of_antitone`: repeated unchanged from the Tier 1 file; counted there.
- `k_order_iff`: repeated unchanged from the Tier 1 file; counted there.
- `earth_reading`: repeated unchanged from the Tier 1 file; counted there.
- `sr_ceiling_at_k1`: repeated unchanged from the Tier 1 file; counted there.
- `falsifier_iff`: repeated unchanged from the Tier 1 file; counted there.
- `discriminating_case`: repeated unchanged from the Tier 1 file; counted there.

## Not certified

- That the gravitational clock factor and Chapter 9's tempo function are the same physical object. The file sets g_grav = τ² by definition; that the two printed objects coincide is the book's claim.
- The bounds and monotonicity of τ, which are hypotheses here.
- Light-deflection integrals and other numeric tests, which remain the symbolic and numeric record.
