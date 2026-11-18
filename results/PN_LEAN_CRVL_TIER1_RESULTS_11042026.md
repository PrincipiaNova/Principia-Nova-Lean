# Results record: Coherence-Relative Velocity Law, Tier 1

*Chapter 9 §4 (the Observer-Compliant Form)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_CRVL_TIER1_PROOF_11042026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 10 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The algebra of the conversion factor between two regions' clocks. Objects: a ceiling c_max; a tempo function g of coherence density; the local limit c_loc(C) = c_max·g(C); and the conversion factor k(C_X, C_Y) = g(C_X)/g(C_Y). The book's conditions on g enter as hypotheses: 0 < g < 1, and g decreasing. A speed is written as a fraction α of the local limit.

## Theorems

**Bounds and the algebra of k**

- `mu_pair`: 0 < c_loc(C) < c_max for every C. *Named assumptions: c_max > 0; 0 < g < 1.*
- `k_self`: k(C, C) = 1. *Named assumptions: g > 0.*
- `k_inv`: k(C_X, C_Y)·k(C_Y, C_X) = 1. *Named assumptions: g > 0.*
- `k_cocycle`: k(C_X, C_Z) = k(C_X, C_Y)·k(C_Y, C_Z). Conversion factors compose by multiplication, with no dependence on the intermediate region. *Named assumptions: g > 0.*

**Order**

- `k_gt_one_of_antitone`: if g is decreasing (not necessarily strictly) and k(C_X, C_Y) > 1, then C_X < C_Y. One direction only. *Named assumptions: g > 0; g antitone.*
- `k_order_iff`: if g is strictly decreasing, k(C_X, C_Y) > 1 exactly when C_X < C_Y. *Named assumptions: g > 0; g strictly antitone.*

**Readings**

- `earth_reading`: α·(k(C_X, C_E)·c_loc(C_E)) = α·c_loc(C_X). The reading taken from one region is the local motion in the other, converted. *Named assumptions: g > 0.*
- `sr_ceiling_at_k1`: at k = 1, for 0 ≤ α < 1: α·k·c_E < c_E and 2·α·k·c_E < 2·c_E. The ceilings of special relativity hold where the conversion factor is 1. *Named assumptions: c_E > 0; 0 ≤ α < 1; k = 1.*
- `falsifier_iff`: 2·c_E < 2·α·k·c_E exactly when 1 < α·k. *Named assumptions: c_E > 0.*
- `discriminating_case`: the book's printed example checks out as arithmetic: 0.8 < 1, 1 < 0.8 × 1.5, and 2 × 0.8 × 1.5 × c_E = 2.4·c_E.

## Not certified

- That the conversion factor depends only on the two endpoint densities. That is how k is defined in the file; it is an assumption of the construction (the book's locality clause), not a theorem.
- Lorentz boost composition. `sr_ceiling_at_k1` recovers coordinate ceilings only.
- Light itself (α = 1), which is outside this file by design.
- Whether any region of nature realizes α·k > 1. That is an observational question.
