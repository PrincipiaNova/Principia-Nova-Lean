# Results record: Z-N.2 sourced continuity and irremovability, Tier 2 (analysis)

*Appendix Z §24, Z-N.2*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZN2_TIER2_PROOF_11022026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 6 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The field-stage claims for real functions of two variables (t, x). Every partial derivative is mathlib's `HasDerivAt` in the corresponding slot, and division is real division licensed by N > 0. Energy density: ρ_E = p_t²/(2n) + n·(p_x²/2 + V(φ)). Flux: f = −n·p_x·p_t. The mixed partial m is carried as two-sided named data: one function assumed to be both ∂t p_x and ∂x p_t.

## Theorems

- `energy_time_deriv`: ∂tρ_E = (∂t n/n)·ρ_E + (n_x·p_x·p_t + n·b_x·p_t + n·p_x·m), where b_x = ∂x p_x. *Named assumptions: N > 0; the time derivatives of φ, p_t, p_x and n; V has derivative V′; the field Euler–Lagrange equation in cleared form.*
- `flux_space_deriv`: ∂x f = −(n_x·p_x·p_t + n·b_x·p_t + n·p_x·m). *Named assumptions: the x-derivatives of p_t, p_x and n.*
- `sourced_continuity`: any values certified as ∂tρ_E and ∂x f satisfy ∂tρ_E + ∂x f = (∂t n/n)·ρ_E. The flux is intact and the source is the time variation of the clock. *Named assumptions: all of the above together.*
- `arena_obstruction_x`: if n·c is constant in x, then n_x·c + n·c_x = 0. *Named assumptions: the x-derivatives of n and c.*
- `obstruction_iff`: under the same condition, n_x = 0 exactly when c_x = 0. *Named assumptions: N > 0 and C > 0; the x-derivatives of n and c.*
- `flat_patch`: if ∂t n = 0 at the point, then ∂tρ_E + ∂x f = 0. *Named assumptions: as for `sourced_continuity`.*

## Not certified

- The field Euler–Lagrange equation and the mixed-partial data, both hypotheses here. The mixed-partial data is derived from smoothness in the Schwarz file; the field equation is derived from the action in Tier 3.
- The reading of c as coherence and of its gradient as gravity (Chapter 5 of the book).
- The FRW numeric gate.
