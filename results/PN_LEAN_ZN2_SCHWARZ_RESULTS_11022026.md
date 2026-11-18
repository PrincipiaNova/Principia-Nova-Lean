# Results record: Z-N.2 mixed partial, derived from smoothness

*Appendix Z §24, Z-N.2*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZN2_SCHWARZ_PROOF_11022026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 1 theorem |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Z-N.2 Tier 2 takes the equality of mixed partials as named data. This file shows that data follows from smoothness, using mathlib's symmetry of second derivatives.

## Theorems

- `schwarz_curried`: for a field φ(t, x) with partial derivatives p_t and p_x, there is a single value m that is both the t-derivative of p_x and the x-derivative of p_t at the given point. *Named assumptions: φ, as a function on the plane, is twice continuously differentiable; p_t and p_x are its partial derivatives everywhere.*

## Not certified

- Nothing about the field equation or the continuity law. This file supplies one regularity fact; the Tier 2 theorems themselves are stated with the mixed-partial data as a hypothesis.
