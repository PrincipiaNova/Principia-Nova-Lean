# Results record: Z-N.2 sourced continuity and irremovability, Tier 1 (algebra)

*Appendix Z §24, Z-N.2 (the field stage of the Noether variation)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZN2_TIER1_PROOF_11022026.lean` |
| Library | Lean 4 core only (no mathlib) |
| Certified statements | 4 theorems |
| `sorry` | none |
| Axiom audit | 2 on no axioms; 2 on `propext` alone. Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The algebra of the 1+1 field stage, in a commutative algebra with two derivations ∂t and ∂x, each additive and Leibniz. The model is L = φ_t²/(2N) − N·φ_x²/2 − N·V(φ) with a position-dependent lapse. Cleared quantities, with no division: R = p_t² + n²·p_x² + 2n²·V (which is 2N·ρ_E) and g = n·p_x·p_t (the energy flux with its sign moved).

## Theorems

- `sourced_continuity`: n·∂tR = 2·(∂t n)·R + 2n²·∂x g. This is the cleared form of ∂tρ_E + ∂x f = (∂t N)·ρ_E/N: the flux term is untouched and the source is proportional to the time variation of the clock. *Named assumptions: the time chain rule ∂tV = V′·p_t; equality of mixed partials, ∂t p_x = ∂x p_t; the field Euler–Lagrange equation in cleared form.* *(audits to `propext` alone)*
- `arena_obstruction`: if n·c = k and ∂x k = 0, then (∂x n)·c + n·(∂x c) = 0. *(audits to no axioms)*
- `obstruction_iff`: under the same arena-law condition, ∂x n = 0 exactly when ∂x c = 0. The clock can be flattened in space exactly where the spatial gradient of c vanishes. *Named assumptions: n and c are cancellable (multiplying by either sends only zero to zero), the ring form of "clock rate and coherence are nonzero".* *(audits to no axioms)*
- `flat_patch`: if ∂t n = 0 then n·∂tR = 2n²·∂x g. Where the clock is steady in time, the continuity law is pure flux exchange. *Named assumptions: as for `sourced_continuity`.* *(audits to `propext` alone)*

## Not certified

- The real-function version of these statements (Tier 2) and the derivation of the field equation from the action (Tier 3).
- The reading of c as coherence and of its spatial gradient as gravity. That identification is made in Chapter 5 of the book; the theorem is about n and c only.
- The FRW numeric gate, which remains the symbolic and numeric record.
