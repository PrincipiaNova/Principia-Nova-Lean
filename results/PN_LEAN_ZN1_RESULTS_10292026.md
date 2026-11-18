# Results record: Z-N.1 drift law, Tier 1 (algebra)

*Appendix Z §24, Z-N.1 (the particle stage of the Noether variation)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZN1_PROOF_10292026.lean` |
| Library | Lean 4 core only (no mathlib) |
| Certified statements | 3 theorems |
| `sorry` | none |
| Axiom audit | 3 on `propext` alone. Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The algebra of the drift law, in an arbitrary commutative algebra with a derivation ∂ standing for d/dt. The ring laws and the derivation laws (additivity and the Leibniz rule) are fields of a structure stated in the file; nothing else is available to the proofs. To avoid division the energy is carried in denominator-cleared form, F = v² + 2n²V, which is 2N·E for the lapse Lagrangian L = q̇²/(2N) − N·V(q). Here v is the velocity, n the lapse (clock rate), V the potential along the trajectory and V′ its derivative.

## Theorems

- `drift_law`: n·∂F = 2·(∂n)·F. This is the denominator-cleared form of dE/dt = (Ṅ/N)·E. Read as the vanishing numerator of ∂(F/n²), the same identity says the energy measured in the substrate's own clock is conserved. *Named assumptions: the chain rule ∂V = V′·v; the Euler–Lagrange equation in cleared form, n·∂v + n³·V′ = v·∂n.* *(audits to `propext` alone)*
- `flat_clock`: if ∂n = 0 then n·∂F = 0. Where the clock is flat, conservation is exact. *Named assumptions: as for `drift_law`.* *(audits to `propext` alone)*
- `arena_law`: given the differentiated arena law (∂n)·C + n·Ċ = 0, it follows that n·(C·∂F + 2·Ċ·F) = 0. This is the cleared form of dE/dt = [(D_loss − G)/C]·E once Ċ is read as G − D_loss. *Named assumptions: as for `drift_law`, plus the differentiated arena law. In the statement Ċ is a free element; reading it as G − D_loss is the book's Generative Law, not something this theorem proves.* *(audits to `propext` alone)*

## Not certified

- That d/dt on real functions is a derivation of this kind. Tier 2 restates the result for real functions with real derivatives.
- The Euler–Lagrange equation itself, which is a hypothesis here. Tier 3 derives it from the action principle.
- Any numeric result. Numeric checks remain the symbolic and numeric record described in Appendix Z-N.

## Notes

- The file also defines a small model of the structure (the integers with the zero derivation), which shows the stated laws can be satisfied together.
