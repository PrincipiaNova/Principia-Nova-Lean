# Results record: Winding numbers, Tier 1

*Chapter 8 §6 and Chapter 20 §8*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_WINDING_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 7 theorems |
| `sorry` | none |
| Axiom audit | 2 on `propext` alone; 5 on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Winding numbers in terms of phase data. A loop is represented by its phase θ, and the winding number is the total phase change divided by 2π. In this tier the phase function is given; Tier 2 proves it always exists.

## Theorems

- `winding_integer`: if the phase returns to where it started, in the sense e^(iθ₁) = e^(iθ₀), then θ₁ − θ₀ = 2π·k for an integer k, so the winding number is an integer. *Named assumptions: the closing condition.*
- `winding_via_integral`: (1/2π)·∫₀¹ θ′(t) dt = (θ(1) − θ(0))/2π. The book's loop-integral formula equals the endpoint difference. *Named assumptions: θ differentiable with continuous derivative.*
- `no_gradual_unwinding`: a continuous real function that takes integer values everywhere is constant. A winding number cannot change under a continuous deformation. *Named assumptions: continuity of the family; integer values.*
- `tear_quantum`: two different integers differ by at least 1. *(audits to `propext` alone)*
- `trivial_loop`: a constant phase has winding number 0. *Named assumptions: the phase is constant.*
- `pair_creation_blind_spot`: 0 + 0 = 1 + (−1), while 1 ≠ 0 and −1 ≠ 0. A total can stay unchanged while the individual winding numbers change. *(audits to `propext` alone)*
- `discrete_jump_witness`: there is an integer-valued family with different values at 0 and 1, and it is not continuous. A change in winding number requires a discontinuity.

## Not certified

- The physical reading of the phase as the book's coherence phase field.
- That real deformations are continuous. Chapter 20 notes that thermal fluctuations are not; continuity is a hypothesis of `no_gradual_unwinding`.
- The classification of loops up to deformation (the fundamental group of the circle). The book does not claim it and neither does this file.
