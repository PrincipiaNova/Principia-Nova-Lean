# Results record: Noether stage 1, Tier 3a: the lapse Lagrangian in PhysLean

*Appendix Z-N.1*

| | |
|---|---|
| Proof file | `physlean/PN_LEAN_ZN1_TIER3A_PROOF_11022026.lean` |
| Library | Lean 4 (v4.35.0) + mathlib + PhysLean |
| Certified statements | 1 certified construction (no counted theorems) |
| `sorry` | none |
| Axiom audit | Every audited statement rests on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing else, as recorded at certification. |
| Build status | Certified on its recorded toolchain; outside the repository's CI build until the PhysLean workspace pin is recorded. |

## Scope

A construction, not a theorem. The Lagrangian L(t, q, q̇) = q̇²/(2N(t)) − N(t)·V(q) is built as an object of PhysLean's local field theory with one base coordinate (time), one field and first-order jets. PhysLean requires each Lagrangian to come with a proof that its declared partial derivatives are the true ones; that proof is supplied here. The whole of this file is repeated at the start of the Tier 3 file.

## Certified construction

- `lapseLagrangian`: the lapse Lagrangian as a PhysLean `Lagrangian 1 1 1`, with ∂L/∂q = −N·V′(q) and ∂L/∂q̇ = q̇/N proved to be its fiber derivatives. Named assumptions: N(t) > 0 for all t; V differentiable with derivative V′.

## Also audited in this file (not counted)

- `sum_derivIndex11`: a helper lemma: a sum over the two derivative indices (position and velocity) has exactly two terms.

## Not certified

- Any statement about solutions or about the action. Those are in the Tier 3 file.
- That N is the book's clock rate. Here N is any positive function of time.
