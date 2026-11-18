# Results record: Noether stage 1, Tier 3: from the action principle to the drift law

*Appendix Z-N.1*

| | |
|---|---|
| Proof file | `physlean/PN_LEAN_ZN1_TIER3_PROOF_11022026.lean` |
| Library | Lean 4 (v4.35.0) + mathlib + PhysLean |
| Certified statements | 6 theorems (the file also repeats the Tier 3a construction) |
| `sorry` | none |
| Axiom audit | Every audited statement rests on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing else, as recorded at certification. |
| Build status | Certified on its recorded toolchain; outside the repository's CI build until the PhysLean workspace pin is recorded. |

## Scope

The lower tiers took the Euler–Lagrange equation as a hypothesis. Here it is derived from the action principle, using PhysLean's proved theorem that a field is a critical point of the action exactly when it satisfies the Euler–Lagrange equations. The Lagrangian is L = q̇²/(2N) − N·V(q) and the energy is E = v²/(2N) + N·V(q), with v the velocity and a the acceleration.

## Theorems

- `satisfiesEL_iff_cleared`: PhysLean's Euler–Lagrange condition for this Lagrangian holds exactly when N·a = v·Ṅ − N³·V′(q) at every time. This is the equation the lower tiers assumed. *Named assumptions: N > 0; q, v, N and V differentiable with the named derivatives.*
- `drift_law_at`: from that equation at a time t, the energy has derivative (Ṅ/N)·E at t. This is the Tier 2 drift law, repeated in this workspace; its statement is not new. *Named assumptions: N > 0; the named derivatives; the equation at t.*
- `action_critical_iff_el`: the trajectory is a critical point of the action exactly when N·a = v·Ṅ − N³·V′(q) at every time. *Named assumptions: as above, plus PhysLean's regularity conditions: the field is smooth, the Lagrangian is smooth in jet coordinates, and the action is finite.*
- `action_critical_drift_law`: if the trajectory is a critical point of the action, then dE/dt = (Ṅ/N)·E at every time. *Named assumptions: the same assumptions as `action_critical_iff_el`.*
- `lapse_smoothInCoordinates`: if N and V′ are smooth, the Lagrangian is smooth in jet coordinates. One of the regularity conditions above is thereby proved rather than assumed. *Named assumptions: N > 0; V differentiable; N and V′ smooth.*
- `action_critical_drift_law_canon`: with N = C_floor/C and Ċ = G − D_loss substituted, a critical point of the action satisfies dE/dt = ((D_loss − G)/C)·E. *Named assumptions: C > 0; C_floor > 0; C has derivative G − D_loss; N and Ṅ given by the stated formulas; and the assumptions of `action_critical_drift_law`.*

## Also audited in this file (not counted)

- `lapseLagrangian`: the construction of the Tier 3a file, repeated here; counted there.
- `sum_derivIndex11`: the helper lemma of the Tier 3a file, repeated here.

## Not certified

- The tempo law N = C_floor/C and the Generative Law Ċ = G − D_loss. In the last theorem they are substitutions made by hypothesis, not results.
- Finite action and smoothness of the field, which are assumed. PhysLean's theorem needs them.
- The correctness of PhysLean's variational theorem beyond the fact that it compiles in the recorded workspace. It is used as the library provides it.

## Notes

- `drift_law_at` and `action_critical_iff_el` have no axiom line of their own in the file. `action_critical_drift_law` is proved directly from both, and its axiom line therefore covers them.
