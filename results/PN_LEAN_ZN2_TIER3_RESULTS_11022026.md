# Results record: Noether stage 2, Tier 3: the field action principle

*Appendix Z-N.2*

| | |
|---|---|
| Proof file | `physlean/PN_LEAN_ZN2_TIER3_PROOF_11022026.lean` |
| Library | Lean 4 (v4.35.0) + mathlib + PhysLean |
| Certified statements | 10 theorems and 1 certified construction |
| `sorry` | none |
| Axiom audit | Every audited statement rests on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing else, as recorded at certification. |
| Build status | Certified on its recorded toolchain; outside the repository's CI build until the PhysLean workspace pin is recorded. |

## Scope

The field version of the stage 1 result, on the (t, x) plane. The Lagrangian is L = u_t²/(2N) − N·u_x²/2 − N·V(u), where the clock field N(t, x) may depend on both coordinates. The energy density is ρ = u_t²/(2N) + N·(u_x²/2 + V(u)) and the flux is f = −N·u_x·u_t. The field equation, called here the cleared field equation, is N·u_tt + N³·V′(u) = u_t·N_t + N²·N_x·u_x + N³·u_xx.

## Theorems

**From the action to the field equation**

- `satisfiesEL_iff_cleared2`: PhysLean's Euler–Lagrange condition for this Lagrangian holds exactly when the cleared field equation holds at every point. *Named assumptions: N > 0; V differentiable; u, u_t, u_x and N differentiable on the plane with the named partial derivatives, one mixed partial serving both orders.*
- `lapseField_smoothInCoordinates`: if N and V′ are smooth, the Lagrangian is smooth in jet coordinates. *Named assumptions: N > 0; V differentiable; N and V′ smooth.*
- `action_critical_iff_el2`: the field is a critical point of the action exactly when the cleared field equation holds at every point. *Named assumptions: as for `satisfiesEL_iff_cleared2`, plus a smooth field, a Lagrangian smooth in jet coordinates, and finite action.*

**The energy balance (statements repeated from Tier 2)**

- `energy_time_deriv`: from the cleared field equation at a point, the time derivative of ρ equals (N_t/N)·ρ + (N_x·u_x·u_t + N·u_xx·u_t + N·u_x·u_xt). *Named assumptions: N > 0; the named time derivatives; V differentiable; the field equation at the point.*
- `flux_space_deriv`: the space derivative of f equals −(N_x·u_x·u_t + N·u_xx·u_t + N·u_x·u_xt). *Named assumptions: the named space derivatives.*
- `sourced_continuity`: from the cleared field equation at a point: ∂ρ/∂t + ∂f/∂x = (N_t/N)·ρ. *Named assumptions: N > 0; the named derivatives; the field equation at the point.*
- `arena_obstruction_x`: if N·C is the same constant along x at a fixed time, then N_x·C + N·C_x = 0. *Named assumptions: N·C constant in x; N and C differentiable in x.*
- `obstruction_iff`: under the same condition with N > 0 and C > 0: N_x = 0 exactly when C_x = 0. *Named assumptions: N > 0; C > 0; N·C constant in x; N and C differentiable in x.*

**End to end**

- `action_critical_sourced_continuity`: if the field is a critical point of the action, then ∂ρ/∂t + ∂f/∂x = (N_t/N)·ρ at every point. *Named assumptions: the assumptions of `action_critical_iff_el2`, and the named one-variable derivatives at the point.*
- `action_critical_sourced_continuity_canon`: with N = C_floor/C and ∂C/∂t = G − D_loss substituted, a critical point of the action satisfies ∂ρ/∂t + ∂f/∂x = ((D_loss − G)/C)·ρ. *Named assumptions: C > 0; C_floor > 0; C has time derivative G − D_loss; N and N_t given by the stated formulas; and the assumptions above.*

## Certified construction

- `lapseFieldLagrangian`: the field Lagrangian as a PhysLean `Lagrangian 2 1 1`, with its declared partial derivatives proved to be its fiber derivatives. Named assumptions: N > 0; V differentiable.

## Also audited in this file (not counted)

- `sum_derivIndex21`: a helper lemma: a sum over the three derivative indices (value, time derivative, space derivative) has exactly three terms.
- `jet2_coord10`: a helper lemma: the (1, 0) jet coordinate of the packaged field is its time derivative.

## Not certified

- The tempo law and the Generative Law, which enter the last theorem as substitutions made by hypothesis.
- Finite action and smoothness of the field, which are assumed.
- More than one space dimension.
- The stage 3 chain to the book's metric, whose kernel step remains a named hypothesis in its own file.

## Notes

- The five theorems under "The energy balance" repeat statements already certified in the Tier 2 file, rebuilt in this workspace so the end-to-end theorems can use them. They are counted as instances, not as new statements.
- `energy_time_deriv`, `flux_space_deriv` and `arena_obstruction_x` have no axiom line of their own in the file. `sourced_continuity` is proved directly from the first two and `obstruction_iff` from the third, and those axiom lines therefore cover them.
