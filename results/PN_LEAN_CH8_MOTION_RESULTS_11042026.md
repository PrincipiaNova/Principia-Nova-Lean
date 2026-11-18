# Results record: Motion along the coherence gradient

*Chapter 8 §3 (Law 2) and §4 (Equation 1), with Appendix Z §14.4*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_CH8_MOTION_PROOF_11042026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 8 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The chapter's two printed motion laws as two regimes, and the relation between them. Setting: any real inner-product space. The gradient ∇C is named data: a vector field whose inner product gives the derivative of C. The acceleration law is a = (k_s/τ)·∇C. The flow law is dx/dt = α_f·ρ·∇C, with the external term set to zero.

## Theorems

**The acceleration law**

- `acceleration_aligned`: ⟨a, ∇C⟩ = (k_s/τ)·‖∇C‖². *Named assumptions: the acceleration law holds at the time considered.*
- `no_opposition`: ⟨a, ∇C⟩ ≥ 0. *Named assumptions: the acceleration law; k_s > 0; τ > 0.*
- `equilibrium_iff`: a = 0 exactly when ∇C = 0 at the trajectory point. *Named assumptions: the acceleration law; k_s ≠ 0; τ ≠ 0.*
- `coherence_rate_along_path`: along a trajectory x(t) with velocity v, dC/dt = ⟨∇C, v⟩. *Named assumptions: ∇C is the gradient of C at x(t); x has derivative v.*
- `newtonian_first_integral`: at constant τ, the quantity ½‖v‖² − (k_s/τ)·C(x) has zero time derivative along the motion. *Named assumptions: the acceleration law; ∇C is the gradient of C; x and v differentiable; τ a constant.*

**The flow law**

- `flow_regime_climb`: if dx/dt = α_f·ρ·∇C then dC/dt = α_f·ρ·‖∇C‖², which is ≥ 0. Coherence does not decrease along the flow. *Named assumptions: α_f·ρ > 0; ∇C is the gradient of C; the flow law holds at the time considered.*
- `flow_stationary_iff`: α_f·ρ·‖∇C‖² = 0 exactly when ∇C = 0. *Named assumptions: α_f·ρ > 0.*

**The relation between them**

- `overdamped_bridge`: add linear drag, a = (k_s/τ)·∇C − γ·v. Where a = 0, the velocity is v = (k_s/(γ·τ))·∇C, which has the form of the flow law. *Named assumptions: τ > 0; γ > 0; the drag law; a = 0.*

## Not certified

- That either printed law holds in nature. Each enters as a hypothesis.
- A monotone rise in coherence for the acceleration law. It is proved only for the flow law; under the acceleration law a body can move against the gradient.
- The first integral for time-varying tempo, and the flow law with a nonzero external term.
- The scope clause of Appendix Z §14.4 on when the two regimes coincide, which is prose.
