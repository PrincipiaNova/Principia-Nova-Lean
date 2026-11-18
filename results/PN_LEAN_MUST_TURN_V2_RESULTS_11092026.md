# Results record: The Turn under a rate bound

*Chapter 10 §6 (the Turn)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_MUST_TURN_V2_PROOF_11092026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 7 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

A corrected form of the Turn. The first form (`must_turn`, in the ledger file) bounds the size of the drift near the floor, which excludes a field that arrives falling. This file instead bounds the drift's rate of change: while C ≤ C_min + δ, the drift D = G − D_loss increases at rate at least ε. That hypothesis is called the squeeze. The two forms are alternatives, not a pair to be used together.

## Theorems

**The Turn**

- `must_turn_v2`: a field in the zone at time t₁ ≥ 0 has strictly positive drift at some time in the window [t₁, t₁ + max(0, −D(t₁))/ε + 1]. *Named assumptions: the drift form dC/dt = G − D_loss; G and D_loss continuous; D differentiable with continuous derivative D′; ε > 0; the squeeze, D′ ≥ ε whenever t ≥ 0 and C ≤ C_min + δ. The floor is not a hypothesis and no proof uses it.*
- `turn_time_bound`: if the field enters the zone with D(t₁) ≤ 0, the drift equals zero at some time in [t₁, t₁ + (−D(t₁))/ε]. *Named assumptions: as for `must_turn_v2`.*
- `turn_in_zone`: under the same conditions there is a time in that window at which the drift is zero, the field is still in the zone, and the drift was ≤ 0 at every earlier time since t₁. *Named assumptions: as for `must_turn_v2`.*

**How the two forms relate**

- `activity_forms_exclusive`: the first form's bound (|D| ≥ ε′ in the zone) and the squeeze cannot both hold of a field that is in the zone with D ≤ 0. Together they give a contradiction. *Named assumptions: as for `must_turn_v2`, plus the first form's bound with ε′ > 0.*
- `squeeze_admits_falling_entrant`: there is an explicit model satisfying every hypothesis of `must_turn_v2` together with C ≥ C_min, G ≥ 0, D_loss ≥ 0 and a strictly falling entry. The model is C = t²/2 − t + 3/4, G = t² + t + 1, D_loss = t² + 2, with C_min = 0, δ = 1, ε = 1, t₁ = 0.

**The arrival theorem, scoped to the floor**

- `cannot_arrive_scoped`: if C ≥ C_min at all times and the drift is nonzero whenever C = C_min, then C > C_min at all times. *Named assumptions: the drift form; the floor; the nonzero-drift clause required only at the floor, which is where Chapter 10 §6 states it.*
- `scoped_strictly_weaker`: the floor-only clause is weaker than requiring nonzero drift everywhere: C = t² + 1 over C_min = 0 satisfies the first and violates the second (its drift is zero at t = 0, away from the floor).

## Not certified

- The squeeze itself. It is assumed, not derived. Nothing here derives any size, sign or form of G or D_loss.
- That the universe, or any physical system, satisfies the squeeze near its floor. Chapter 10 §6 gives the book's argument in prose.
- Any statement about what happens after the drift turns positive.
