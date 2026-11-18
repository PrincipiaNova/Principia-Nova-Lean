# Results record: The qubit model beside the Turn

*Appendix Z §5 compared with Chapter 10 §6*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_Z5_TURN_RECEIPT_PROOF_11172026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 6 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

An illustration, not an identification. A single qubit relaxing toward an environment state s, with Bloch vector obeying ṙ = s − r, is used to exhibit the shapes Chapter 10 §6 describes. This relaxation law is the file's own model; the book prints the channel classification, not this generator. Coherence is C(r) = ½(1 + ‖r‖²), whose floor is ½ at r = 0. The trajectories are explicit, and the file proves they solve the model.

## Theorems

**The channel**

- `channel_identity_state_relative`: there are an environment state s and two states r₁, r₂, all strictly inside the ball, such that the same channel raises coherence at r₁ and lowers it at r₂ (⟨r₁, s − r₁⟩ > 0 and ⟨r₂, s − r₂⟩ < 0).
- `drain_bounded_by_arrow`: in any real inner-product space, for γ ≥ 0, both the negative part and the positive part of γ·⟨r, s − r⟩ are at most γ·‖r‖·(‖s‖ + ‖r‖). Both vanish as r shrinks to zero. *Named assumptions: γ ≥ 0.*

**Trajectories**

- `arrow_turns_witness`: for s = (½, 0, 0) and start r₀ = (−¼, ¼, 0): the trajectory solves the model; C(0) = 9/16; coherence is falling at t = 0 (rate −¼); its rate is zero at t = ln(5/3); its rate is positive at every later time; and ‖r(t)‖² ≥ 1/40 at all times, so the floor is never reached.
- `no_dip_witness`: for the same s and start r₀ = (¾, 0, 0): the trajectory solves the model; C(0) = 25/32; coherence falls at every time; and C stays above 5/8. Not every start turns. This is not a counterexample to the Turn: the trajectory never comes near the floor.
- `anchor_glide`: on the first trajectory, C(t) < 5/8 for every t ≥ 0 and C(t) tends to 5/8. The resting value is approached and never reached.
- `merger_is_limit_state`: with the environment at the centre (s = 0) and any start r₀ ≠ 0: the trajectory e^(−t)·r₀ solves ṙ = −r; C stays strictly above ½ at every time; and C tends to ½. *Named assumptions: r₀ ≠ 0.*

## Not certified

- That the Turn of Chapter 10 §6 is this model at a larger scale. The file shows a small system with the same shape; it proves no connection between the two.
- The relaxation law as physics. It is a named model, chosen for the illustration.
- The exclusion of s = 0 as a physical environment. Appendix Z §5.4 argues that in prose.
- Anything about tempo, which does not appear in these statements.
