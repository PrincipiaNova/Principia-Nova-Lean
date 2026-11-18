# Results record: Winding numbers, Tier 2 (the phase lift)

*Chapter 8 §6 and Chapter 20 §8*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_WINDING_TIER2_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 4 new theorems (the file also repeats the 7 of Tier 1) |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Removes Tier 1's one assumption. There the phase function was given. Here it is proved that every continuous path on the circle has a continuous phase, using the library's covering-space results, so the integer winding number needs no supplied data.

## Theorems

- `no_gradual_unwinding_interval`: a continuous integer-valued function on the unit interval is constant. *Named assumptions: continuity; integer values.*
- `phase_lift_exists`: every continuous path γ on the circle has a continuous phase θ with e^(iθ(t)) = γ(t) for all t.
- `loop_winding_integer`: every continuous loop on the circle has such a phase, and its total change θ(1) − θ(0) is 2π times an integer. *Named assumptions: the path is a loop: γ(1) = γ(0).*
- `winding_well_defined`: any two phases of the same path have the same total change. The winding number belongs to the loop, not to the choice of phase. *Named assumptions: both are phases of the same path.*

## Also audited in this file (not counted)

- `winding_integer`: repeated unchanged from the Tier 1 file; counted there.
- `winding_via_integral`: repeated unchanged from the Tier 1 file; counted there.
- `no_gradual_unwinding`: repeated unchanged from the Tier 1 file; counted there.
- `tear_quantum`: repeated unchanged from the Tier 1 file; counted there.
- `trivial_loop`: repeated unchanged from the Tier 1 file; counted there.
- `pair_creation_blind_spot`: repeated unchanged from the Tier 1 file; counted there.
- `discrete_jump_witness`: repeated unchanged from the Tier 1 file; counted there.

## Not certified

- The physical reading of the phase, as in Tier 1.
- The classification of loops up to deformation.
