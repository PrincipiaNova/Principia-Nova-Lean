# Results record: The ledger and the Turn

*Chapter 7 (the thermodynamic ledger) and Chapter 10 §6 (the Turn)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_LEDGER_TURN_PROOF_11042026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 8 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Consequences of the drift form dC/dt = G − D_loss for real functions of time: the budget, the monotone ledger, and what happens at a floor C_min. G is generation, D_loss is loss, and the ledger is S = ∫D_loss.

## Theorems

**The ledger**

- `budget_identity`: C(b) − C(a) = ∫G − ∫D_loss over [a, b]. *Named assumptions: dC/dt = G − D_loss at every time; G and D_loss continuous.*
- `ledger_monotone`: for a ≤ b, ∫₀ᵃ D_loss ≤ ∫₀ᵇ D_loss. The ledger only grows. *Named assumptions: D_loss continuous; D_loss ≥ 0.*
- `balance_patch`: if G = D_loss throughout the interval between a and b, then C(b) = C(a). *Named assumptions: the drift form; G and D_loss continuous.*
- `ledger_dominated`: ∫₀ᵇ D_loss ≤ ∫₀ᵇ G + (C(0) − C_min). Losses can exceed generation only by the initial amount above the floor. *Named assumptions: the drift form; continuity; C ≥ C_min at all times.*

**At the floor**

- `no_eternal_fade`: it cannot be that G − D_loss ≤ −ε at every time t ≥ 0, for any ε > 0. *Named assumptions: the drift form; continuity; C ≥ C_min at all times.*
- `the_turn`: if C touches C_min at a time t₀ and stays at or above it afterward, and the drift at t₀ is not zero, then the drift at t₀ is positive. *Named assumptions: the drift form; C(t₀) = C_min; C ≥ C_min from t₀ on; the drift at t₀ is nonzero (the book's Perpetual Flow, as a hypothesis).*
- `cannot_arrive`: if C ≥ C_min at all times and the drift is never zero, then C > C_min at all times. The floor is never reached. *Named assumptions: the drift form; the floor; the drift nonzero at every time. The companion file restates this with the nonzero clause required only at the floor.*
- `must_turn`: if the field is within δ of the floor at some time t₁ ≥ 0, and |G − D_loss| ≥ ε whenever it is that close, then the drift is positive at some time t ≥ 0. The hypotheses cannot all hold for a field that enters the zone falling, so this certifies that the zone admits no fading states. It does not certify a fall followed by a rise; that is `must_turn_v2` in the companion file. *Named assumptions: the drift form; continuity; the floor at all times; the bound |G − D_loss| ≥ ε in the zone.*

## Not certified

- G ≥ 0, and D_loss ≥ 0 beyond its use as a hypothesis in `ledger_monotone`. The book treats both signs as basic assumptions (Chapter 8 §6).
- The floor C ≥ C_min and the nonzero-drift clause, which are hypotheses wherever they are used.
- That total loss over all time is finite. Only the budget bound `ledger_dominated` is proved; the finite total is the book's cosmological claim.
- Any dependence on position. All quantities here are functions of time only.
