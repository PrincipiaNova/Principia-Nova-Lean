# Results record: The Higgs potential, Tier 2 (comparison with PhysLean)

*Appendix Z §14.1*

| | |
|---|---|
| Proof file | `physlean/PN_LEAN_HIGGS_TIER2_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib + PhysLean |
| Certified statements | 5 theorems |
| `sorry` | none |
| Axiom audit | Every audited statement rests on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and nothing else, as recorded at certification. |
| Build status | Certified on its recorded toolchain; outside the repository's CI build until the PhysLean workspace pin is recorded. |

## Scope

PhysLean contains its own formal Standard Model Higgs potential, with parameters it calls μ2 and 𝓵 and a field norm ‖φ‖². These theorems check that the quantities printed in Appendix Z §14.1 agree with PhysLean's under the dictionary μ2 = μ² and 𝓵 = λ. The dictionary appears as explicit assumptions in each statement that uses it.

## Theorems

- `physlean_minimum_consumed`: PhysLean's own characterization, restated: for 𝓵 > 0, a point is a global minimum of the potential exactly when either μ2 ≥ 0 and ‖φ‖² = μ2/(2𝓵), or μ2 < 0 and the field is zero there. *Named assumptions: 𝓵 > 0.*
- `potential_form_handshake`: under the dictionary, PhysLean's potential equals −μ²·‖φ‖² + λ·(‖φ‖²)². *Named assumptions: μ2 = μ²; 𝓵 = λ.*
- `convention_handshake`: under the dictionary with λ > 0, a point is a global minimum exactly when ‖φ‖² = μ²/(2λ). This is the section's printed minimum condition. *Named assumptions: μ2 = μ²; 𝓵 = λ; λ > 0.*
- `vacuum_depth_handshake`: under the dictionary with λ > 0: the potential is at least −μ⁴/(4λ) everywhere, and a point is a global minimum exactly when the potential equals −μ⁴/(4λ) there. *Named assumptions: μ2 = μ²; 𝓵 = λ; λ > 0.*
- `stability_direction`: if 𝓵 > 0 the potential is bounded below; and if it is bounded below then 𝓵 ≥ 0. These are two one-way statements, not an equivalence: the case 𝓵 = 0 is left open, as it is in PhysLean.

## Not certified

- The mass relation m_H² = 2μ², which is in the Tier 1 file, and its naturalness, which is claimed nowhere.
- The gauge sector.
- The three limits Appendix Z §14.3 states for itself: a finite vacuum sum is not a small one; a gauge-covariant cutoff is an open problem; the hierarchy problem stands until the scale is specified.
