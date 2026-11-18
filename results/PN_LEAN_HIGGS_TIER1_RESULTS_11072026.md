# Results record: The Higgs potential, Tier 1 (radial profile)

*Appendix Z §13–14*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_HIGGS_TIER1_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 19 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The radial profile of the potential V(r) = −μ²r² + λr⁴, where r stands for |Φ|, and the radial energy W(r) = −μ²r²/2 + λr⁴/4 used for the fluctuation. All statements are one-variable calculus and algebra.

## Theorems

**Shape**

- `hat_slope`: V′(r) = 2r·(2λr² − μ²).
- `origin_critical`: V′(0) = 0.
- `rim_critical`: V′(r) = 0 wherever r² = μ²/(2λ). *Named assumptions: λ ≠ 0.*
- `hat_curvature`: the slope has derivative −2μ² + 12λr².
- `rim_curvature_positive`: on the rim that second derivative is 4μ², which is positive. *Named assumptions: μ ≠ 0; λ ≠ 0; r² = μ²/(2λ).*
- `origin_is_maximum`: at r = 0 the second derivative is −2μ², which is negative. The symmetric point is a local maximum of the profile. *Named assumptions: μ ≠ 0.*

**The minimum and the mass**

- `hat_square_identity`: V(r) = λ·(r² − μ²/(2λ))² − μ⁴/(4λ). *Named assumptions: λ ≠ 0.*
- `rim_global_min`: V(r) ≥ −μ⁴/(4λ) for every r. *Named assumptions: λ > 0.*
- `vacuum_depth`: on the rim, V = −μ⁴/(4λ). *Named assumptions: λ ≠ 0; r² = μ²/(2λ).*
- `minimum_iff`: V(r) = −μ⁴/(4λ) exactly when r² = μ²/(2λ). *Named assumptions: λ > 0.*
- `vev_reconciliation`: v²/2 = μ²/(2λ) exactly when v² = μ²/λ. The section's two printed forms of the vacuum value agree. *Named assumptions: λ ≠ 0.*
- `Wr_slope`: W′(r) = −μ²r + λr³.
- `fluctuation_slope`: the function h ↦ W(v + h) has slope −μ²(v + h) + λ(v + h)³.
- `higgs_mass`: when v² = μ²/λ, that slope has derivative 2μ² at h = 0. This is the printed relation m_H² = 2μ². *Named assumptions: λ ≠ 0; v² = μ²/λ.*

**The bounded field range and the mode sum**

- `annulus_hosts_vacuum`: if the rim radius r* lies between ε and Φ_max, then r* is in the interval [ε, Φ_max] and V(r*) ≤ V(r) for every r. *Named assumptions: λ > 0; r*² = μ²/(2λ); ε ≤ r* ≤ Φ_max.*
- `symmetric_point_excluded`: if ε > 0 then 0 is not in [ε, Φ_max]. *Named assumptions: ε > 0.*
- `vacuum_sum_finite`: a sum of ω_k/2 over a finite set of modes with ω_k ≥ 0 is a nonnegative real number. Finiteness is built in by summing over a finite set. *Named assumptions: ω_k ≥ 0.*
- `unbounded_sum_diverges`: if every ω_k is at least some c > 0, the sum of ω_k/2 over all k does not converge. *Named assumptions: ω_k ≥ c > 0 for all k.*

**Link to the selection law**

- `boltzmann_bridge`: exp(β·((−V(a)) − (−V(b)))) = exp(−β·(V(a) − V(b))). Writing C = −V turns the weight exp(β·ΔC) of Chapter 4 into the familiar exponential of the potential difference.

## Not certified

- The gauge sector, and anything beyond the radial profile.
- That a bounded mode sum is small. Appendix Z §14.3 says so itself: finite is not small, and the cosmological constant problem is not resolved.
- Gauge invariance of a hard cutoff, which §14.3 leaves open.
- Naturalness. The mass relation is checked; the hierarchy problem stands until the scale is specified.
