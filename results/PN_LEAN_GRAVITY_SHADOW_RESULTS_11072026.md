# Results record: The gravity sector at radial grain

*Chapter 5 §3 and Appendix Z-G (Z-G.2, Z-G.3, Z-G.4)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_GRAVITY_SHADOW_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 17 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Calculus and algebra facts about the printed formulas of the gravity sector, in one radial variable. This is not general relativity formalized: there are no manifolds and no tensors. The potential is V = −M/r, the clock factor is e^(2Φ) with Φ = −M/r, the areal radius is R(r) = r·e^(M/r), and K(M, r) is the printed curvature-invariant formula M²·(28M² − 64Mr + 48r²)·e^(−4M/r)/r⁸, taken as given.

## Theorems

**Chapter 5**

- `flux_inverse_square`: the total flux through every sphere is the same constant, 4πr²·F(r) = Φ₀ for all r > 0, exactly when F(r) = Φ₀/(4πr²) for all r > 0.
- `potential_harmonic`: V = −M/r has slope M/r²; that slope has derivative −2M/r³; and −2M/r³ + (2/r)·(M/r²) = 0, so the radial Laplacian of V vanishes. *Named assumptions: r ≠ 0.*
- `gradients_coexist_additively`: if two potentials have slopes g₁ and g₂ at a point, their sum has slope g₁ + g₂ there. *Named assumptions: both differentiable at the point.*

**Three wirings and their light cones (Appendix Z-G.2)**

- `conformal_blindness`: with one factor on both time and space, −τ² + τ²·s² = 0 exactly when s² = 1. The null slope does not depend on τ. *Named assumptions: τ ≠ 0.*
- `time_only_cone`: with the factor on time only, −τ² + s² = 0 exactly when s² = τ².
- `reciprocal_cone`: with reciprocal factors, −τ² + s²/τ² = 0 exactly when s² = τ⁴. *Named assumptions: τ ≠ 0.*

**The strong-field forms (Appendix Z-G.4)**

- `no_horizon`: e^(2·(−M/r)) > 0 for all M and r. The clock factor is never zero.
- `tempo_asymptote`: for M > 0, e^(−2M/r) tends to 0 as r approaches 0 from above. *Named assumptions: M > 0.*
- `throat_slope`: R(r) = r·e^(M/r) has slope e^(M/r)·(1 − M/r). *Named assumptions: r ≠ 0.*
- `throat_critical`: at r = M the slope of R is zero, and R(M) = M·e. *Named assumptions: M ≠ 0.*
- `throat_curvature`: the slope of R has derivative e^(M/r)·M²/r³, which is positive. *Named assumptions: M ≠ 0; r > 0.*
- `throat_global_min`: M·e ≤ r·e^(M/r) for every r > 0. The areal radius is never smaller than its value at r = M. *Named assumptions: r > 0. No sign condition on M is needed.*
- `kretschmann_at_throat`: K(M, M) = 12·e^(−4)/M⁴. *Named assumptions: M ≠ 0.*
- `kretschmann_pos`: K(M, r) > 0 for every r > 0. *Named assumptions: M ≠ 0; r > 0.*
- `no_singularity_limit`: for M > 0, K(M, r) tends to 0 as r approaches 0 from above. *Named assumptions: M > 0.*
- `schwarzschild_door`: for comparison, 48M²/r⁶ tends to infinity as r approaches 0 from above. *Named assumptions: M ≠ 0.*
- `gradient_stress_identity`: M²·e^(−2M/r)/r⁴ = (e^(−M/r)·M/r²)². *Named assumptions: r ≠ 0.*

## Not certified

- That K is the Kretschmann invariant of the book's metric, or that R is its areal radius. The formulas are taken as printed; deriving them from the metric would need tensor machinery this file does not use.
- The metric itself as a solution of field equations.
- The numeric tests (light deflection, PPN parameters, perihelion advance, ringdown), which remain the symbolic and numeric record.
- The behaviour of K at large r, and the sourcing constant, which the book leaves open.
