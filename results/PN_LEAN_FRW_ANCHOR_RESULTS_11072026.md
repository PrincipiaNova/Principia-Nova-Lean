# Results record: The FRW redshift anchor

*Appendix Z §24, Z-N.2 (the calibration case; framework-free)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_FRW_ANCHOR_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 6 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Framework-free: textbook cosmology only. Given the radiation redshift law dE/dt = −(ȧ/a)·E for an energy E(t) and a positive scale factor a(t), the product E·a is conserved. Appendix Z-N.2 uses this case as a calibration check before any of the framework's own objects enter.

## Theorems

- `adiabatic_invariant`: d(E·a)/dt = 0 at a time t. *Named assumptions: the redshift law at t; a differentiable at t; a(t) > 0.*
- `invariant_constant`: E(t)·a(t) = E(s)·a(s) for all times s and t. *Named assumptions: the redshift law at every time; a differentiable; a > 0.*
- `redshift_product`: E(t₁)·a(t₁) = E(t₀)·a(t₀). *Named assumptions: as for `invariant_constant`.*
- `redshift_ratio`: E(t₁)/E(t₀) = a(t₀)/a(t₁). *Named assumptions: as for `invariant_constant`, plus E(t₀) ≠ 0.*
- `halving_witness`: if a(t₁) = 2·a(t₀) then E(t₁) = E(t₀)/2. When the scale factor doubles, the energy halves exactly. *Named assumptions: as for `invariant_constant`.*
- `flat_clock_bookend`: if ȧ = 0 at every time then E is constant. *Named assumptions: the redshift law at every time.*

## Not certified

- The numeric mode integration reported in Appendix Z-N.2 (the invariant held to one part in a thousand). That remains the numeric record; this file proves the exact law the numbers approximate.
- Any link between the scale factor and the book's lapse or coherence. None is assumed or claimed here.
