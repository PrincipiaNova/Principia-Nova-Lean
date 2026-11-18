# Results record: The band under free evolution

*Appendix Z §10 (operators and dynamics)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_Z10_BAND_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 4 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Momentum-space statements about band-limited states. A function is "in the band" for a cutoff p_max if it vanishes wherever |p| > p_max. Free evolution multiplies by the phase e^(−ip²t/2mħ).

## Theorems

- `phase_preserves_support`: e^(iφ(p))·f(p) = 0 exactly when f(p) = 0. Multiplying by a phase moves no zero.
- `mu_band_invariant`: if ψ₀ is in the band, then e^(−ip²t/2mħ)·ψ₀ is in the band, for every t. *Named assumptions: ψ₀ in the band.*
- `spectral_weight_frozen`: |e^(−ip²t/2mħ)·ψ₀(p)| = |ψ₀(p)| at every p. Free evolution changes phase only.
- `convolution_door`: there are two real polynomials of degree at most 1 whose product has degree 2. Since multiplying polynomials convolves their coefficients, this shows at discrete grain that convolution can enlarge support.

## Not certified

- The Hilbert-space (L²) and position-space formulations, which stay as standard prose.
- Which interactions keep states in the band. `convolution_door` shows only that the question is not empty; the classification is an open problem the book names.
- The identification of the momentum cutoff with the book's Mu bound.
