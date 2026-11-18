# Results record: Selection and the loss dial

*Chapter 5 §3–4 and Chapter 6 (with Chapter 13 §4 as a limit only)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_PMD_GAMMA_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 9 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Three small groups. Selection among a finite set of modes whose weights are exp(β·C), with β the selectivity. The equivalence of "lose less" and "gain more" at fixed income. And arithmetic facts about the product τ·Γ that the book uses for the loss rate.

## Theorems

**Selection**

- `argmax_favored`: if mode i₀ has the largest coherence in the set and β ≥ 0, it has the largest weight; strictly larger than any strictly less coherent mode when β > 0. *Named assumptions: weights are exp(β·C) with no other factor (uniform base weights); β ≥ 0.*
- `lock_limit`: if i₀ is in the set and strictly more coherent than every other mode, its share of the total weight tends to 1 as β → ∞. *Named assumptions: i₀ in the set; unique strict maximum.*
- `partial_lock`: at every finite β, every mode in a nonempty set has a strictly positive share. *Named assumptions: the set is nonempty.*
- `pmd_equivalence`: if D is a strictly decreasing function of coherence, then i₀ maximizes C over the set exactly when it minimizes D(C). *Named assumptions: D strictly antitone.*

**The objective**

- `pmd_objective_equivalence`: for two evolutions with ΔC₁ = G − D₁ and ΔC₂ = G − D₂ and the same G: D₁ ≤ D₂ exactly when ΔC₂ ≤ ΔC₁, and likewise with strict inequalities. *Named assumptions: the two budget equations with a common G.*

**The product τ·Γ**

- `bridge_equation`: for τ ≥ 0 and Γ ≥ 0: τ·Γ ≥ 0; it increases with Γ at fixed τ; and it increases with τ at fixed Γ ≥ 0. *Named assumptions: nonnegativity of the factors.*
- `gamma_mu_bounds`: for τ > 0 and 0 < Γ < 1: 0 < τ·Γ < τ. *Named assumptions: τ > 0; 0 < Γ < 1.*
- `entropy_decomposition`: if S has derivative τ(t)·Γ(t) at every time and that product is continuous, then ∫ τ·Γ dt over [a, b] equals S(b) − S(a). *Named assumptions: the derivative of S; continuity of τ·Γ.*
- `floor_mirror`: for Γ > 0, C_floor > 0 and 0 < C₁ < C₂: Γ·C_floor/C₂ < Γ·C_floor/C₁. With τ = C_floor/C, loss is larger where coherence is lower. *Named assumptions: positivity as stated.*

## Not certified

- The bridge equation D_loss = τ·Γ itself, and the tempo law τ = C_floor/C. The theorems are about those expressions; that they describe nature is the book's claim.
- The variational statement δ∫D dt = 0 and any Euler–Lagrange treatment. The book labels that form as not meant for computation.
- Selection with non-uniform base weights.
- Chapter 13's locking regimes at finite selectivity. Only the β → ∞ limit and its finite-β counterpart are covered.
