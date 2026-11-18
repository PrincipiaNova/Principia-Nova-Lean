# Results record: The Composition Inheritance (nested clocks)

*Appendix Z §24 (Composition) and Chapter 6 §2*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_LEIBNIZ_PANEL_PROOF_11042026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 5 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

How rates compose when one clock is a reparametrization of another. Each clock is a real function with a derivative; nesting is function composition. The content is the chain rule, applied to clocks.

## Theorems

- `nested_rates_multiply`: if f has rate τ₁ at t and g has rate τ₂ at f(t), then g∘f has rate τ₂·τ₁ at t. *Named assumptions: the two derivatives exist.*
- `composition_rate_unique`: any rate r certified for g∘f at t equals τ₂·τ₁. The product is forced by uniqueness of derivatives. *Named assumptions: the two derivatives exist.*
- `three_level_stack`: three nested clocks compose at τ₃·τ₂·τ₁. *Named assumptions: the three derivatives exist.*
- `uniform_factors`: linear clocks stack: s ↦ k₂·(k₁·s) has rate k₂·k₁.
- `forcings_meet_in_log`: for positive factors, log(τ₂·τ₁) = log τ₂ + log τ₁. A product of tempo factors becomes a sum under the logarithm. *Named assumptions: τ₁ > 0 and τ₂ > 0.*

## Not certified

- That each factor depends only on its own arena's coherence (the book's locality clause). It does not appear in any statement here.
- Parallel composition of overlapping arenas, which Chapter 6 §2 leaves open. These theorems cover serial nesting only.
- That the product form is more than the chain rule. It is the chain rule, and the file claims nothing beyond it.
