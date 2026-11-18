# Results record: The Self-Identity Requirement: skeleton

*Appendix Z §22 (Theorem 6)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_Z22_SKELETON_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 12 theorems and 1 certified construction |
| `sorry` | none |
| Axiom audit | 1 on no axioms; 11 on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The arithmetic and the library inputs of Theorem 6, not the theorem as a whole. The self-model is a finite catalogue S inside a finite set D of defects to be monitored; the coverage ratio is ρ = |S|/|D|; probabilities are fractions of finite sets. The book's premises enter as hypotheses: the catalogue is nonempty (the floor) and never the whole of D (the ceiling). The strict-case model takes a configuration to be a set of relations, with a transition from A to B when A is contained in B.

## Theorems

**Coverage and escape**

- `mu_bounded_coverage`: for whole numbers with 0 < m < n: 0 < m/n < 1. *Named assumptions: 0 < m; m < n.*
- `escape_bound_uniform`: the fraction of D outside S equals 1 − |S|/|D|. *Named assumptions: S ⊆ D; D nonempty.*
- `no_sigma_blind`: with an empty catalogue, the fraction outside is 1. *Named assumptions: D nonempty.*
- `escape_concentrated_strict`: if the catalogue is nonempty, the uniform escape fraction 1 − |S|/|D| is strictly less than 1. Drift that lands entirely outside the catalogue therefore escapes strictly more often than uniform drift. *Named assumptions: S nonempty; D nonempty.*
- `corollary_6_1`: for 0 < p < 1, the sum of (n + 1)·(1 − p)ⁿ·p over all n is 1/p. This is the expected waiting time for a per-step drift probability p. *Named assumptions: 0 < p < 1.*
- `frozen_sigma_rejects_growth`: if a catalogue is contained in the structure at time t, then anything present at time t + 1 but not at time t is outside the catalogue. *Named assumptions: the catalogue is contained in the earlier structure.* *(audits to no axioms)*
- `tempo_differential`: if the catalogue grows as a₀ + a·t and the structure as b₀ + b·t with 0 ≤ a < b, the ratio (a₀ + a·t)/(b₀ + b·t) strictly decreases for t ≥ 0, tends to a/b, and a/b < 1. *Named assumptions: a ≥ 0; b > 0; a < b; a₀, b₀ > 0; and a·b₀ < b·a₀ (the ratio starts above its limit).*
- `theorem_six_skeleton`: with a nonempty catalogue that is not all of D: 0 < ρ < 1, the escape fraction is 1 − ρ, and the expected waiting time is 1/p. *Named assumptions: S ⊆ D; S nonempty; S ≠ D; 0 < p < 1.*

**The strict-case model and the library inputs**

- `morphism_iff_preserves`: a transition from A to B exists exactly when A ⊆ B.
- `strict_case_rigid`: in this model, isomorphic configurations are equal.
- `profile_determines`: in this model, configurations with isomorphic Yoneda profiles are equal. This uses the library's Yoneda lemma.
- `ceiling_rice`: Rice's theorem, from the library: for a class of partial functions that contains one computable function and omits another, it is undecidable whether a program computes a function in the class. *Named assumptions: one partial recursive function in the class and one outside it.*

## Certified construction

- `category_check`: the strict-case model is a category. Its identity, composition, associativity and unit laws are checked by the kernel.

## Also audited in this file (not counted)

- `identity_exists`: a definition: the identity transition on a configuration.
- `floor_yoneda`: a definition packaging the library's Yoneda result for this model.
- `profile_evaluation`: a definition packaging the library's Yoneda equivalence.

## Not certified

- Theorem 6 as a whole. Appendix Z §22 is not machine-checked as a section.
- The book's axioms, which enter only as premises. As the section's own note on premises says, they are not derived within the formal system.
- The Kolmogorov-complexity argument, which the book names as the load-bearing route to the ceiling. The library has nothing to build it on, so it remains prose. Rice's theorem is the on-ramp only.
- That real systems match the uniform or linear-growth models used here.
