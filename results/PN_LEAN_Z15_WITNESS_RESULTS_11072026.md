# Results record: Witnesses for the Incompleteness Principle

*Appendix Z §15 (framework-free)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_Z15_WITNESS_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 7 theorems |
| `sorry` | none |
| Axiom audit | 2 on no axioms; 3 on `propext` and `Quot.sound` (no choice); 2 on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Framework-free: these are standard theorems of mathematics and computability, most taken directly from the library. Appendix Z §15 cites them as witnesses; this file checks that they hold as cited. No premise of the book's framework appears in any statement.

## Theorems

- `lawvere_core`: Lawvere's fixed-point theorem: if there is a surjection from α onto the functions α → β, then every function β → β has a fixed point. *Named assumptions: the surjection.* *(audits to no axioms)*
- `diagonal_unification`: no function from α to the subsets of α is surjective (Cantor's theorem), proved inside the file from `lawvere_core`. *(audits to `propext` and `Quot.sound`; no choice)*
- `no_summit`: the same statement as `diagonal_unification`, here taken from the library's own proof of Cantor's theorem. The two differ in proof, not in statement. *(audits to no axioms)*
- `totality_not_object_russell`: the class of all sets is not a member of the class of all sets. *(audits to `propext` and `Quot.sound`; no choice)*
- `totality_not_object_burali_forti`: the class of all ordinals is not a set. *(audits to `propext` and `Quot.sound`; no choice)*
- `halting_wall`: for each input n, the set of programs that halt on n is not decidable, and the set of programs that do not halt on n is not even semi-decidable.
- `mu_open_witness`: there is a sequence inside the open interval (−1, 1) that converges to 1, and 1 is not in the interval. A limit can exist outside the space the sequence lives in.

## Not certified

- Gödel's incompleteness theorems, Tarski's undefinability theorem, the describability results, the index-theorem family (Poincaré–Hopf and its relatives), and the Page–Wootters result. The library does not yet contain what would be needed, so those witnesses remain prose.
- Appendix Z §15 as a whole. The claim that these results are instances of one principle is the book's own claim and is not a theorem here.
