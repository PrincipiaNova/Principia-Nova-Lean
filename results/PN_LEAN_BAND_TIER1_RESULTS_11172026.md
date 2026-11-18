# Results record: The geometry of the constraint space

*Chapter 18 §11 (the Interference Model; framework-free)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_BAND_TIER1_PROOF_11172026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 5 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Framework-free: no premise of the book's framework appears in any statement. Chapter 18 §11 gives two formulas for the same object: the intersection F ∩ B of a forward and a backward region, and the set of points minimizing ‖x − F‖ + ‖x − B‖. Here F and B are sets in an arbitrary metric space, ‖x − S‖ is the distance from x to the set S, and J(x) is the sum of the two distances.

## Theorems

- `constraint_space_is_intersection`: for closed sets F and B that overlap, a point minimizes J exactly when it lies in F ∩ B. *Named assumptions: F and B closed; F ∩ B nonempty.*
- `geometric_equals_variational`: under the same conditions, the set of minimizers of J equals F ∩ B. The chapter's two formulas describe the same set. *Named assumptions: F and B closed; F ∩ B nonempty.*
- `broken_band_positive`: if F is compact, B is closed, both are nonempty and they do not meet, then J is bounded below by a positive constant everywhere. *Named assumptions: F compact; B closed; both nonempty; disjoint.*
- `noncompact_door`: without compactness that bound can fail: there are two closed, nonempty, disjoint sets in the plane (a horizontal axis and the graph of the exponential) for which J is positive at every point yet takes values below any positive number.
- `smear_witness`: for the two one-point sets {0} and {1} on the real line: J equals 1 on the whole segment [0, 1] and is at least 1 everywhere; the minimizers are exactly that segment; and the two sets have empty intersection. When the sets do not meet, minimizing no longer means lying in both.

## Not certified

- Which physical or neural systems realize F and B.
- Any particular choice of metric. The theorems hold for every metric and select none.
- Any claim about experience. The chapter's reading of this geometry is the chapter's.
