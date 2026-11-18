# Results record: The Zeroth PN Law

*Chapter 7 (the Zeroth PN Law and its reason clause)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZEROTH_LAW_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 10 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Two parts. First, the equation ∇·(Cv) = 0 in one dimension, as a statement about the flux C·v. Second, a finite model of pairwise balance: a net flow J(X, Y) between systems, with "X balances Y" meaning J(X, Y) = 0. The model's witness flow is on three systems A, B, C, with a unit flow between A and C and none elsewhere. It is compared with a flow induced by a scalar, J(X, Y) = T(X) − T(Y).

## Theorems

**The equation (one dimension)**

- `divergence_of_product`: d(C·v)/dx = C′·v + C·v′. *Named assumptions: C and v differentiable at the point.*
- `flux_balance`: if the derivative of C·v is zero everywhere, then C·v has the same value at any two points. *Named assumptions: C·v differentiable.*
- `equilibrium_iff_flux_balance`: the derivative of C·v is zero everywhere exactly when C·v has the same value at every pair of points. *Named assumptions: C·v differentiable.*

**Balance in the finite model**

- `Jw_antisymm`: the witness flow is antisymmetric: J(X, Y) = −J(Y, X).
- `balance_reflexive`: for any antisymmetric flow, every system balances itself. *Named assumptions: J antisymmetric.*
- `balance_symmetric`: for any antisymmetric flow, if X balances Y then Y balances X. *Named assumptions: J antisymmetric.*
- `scalarFlow_antisymm`: a flow induced by a scalar is antisymmetric.
- `classical_transitivity`: for a flow induced by a scalar, balance is transitive: if X balances Y and Y balances Z then X balances Z.
- `no_middlemen`: in the witness flow, A balances B and B balances C, but A does not balance C.
- `balance_not_equivalence`: taken together: in the witness flow, balance is reflexive and symmetric but not transitive, while for every scalar-induced flow it is transitive.

## Not certified

- The equation in more than one dimension.
- That any particular physical triple of systems behaves like the witness flow. The model shows the classical inference can fail when the flow is not induced by a scalar; it asserts nothing about specific systems.
- Any dynamical premise of the framework. None is used.
