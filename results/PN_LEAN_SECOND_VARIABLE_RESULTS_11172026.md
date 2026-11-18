# Results record: Why a turn needs a second variable

*Background to Chapter 10 §6 (framework-free)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_SECOND_VARIABLE_PROOF_11172026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 4 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Framework-free: no premise of the book's framework appears in any statement. The subject is a one-variable autonomous law Ċ = F(C), where the rate of change depends only on the current value.

## Theorems

- `first_order_rest_is_forever`: if F is Lipschitz, C solves Ċ = F(C), and the drift is zero at one instant, then C is constant for all time. *Named assumptions: F Lipschitz; C solves the law at every time.*
- `first_order_cannot_turn`: for any function F at all, if C solves Ċ = F(C) then the drift is never negative at one time and positive at another. *Named assumptions: C solves the law at every time. No condition on F.*
- `two_variables_can_turn`: with the drift as its own state (Ċ = D, Ḋ = 1) there is a solution whose drift is negative at t = 0, zero at t = 1 and positive at t = 2.
- `rest_needs_smoothness`: there are F and C with C solving Ċ = F(C), the drift zero at t = 0, and C(1) ≠ C(0). The example is C = t³ with F(c) = 3·|c|^(2/3). So the Lipschitz hypothesis of the first theorem cannot be dropped.

## Not certified

- Any connection to the book's dynamics. The file says what one-variable laws cannot do; which additional variable the book's Turn relies on is not addressed here.
