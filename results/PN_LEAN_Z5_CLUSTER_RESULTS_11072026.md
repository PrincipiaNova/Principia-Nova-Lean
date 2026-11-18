# Results record: The minimal model

*Appendix Z §5 (the qubit model)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_Z5_CLUSTER_PROOF_11072026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 6 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

Statements about the minimal quantum model of Appendix Z §5. The trace identities hold for square matrices of any size over any commutative ring. The remaining theorems use the qubit's Bloch-vector picture: a state is a vector r with ‖r‖ ≤ 1, its coherence is C(r) = ½(1 + ‖r‖²), and the overlap of two states is ½(1 + ⟨r, s⟩).

## Theorems

**Trace identities (any dimension)**

- `hamiltonian_writes_nothing`: Tr(ρ·[H, ρ]) = 0 for all square matrices ρ and H.
- `only_channels_write`: Tr(ρ·([H, ρ] + K)) = Tr(ρ·K). In a rate written as a commutator plus another term, the commutator contributes nothing to this trace.

**The qubit**

- `definition_one_bounds`: for ‖r‖ ≤ 1: ½ ≤ C(r) ≤ 1; C(r) = ½ exactly when r = 0; and C(r) < 1 exactly when ‖r‖ < 1. *Named assumptions: ‖r‖ ≤ 1.*
- `mu_interior`: if ‖r‖ < 1 then C(r) < 1. *Named assumptions: ‖r‖ < 1.*
- `overlap_positive`: a state strictly inside the Bloch ball has strictly positive overlap with every state. *Named assumptions: ‖r‖ < 1 for the first state; ‖s‖ ≤ 1 for the second.*
- `shell_orthogonality_witness`: on the boundary the conclusion can fail: there are two states with ‖r‖ = ‖s‖ = 1 and overlap exactly zero.

## Not certified

- Theorem 1 of Appendix Z §5 as printed, which is stated in terms of Uhlmann fidelity. What is certified is the overlap form, following the book's own support argument. The fidelity statement itself remains prose, because the library has no fidelity theory to build on. Any citation of Theorem 1 as machine-checked, including through Chapter 13, carries this limit.
- The dynamical reading of the trace identities (that only the non-commutator part changes coherence over time). The identities are algebra; the dynamics is the book's.
- Systems beyond the qubit, for the Bloch-vector theorems.
