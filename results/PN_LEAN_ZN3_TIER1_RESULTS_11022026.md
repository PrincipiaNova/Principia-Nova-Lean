# Results record: Z-N.3 metric chain

*Appendix Z §24, Z-N.3 (the Noether variation on the book's own metric)*

| | |
|---|---|
| Proof file | `PN/PN_LEAN_ZN3_TIER1_PROOF_11022026.lean` |
| Library | Lean 4 + mathlib |
| Certified statements | 10 theorems |
| `sorry` | none |
| Axiom audit | all on Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). Source: the repository's CI build log. |
| Build status | Built and audited by the repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). |

## Scope

The algebra and calculus links of the Z-N.3 chain: the Z-G.1 metric assembles the matter Lagrangian, the tempo map τ = exp(V_C/c²) turns the coherence potential into the clock, and the clock rate sets the energy drift. Two steps the book does not derive are carried as named hypotheses and never discharged. This is why the chain has no higher tier.

## Theorems

**The metric and its couplings**

- `metric_reduction`: for τ ≠ 0, (1/τ²)·[½(1/τ²)p_t² − ½τ²g_x² − V] = p_t²/(2τ⁴) − g_x²/2 − V/τ². The gradient term comes out with no power of the clock. *Named assumptions: τ ≠ 0.*
- `kinetic_coupling`: with the fields held fixed, d/dt[p_t²/(2τ⁴)] = −4(τ̇/τ)·[p_t²/(2τ⁴)]. *Named assumptions: τ differentiable and nonzero at t.*
- `potential_coupling`: with the fields held fixed, d/dt[V/τ²] = −2(τ̇/τ)·[V/τ²]. *Named assumptions: τ differentiable and nonzero at t.*
- `gradient_decoupling`: with the fields held fixed, d/dt[g_x²/2] = 0. The term has no dependence on the clock.
- `explicit_source`: with the fields held fixed, the Lagrangian's time derivative is −(τ̇/τ)·(4E_kin − 2E_V), where E_kin = p_t²/(2τ⁴) and E_V = V/τ². The gradient energy does not appear. These are the coefficients the book reports as (+4, −2, 0). *Named assumptions: τ differentiable and nonzero at t.*

**The clock**

- `tempo_map`: if τ = exp(V_C/c²) then τ̇ = (V̇_C/c²)·τ. *Named assumptions: V_C differentiable at t.*
- `tempo_pos`: exp(V_C/c²) > 0. The clock defined by the tempo map is never zero.
- `clock_rate_from_kernel`: if V̇_C = −κ_P·(G − D_loss), then τ̇ = (−κ_P·(G − D_loss)/c²)·τ. *Named assumptions: the displayed equation for V̇_C, named `hkernel`. This is the Green's-function step of Appendix Z-G.3 (localized-source scope). It is assumed, not proved.*

**The drift**

- `canon_drift`: any rate certified for the tempo clock equals V̇_C/c² by uniqueness of derivatives, and then dE/dt = −(2κ_P/c²)·(G − D_loss)·E. *Named assumptions: `hkernel` as above; and the ledger equation dE/dt = 2·(rate)·E, named `hledger`. The book obtains that ledger form for massless matter with mode equipartition; it is assumed here, not re-derived.*
- `flat_clock_limit`: under the same hypotheses, if G = D_loss then dE/dt = 0. *Named assumptions: as for `canon_drift`.*

## Not certified

- The Green's-function step (`hkernel`). The book states it as an assumption with a stated scope, and the file keeps it as one.
- The ledger form (`hledger`), including the massless-matter and equipartition conditions behind it.
- Position dependence of the clock. This file works with a clock that depends on time only; the spatial case is the subject of Z-N.2.
- Any numeric result. The numeric gates remain the symbolic and numeric record.
