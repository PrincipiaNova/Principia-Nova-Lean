# Results records

One record for each proof file in this repository. A record says in plain words what its file's theorems state, which assumptions each one names, and what the file does not establish. The theorem statements in the proof files are the authority; where a record and a statement differ, the statement governs.

## How to read a record

- **Theorems.** Each entry gives the theorem's name as it appears in the proof file, a plain restatement, and its named assumptions. A named assumption is a hypothesis written into the theorem's statement. Nothing is assumed outside the statements.
- **Not certified.** What the file does not prove. This list is part of the result.
- **Axiom audit.** Lean reports which axioms each theorem depends on. Lean's standard three are `propext`, `Classical.choice` and `Quot.sound`. Some theorems here need fewer, and the record says so.
- **Build status.** The files in `PN/` are built and audited from source by this repository's CI pipeline on the pinned toolchain (Lean v4.36.0, mathlib `6201aea8`). The four files in `physlean/` are certified on their recorded toolchain and are outside the CI build until the PhysLean workspace pin is recorded.

## Totals

- **225 certified theorem instances** in 33 proof files: 204 in the 29 `PN/` files and 21 in the 4 `physlean/` files.
- **219 distinct statements.** Six instances repeat a statement certified in an earlier file: `drift_law_at` in the Noether stage 1 Tier 3 file, and the five energy-balance theorems in the Noether stage 2 Tier 3 file. Each such record marks the repeats. In the Appendix Z §15 file, `diagonal_unification` and `no_summit` state the same theorem with different proofs (one built in the file from the Lawvere core, one taken from the library); they are counted as two statements.
- **3 certified constructions**, counted separately from theorems: `lapseLagrangian`, `lapseFieldLagrangian` and `category_check`.
- **Axioms.** 5 theorems depend on no axioms at all (`lawvere_core`, `no_summit`, `frozen_sigma_rejects_growth`, `arena_obstruction`, `obstruction_iff`; the last two are those of the Noether stage 2 Tier 1 file). 7 depend on `propext` alone and 3 on `propext` and `Quot.sound` without choice. The remaining 210 depend on the standard three. No theorem depends on any other axiom, and no file contains `sorry`.

## Coverage

| Proof file | Record | Theorems | Constructions |
|---|---|---|---|
| `PN/PN_LEAN_BAND_TIER1_PROOF_11172026.lean` | [The geometry of the constraint space](PN_LEAN_BAND_TIER1_RESULTS_11172026.md) | 5 |  |
| `PN/PN_LEAN_CH8_MOTION_PROOF_11042026.lean` | [Motion along the coherence gradient](PN_LEAN_CH8_MOTION_RESULTS_11042026.md) | 8 |  |
| `PN/PN_LEAN_CRVL_TIER1_PROOF_11042026.lean` | [Coherence-Relative Velocity Law, Tier 1](PN_LEAN_CRVL_TIER1_RESULTS_11042026.md) | 10 |  |
| `PN/PN_LEAN_CRVL_TIER2_PROOF_11042026.lean` | [Coherence-Relative Velocity Law, Tier 2 (the cone-slope bridge)](PN_LEAN_CRVL_TIER2_RESULTS_11042026.md) | 7 |  |
| `PN/PN_LEAN_DOOB_TIER1_PROOF_11072026.lean` | [The exponential bias, Tier 1 (finite model)](PN_LEAN_DOOB_TIER1_RESULTS_11072026.md) | 6 |  |
| `PN/PN_LEAN_DOOB_TIER2_PROOF_11072026.lean` | [The exponential bias, Tier 2 (martingale form)](PN_LEAN_DOOB_TIER2_RESULTS_11072026.md) | 6 |  |
| `PN/PN_LEAN_FORCED_EXP_PROOF_11042026.lean` | [The forced exponential](PN_LEAN_FORCED_EXP_RESULTS_11042026.md) | 4 |  |
| `PN/PN_LEAN_FRW_ANCHOR_PROOF_11072026.lean` | [The FRW redshift anchor](PN_LEAN_FRW_ANCHOR_RESULTS_11072026.md) | 6 |  |
| `PN/PN_LEAN_GRAVITY_SHADOW_PROOF_11072026.lean` | [The gravity sector at radial grain](PN_LEAN_GRAVITY_SHADOW_RESULTS_11072026.md) | 17 |  |
| `PN/PN_LEAN_HIGGS_TIER1_PROOF_11072026.lean` | [The Higgs potential, Tier 1 (radial profile)](PN_LEAN_HIGGS_TIER1_RESULTS_11072026.md) | 19 |  |
| `PN/PN_LEAN_LEDGER_TURN_PROOF_11042026.lean` | [The ledger and the Turn](PN_LEAN_LEDGER_TURN_RESULTS_11042026.md) | 8 |  |
| `PN/PN_LEAN_LEIBNIZ_PANEL_PROOF_11042026.lean` | [The Composition Inheritance (nested clocks)](PN_LEAN_LEIBNIZ_PANEL_RESULTS_11042026.md) | 5 |  |
| `PN/PN_LEAN_MUST_TURN_V2_PROOF_11092026.lean` | [The Turn under a rate bound](PN_LEAN_MUST_TURN_V2_RESULTS_11092026.md) | 7 |  |
| `PN/PN_LEAN_PMD_GAMMA_PROOF_11072026.lean` | [Selection and the loss dial](PN_LEAN_PMD_GAMMA_RESULTS_11072026.md) | 9 |  |
| `PN/PN_LEAN_SECOND_VARIABLE_PROOF_11172026.lean` | [Why a turn needs a second variable](PN_LEAN_SECOND_VARIABLE_RESULTS_11172026.md) | 4 |  |
| `PN/PN_LEAN_WINDING_PROOF_11072026.lean` | [Winding numbers, Tier 1](PN_LEAN_WINDING_RESULTS_11072026.md) | 7 |  |
| `PN/PN_LEAN_WINDING_TIER2_PROOF_11072026.lean` | [Winding numbers, Tier 2 (the phase lift)](PN_LEAN_WINDING_TIER2_RESULTS_11072026.md) | 4 |  |
| `PN/PN_LEAN_Z10_BAND_PROOF_11072026.lean` | [The band under free evolution](PN_LEAN_Z10_BAND_RESULTS_11072026.md) | 4 |  |
| `PN/PN_LEAN_Z15_WITNESS_PROOF_11072026.lean` | [Witnesses for the Incompleteness Principle](PN_LEAN_Z15_WITNESS_RESULTS_11072026.md) | 7 |  |
| `PN/PN_LEAN_Z22_SKELETON_PROOF_11072026.lean` | [The Self-Identity Requirement: skeleton](PN_LEAN_Z22_SKELETON_RESULTS_11072026.md) | 12 | 1 |
| `PN/PN_LEAN_Z5_CLUSTER_PROOF_11072026.lean` | [The minimal model](PN_LEAN_Z5_CLUSTER_RESULTS_11072026.md) | 6 |  |
| `PN/PN_LEAN_Z5_TURN_RECEIPT_PROOF_11172026.lean` | [The qubit model beside the Turn](PN_LEAN_Z5_TURN_RECEIPT_RESULTS_11172026.md) | 6 |  |
| `PN/PN_LEAN_ZEROTH_LAW_PROOF_11072026.lean` | [The Zeroth PN Law](PN_LEAN_ZEROTH_LAW_RESULTS_11072026.md) | 10 |  |
| `PN/PN_LEAN_ZN1_PROOF_10292026.lean` | [Z-N.1 drift law, Tier 1 (algebra)](PN_LEAN_ZN1_RESULTS_10292026.md) | 3 |  |
| `PN/PN_LEAN_ZN1_TIER2_PROOF_11022026.lean` | [Z-N.1 drift law, Tier 2 (analysis)](PN_LEAN_ZN1_TIER2_RESULTS_11022026.md) | 3 |  |
| `PN/PN_LEAN_ZN2_SCHWARZ_PROOF_11022026.lean` | [Z-N.2 mixed partial, derived from smoothness](PN_LEAN_ZN2_SCHWARZ_RESULTS_11022026.md) | 1 |  |
| `PN/PN_LEAN_ZN2_TIER1_PROOF_11022026.lean` | [Z-N.2 sourced continuity and irremovability, Tier 1 (algebra)](PN_LEAN_ZN2_TIER1_RESULTS_11022026.md) | 4 |  |
| `PN/PN_LEAN_ZN2_TIER2_PROOF_11022026.lean` | [Z-N.2 sourced continuity and irremovability, Tier 2 (analysis)](PN_LEAN_ZN2_TIER2_RESULTS_11022026.md) | 6 |  |
| `PN/PN_LEAN_ZN3_TIER1_PROOF_11022026.lean` | [Z-N.3 metric chain](PN_LEAN_ZN3_TIER1_RESULTS_11022026.md) | 10 |  |
| `physlean/PN_LEAN_HIGGS_TIER2_PROOF_11072026.lean` | [The Higgs potential, Tier 2 (comparison with PhysLean)](PN_LEAN_HIGGS_TIER2_RESULTS_11072026.md) | 5 |  |
| `physlean/PN_LEAN_ZN1_TIER3A_PROOF_11022026.lean` | [Noether stage 1, Tier 3a: the lapse Lagrangian in PhysLean](PN_LEAN_ZN1_TIER3A_RESULTS_11022026.md) | 0 | 1 |
| `physlean/PN_LEAN_ZN1_TIER3_PROOF_11022026.lean` | [Noether stage 1, Tier 3: from the action principle to the drift law](PN_LEAN_ZN1_TIER3_RESULTS_11022026.md) | 6 |  |
| `physlean/PN_LEAN_ZN2_TIER3_PROOF_11022026.lean` | [Noether stage 2, Tier 3: the field action principle](PN_LEAN_ZN2_TIER3_RESULTS_11022026.md) | 10 | 1 |
| **33 files** (29 in `PN/`, 4 in `physlean/`) | **33 records** | **225** | **3** |

Three files also restate theorems that are counted in an earlier file, so that later results can build on them: the Tier 2 files for the Coherence-Relative Velocity Law and for winding numbers, and the Noether stage 1 Tier 3 file, which contains the Tier 3a construction. Their records list the restated items under "Also audited in this file (not counted)".
