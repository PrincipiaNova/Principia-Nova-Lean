/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE TURN RECEIPT · 11/17/2026 · Lean 4 + mathlib
Z §5's room ⇄ Ch10 §6's story: the qubit shows the Turn's shape
WITNESS-GRADE (discriminating_case species, Zeroth Movement 2 precedent)

Per flight packet PN_Z5_TURN_RECEIPT_FLIGHT_PACKET_11102026 (v4:
A1–A3 ratified, review tightenings in, all six theorems ruled by the author
11/17 — "go · model yes · A1–A3 · all six · Hike!").

MODEL (named, MODEL DATA — canon prints the channel split, not this
generator): Bloch relaxation toward the environment's state, ṙ = γ(s − r),
γ = 1 for witnesses. C(r) = (1 + ‖r‖²)/2 per canon Definition 1 (§5.1),
defined locally (standalone-workspace doctrine; matches the 11/07 file's
`Cbloch` exactly). NO Lindblad machinery claimed — mathlib has none; the
trajectories are explicit and elementary.

Authorities (verbatim, verified at source 11/10 & 11/17):
· §5.6: "This classification is instantaneous and state-relative: a
  channel's contribution depends on the state it acts on, not on a
  permanent identity."
· §5.1/Def 2: "C(ρ) = ½(1 + |r|²)... The pure surface and the dead center
  are excluded as limit states... asymptotes, approached and never occupied."
· §5.3 Thm 2: "...carried strictly into the interior... converges toward an
  interior stationary state."
· §5.4: "Totality is what Mu forbids — not participation."
· Ch10 §6's collision/trichotomy (in the must_turn_v2 packet, 11/09).

FENCES: single-channel loss column DEFINED (D_loss := negative part, per
§5.6's state-relative rule — review tightening 1); the room's sign-flip
decomposition stays in the ROOM's column (canon's arc split-agnostic per
the 11/09 ruling); no_dip guard sentence carried (review tightening 2);
tempo doc-level only; §5.7 roof cited wherever the room ends; the s = 0
exclusion stays PROSE (§5.4 purification; no fidelity donors — hedge
inheritance). Theorems consume NO prior PN file.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

open Real Filter
open scoped InnerProductSpace

namespace PNTurnReceipt

/-- The Bloch space, canon's minimal-model grain. -/
abbrev Bloch := EuclideanSpace ℝ (Fin 3)

/-- Canon Definition 1, defined locally: C(r) = (1 + ‖r‖²)/2. -/
noncomputable def Cof (v : Bloch) : ℝ := (1 + ‖v‖ ^ 2) / 2

noncomputable def e0 : Bloch := EuclideanSpace.single 0 1
noncomputable def e1 : Bloch := EuclideanSpace.single 1 1

/-! ## Helpers (uncounted): orthonormal frame facts, the relaxation solution -/

theorem ho : Orthonormal ℝ (fun i : Fin 3 => (EuclideanSpace.single i (1 : ℝ) : Bloch)) :=
  EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)

theorem e0_norm : ‖e0‖ = 1 := ho.1 0

theorem e1_norm : ‖e1‖ = 1 := ho.1 1

theorem inner_e0_e0 : ⟪e0, e0⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, e0_norm]; norm_num

theorem inner_e1_e1 : ⟪e1, e1⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, e1_norm]; norm_num

theorem inner_e0_e1 : ⟪e0, e1⟫_ℝ = 0 :=
  ho.2 (show (0 : Fin 3) ≠ 1 by decide)

theorem inner_e1_e0 : ⟪e1, e0⟫_ℝ = 0 := by
  rw [real_inner_comm]; exact inner_e0_e1

/-- ‖a·e0 + b·e1‖² = a² + b² (orthonormal expansion). -/
theorem norm_sq_combo (a b : ℝ) : ‖a • e0 + b • e1‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_e0_e0, inner_e0_e1, inner_e1_e0, inner_e1_e1]
  ring

/-- d/dt e^(−t) = −e^(−t). -/
theorem exp_neg_hasDeriv (t : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.exp (-τ)) (-Real.exp (-t)) t := by
  have h1 : HasDerivAt (fun τ : ℝ => -τ) (-1) t := hasDerivAt_neg' t
  have h2 := (Real.hasDerivAt_exp (-t)).comp t h1
  simp only [Function.comp_def] at h2
  convert h2 using 1
  ring

/-- **The relaxation solution**: r(t) = s + e^(−t)·w solves ṙ = s − r (γ = 1). -/
theorem relax_solves (s w : Bloch) (t : ℝ) :
    HasDerivAt (fun τ => s + Real.exp (-τ) • w) (s - (s + Real.exp (-t) • w)) t := by
  have h3 := (exp_neg_hasDeriv t).smul_const w
  have h4 := h3.const_add s
  have hval : (-Real.exp (-t)) • w = s - (s + Real.exp (-t) • w) := by
    rw [neg_smul]; abel
  rw [hval] at h4
  exact h4

/-! ## The dip trajectory (packet witness: s = (1/2,0,0), r₀ = (−1/4,1/4,0), γ = 1) -/

noncomputable def sD : Bloch := (1 / 2 : ℝ) • e0
noncomputable def wD : Bloch := (-(3 / 4) : ℝ) • e0 + (1 / 4 : ℝ) • e1
noncomputable def rD (t : ℝ) : Bloch := sD + Real.exp (-t) • wD

theorem rD_combo (t : ℝ) :
    rD t = (1 / 2 - (3 / 4) * Real.exp (-t)) • e0 + ((1 / 4) * Real.exp (-t)) • e1 := by
  unfold rD sD wD
  module

theorem rD_norm_sq (t : ℝ) :
    ‖rD t‖ ^ 2 = 1 / 4 - (3 / 4) * Real.exp (-t) + (5 / 8) * Real.exp (-t) ^ 2 := by
  rw [rD_combo, norm_sq_combo]
  ring

theorem CD_formula :
    (fun τ => Cof (rD τ)) =
      fun τ => 5 / 8 - (3 / 8) * Real.exp (-τ) + (5 / 16) * Real.exp (-τ) ^ 2 := by
  funext τ
  simp only [Cof, rD_norm_sq]
  ring

theorem CD_hasDeriv (t : ℝ) :
    HasDerivAt (fun τ => Cof (rD τ))
      ((3 / 8) * Real.exp (-t) - (5 / 8) * Real.exp (-t) ^ 2) t := by
  rw [CD_formula]
  have hexp := exp_neg_hasDeriv t
  have hsq := hexp.pow 2
  have h1 := hexp.const_mul (3 / 8 : ℝ)
  have h2 := hsq.const_mul (5 / 16 : ℝ)
  have h := ((hasDerivAt_const t (5 / 8 : ℝ)).sub h1).add h2
  convert h using 1
  ring

/-! ## The no-dip trajectory (r₀ = (3/4,0,0), same s) -/

noncomputable def wN : Bloch := (1 / 4 : ℝ) • e0
noncomputable def rN (t : ℝ) : Bloch := sD + Real.exp (-t) • wN

theorem rN_combo (t : ℝ) :
    rN t = (1 / 2 + (1 / 4) * Real.exp (-t)) • e0 + (0 : ℝ) • e1 := by
  unfold rN sD wN
  module

theorem rN_norm_sq (t : ℝ) :
    ‖rN t‖ ^ 2 = 1 / 4 + (1 / 4) * Real.exp (-t) + (1 / 16) * Real.exp (-t) ^ 2 := by
  rw [rN_combo, norm_sq_combo]
  ring

theorem CN_formula :
    (fun τ => Cof (rN τ)) =
      fun τ => 5 / 8 + (1 / 8) * Real.exp (-τ) + (1 / 32) * Real.exp (-τ) ^ 2 := by
  funext τ
  simp only [Cof, rN_norm_sq]
  ring

theorem CN_hasDeriv (t : ℝ) :
    HasDerivAt (fun τ => Cof (rN τ))
      (-((1 / 8) * Real.exp (-t)) - (1 / 16) * Real.exp (-t) ^ 2) t := by
  rw [CN_formula]
  have hexp := exp_neg_hasDeriv t
  have hsq := hexp.pow 2
  have h1 := hexp.const_mul (1 / 8 : ℝ)
  have h2 := hsq.const_mul (1 / 32 : ℝ)
  have h := ((hasDerivAt_const t (5 / 8 : ℝ)).add h1).add h2
  convert h using 1
  ring

/-! ## THE SIX THEOREMS -/

/-- **THEOREM 1 — the channel's identity is state-relative.** Canon §5.6:
"This classification is instantaneous and state-relative: a channel's
contribution depends on the state it acts on, not on a permanent identity."
The SAME relaxation channel (pull toward s), read through Ċ = ⟪r, s − r⟫, is
GENERATIVE at one interior state and DECOHERING at another — explicit
witnesses both ways, all states strictly inside the Mu region. -/
theorem channel_identity_state_relative :
    ∃ s r₁ r₂ : Bloch, ‖s‖ < 1 ∧ ‖r₁‖ < 1 ∧ ‖r₂‖ < 1 ∧
      0 < ⟪r₁, s - r₁⟫_ℝ ∧ ⟪r₂, s - r₂⟫_ℝ < 0 := by
  refine ⟨(1 / 2 : ℝ) • e0, (1 / 4 : ℝ) • e0, (3 / 4 : ℝ) • e0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, e0_norm, mul_one, Real.norm_eq_abs]; norm_num
  · rw [norm_smul, e0_norm, mul_one, Real.norm_eq_abs]; norm_num
  · rw [norm_smul, e0_norm, mul_one, Real.norm_eq_abs]; norm_num
  · have hs : (1 / 2 : ℝ) • e0 - (1 / 4 : ℝ) • e0 = (1 / 4 : ℝ) • e0 := by
      rw [← sub_smul]; norm_num
    rw [hs, real_inner_smul_left, real_inner_smul_right, inner_e0_e0]
    norm_num
  · have hs : (1 / 2 : ℝ) • e0 - (3 / 4 : ℝ) • e0 = (-(1 / 4) : ℝ) • e0 := by
      rw [← sub_smul]; norm_num
    rw [hs, real_inner_smul_left, real_inner_smul_right, inner_e0_e0]
    norm_num

/-- **THEOREM 2 — the drain is bounded by the arrow** (A2 discharged, loss
column DEFINED per the review). The single channel's contribution to Ċ
is γ⟪r, s−r⟫; per §5.6's state-relative rule its LOSS column is the negative
part max(0, −Ċ) and its GAIN column the positive part. BOTH are bounded by
γ‖r‖(‖s‖+‖r‖) → 0 as the arrow shrinks: "you cannot drain a field that has
nothing left to give" — DERIVED (Cauchy–Schwarz + triangle), not assumed.
General inner-product space; the Bloch instance is a special case. -/
theorem drain_bounded_by_arrow {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (γ : ℝ) (hγ : 0 ≤ γ) (r s : V) :
    max 0 (-(γ * ⟪r, s - r⟫_ℝ)) ≤ γ * (‖r‖ * (‖s‖ + ‖r‖)) ∧
    max 0 (γ * ⟪r, s - r⟫_ℝ) ≤ γ * (‖r‖ * (‖s‖ + ‖r‖)) := by
  have hbound : |⟪r, s - r⟫_ℝ| ≤ ‖r‖ * (‖s‖ + ‖r‖) := by
    calc |⟪r, s - r⟫_ℝ| ≤ ‖r‖ * ‖s - r‖ := abs_real_inner_le_norm r (s - r)
      _ ≤ ‖r‖ * (‖s‖ + ‖r‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le s r) (norm_nonneg r)
  have hB : 0 ≤ γ * (‖r‖ * (‖s‖ + ‖r‖)) := mul_nonneg hγ (by positivity)
  constructor
  · refine max_le hB ?_
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (le_trans (neg_le_abs _) hbound) hγ
  · refine max_le hB ?_
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hbound) hγ

/-- **THEOREM 3 — the arrow turns** (the dip witness, packet numbers).
s = (1/2,0,0), r₀ = (−1/4,1/4,0), γ = 1. The trajectory SOLVES the model
exactly; coherence enters FALLING (C(0) = 9/16, Ċ(0) = −1/4 < 0), rests for
one instant at t* = ln(5/3) (Ċ(t*) = 0, momentary not eternal), RISES at
every later time, and MISSES the center: ‖r(t)‖² ≥ 1/40 > 0 always —
approach, blocked drain, turn in the zone, floor never touched. -/
theorem arrow_turns_witness :
    (∀ t, HasDerivAt rD (sD - rD t) t) ∧
    (Cof (rD 0) = 9 / 16) ∧
    HasDerivAt (fun τ => Cof (rD τ)) (-(1 / 4)) 0 ∧
    HasDerivAt (fun τ => Cof (rD τ)) 0 (Real.log (5 / 3)) ∧
    (∀ t, Real.log (5 / 3) < t →
      ∃ d, 0 < d ∧ HasDerivAt (fun τ => Cof (rD τ)) d t) ∧
    (∀ t, (1 : ℝ) / 40 ≤ ‖rD t‖ ^ 2) := by
  have hE : Real.exp (-Real.log (5 / 3)) = 3 / 5 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5 / 3)]
    norm_num
  refine ⟨fun t => relax_solves sD wD t, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Cof, rD_norm_sq]
    rw [neg_zero, Real.exp_zero]
    norm_num
  · have h := CD_hasDeriv 0
    rw [neg_zero, Real.exp_zero] at h
    norm_num at h
    exact h
  · have h := CD_hasDeriv (Real.log (5 / 3))
    rw [hE] at h
    norm_num at h
    exact h
  · intro t ht
    refine ⟨(3 / 8) * Real.exp (-t) - (5 / 8) * Real.exp (-t) ^ 2, ?_, CD_hasDeriv t⟩
    have hlt : Real.exp (-t) < 3 / 5 := by
      have := Real.exp_lt_exp.mpr (show -t < -Real.log (5 / 3) by linarith)
      rwa [hE] at this
    have hpos := Real.exp_pos (-t)
    nlinarith
  · intro t
    rw [rD_norm_sq]
    nlinarith [sq_nonneg (Real.exp (-t) - 3 / 5)]

/-- **THEOREM 4 — the no-dip witness** (matched door: not every start turns).
r₀ = (3/4,0,0), same s: the trajectory solves the model, enters at
C(0) = 25/32, and its coherence FALLS at every time — no dip, no turn, a
monotone glide. **GUARD (per packet v4): this is NOT a counterexample
to the Turn.** The glide descends toward an interior resting value of 5/8,
strictly above 5/8 at all finite times and nowhere near the floor ½; it
never enters a floor zone and no squeeze operates, so must_turn_v2's
hypotheses are simply not in force. Not every start turns because not every
start is a falling entrant. -/
theorem no_dip_witness :
    (∀ t, HasDerivAt rN (sD - rN t) t) ∧
    (Cof (rN 0) = 25 / 32) ∧
    (∀ t, ∃ d, d < 0 ∧ HasDerivAt (fun τ => Cof (rN τ)) d t) ∧
    (∀ t, 5 / 8 < Cof (rN t)) := by
  refine ⟨fun t => relax_solves sD wN t, ?_, ?_, ?_⟩
  · simp only [Cof, rN_norm_sq]
    rw [neg_zero, Real.exp_zero]
    norm_num
  · intro t
    refine ⟨-((1 / 8) * Real.exp (-t)) - (1 / 16) * Real.exp (-t) ^ 2, ?_, CN_hasDeriv t⟩
    have hpos := Real.exp_pos (-t)
    nlinarith
  · intro t
    simp only [Cof, rN_norm_sq]
    have hpos := Real.exp_pos (-t)
    nlinarith

/-- **THEOREM 5 — the anchor glide** (Theorem 2's "converges toward,"
exhibited; the ceiling_persistence SHAPE). After its turn the dip trajectory
climbs toward the stationary value 5/8 and NEVER arrives: C(t) < 5/8 at
every t ≥ 0, with C(t) → 5/8 — ever-smaller nonzero change, the
asymptote-not-arrival species' 7th appearance. Perpetual-Flow-compliant
rest-approach: the room's anchor half of Ch10's mirror. -/
theorem anchor_glide :
    (∀ t, 0 ≤ t → Cof (rD t) < 5 / 8) ∧
    Tendsto (fun t => Cof (rD t)) atTop (nhds (5 / 8)) := by
  constructor
  · intro t ht
    simp only [Cof, rD_norm_sq]
    have hpos := Real.exp_pos (-t)
    have hle : Real.exp (-t) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith
  · rw [CD_formula]
    have htend : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hcont : Continuous (fun x : ℝ => 5 / 8 - (3 / 8) * x + (5 / 16) * x ^ 2) := by
      continuity
    have h := (hcont.tendsto 0).comp htend
    simp only [Function.comp_def] at h
    convert h using 2
    norm_num

/-- **THEOREM 6 — merger is a limit state** (the s = 0 door: environment
resting at the dead center). The trajectory solves ṙ = −r (the model with
s = 0); coherence stays STRICTLY above the floor ½ at every finite time and
tends to ½ — the eternal thinning exists in the UNFENCED model as an
asymptote only (8th appearance of the species). What EXCLUDES s = 0 as a
physical environment is §5.4's printed merger bound ("no system is ever
perfectly merged... Totality is what Mu forbids") — that exclusion stays
PROSE (purification argument; no fidelity donors; hedge inheritance). -/
theorem merger_is_limit_state (r₀ : Bloch) (hr₀ : r₀ ≠ 0) :
    (∀ t, HasDerivAt (fun τ => Real.exp (-τ) • r₀) (-(Real.exp (-t) • r₀)) t) ∧
    (∀ t, 1 / 2 < Cof (Real.exp (-t) • r₀)) ∧
    Tendsto (fun t => Cof (Real.exp (-t) • r₀)) atTop (nhds (1 / 2)) := by
  have hnorm : ∀ t, ‖Real.exp (-t) • r₀‖ ^ 2 = Real.exp (-t) ^ 2 * ‖r₀‖ ^ 2 := by
    intro t
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hr₀pos : 0 < ‖r₀‖ ^ 2 := by
    have := norm_pos_iff.mpr hr₀
    positivity
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have h := (exp_neg_hasDeriv t).smul_const r₀
    rwa [neg_smul] at h
  · intro t
    simp only [Cof, hnorm]
    nlinarith [mul_pos (pow_pos (Real.exp_pos (-t)) 2) hr₀pos]
  · have hfun : (fun t => Cof (Real.exp (-t) • r₀)) =
        fun t => (1 + Real.exp (-t) ^ 2 * ‖r₀‖ ^ 2) / 2 := by
      funext t
      simp only [Cof, hnorm]
    rw [hfun]
    have htend : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    have hcont : Continuous (fun x : ℝ => (1 + x ^ 2 * ‖r₀‖ ^ 2) / 2) := by
      continuity
    have h := (hcont.tendsto 0).comp htend
    simp only [Function.comp_def] at h
    convert h using 2
    norm_num

end PNTurnReceipt

#print axioms PNTurnReceipt.channel_identity_state_relative
#print axioms PNTurnReceipt.drain_bounded_by_arrow
#print axioms PNTurnReceipt.arrow_turns_witness
#print axioms PNTurnReceipt.no_dip_witness
#print axioms PNTurnReceipt.anchor_glide
#print axioms PNTurnReceipt.merger_is_limit_state
