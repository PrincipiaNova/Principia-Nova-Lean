/-
═══════════════════════════════════════════════════════════════════════════════
PN — WHY A TURN NEEDS A SECOND VARIABLE · v2, STRENGTHENED · 11/17/2026
Lean 4 + mathlib · supersedes the uncompiled 11/09 draft (theorems 1 and 3
carried unchanged; theorem 2 strengthened per the reviewed proof plan
PN_SECOND_VARIABLE_THM2_PROOF_PLAN_11172026 — plan independently
written and reviewed, approved 11/17, ruled by the author).

Framework-free: no PN premise appears in any signature. The content is
classical; what is offered is its bearing on the Turn (doc-level).

  first_order_rest_is_forever : for LIPSCHITZ F — if the drift ever
      vanishes, the field is constant for all time. (Keeps its hypothesis:
      Norton's-dome-type laws genuinely break it — see the door below.)
  first_order_cannot_turn     : for ANY F, however badly behaved — the
      drift can never be negative at one time and positive at another.
      No regularity on F at all; the only assumption is that C solves
      the law. (The strengthening: falling-then-rising means crossing a
      level twice with opposite slopes, and the slope at a level is fixed
      by the level.)
  two_variables_can_turn      : the matched door — with the drift promoted
      to its own state a falling field turns.
  rest_needs_smoothness       : the dome door — C = t³ solves Ċ = 3|C|^(2/3),
      rests for exactly one instant, and moves on: theorem 1's Lipschitz
      hypothesis is load-bearing. (With theorem 1, this also proves this F
      admits no Lipschitz constant — no separate non-Lipschitz proof needed.)

Bearing on the Turn (doc-level, no weld claimed): C alone cannot turn; the
engine that turns a field must carry state beyond C — tempo, direction,
relation. The qubit room's arrow is this theorem wearing physical clothes.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNSecondVariable

/-- **Rest is forever in one variable — for Lipschitz laws.** If Ċ = F(C)
with F Lipschitz and the drift vanishes at a single instant, then C is
constant at all times. A smooth first-order state law has no "momentary"
zero of the drift. (The hypothesis is load-bearing: see
`rest_needs_smoothness`.) -/
theorem first_order_rest_is_forever (F : ℝ → ℝ) (K : NNReal)
    (hF : LipschitzWith K F) (C : ℝ → ℝ)
    (hC : ∀ t, HasDerivAt C (F (C t)) t)
    (t₀ : ℝ) (h0 : F (C t₀) = 0) :
    ∀ t, C t = C t₀ := by
  have h := ODE_solution_unique_univ (v := fun _ => F) (s := fun _ => Set.univ)
    (K := K) (f := C) (g := fun _ => C t₀) (t₀ := t₀)
    (fun _ => hF.lipschitzOnWith)
    (fun t => ⟨hC t, Set.mem_univ _⟩)
    (fun t => ⟨by
      have hc := hasDerivAt_const t (C t₀)
      simpa [h0] using hc, Set.mem_univ _⟩)
    rfl
  intro t
  exact congrFun h t

/-- Helper (uncounted) — **the one-way gate.** A level with positive drift,
once reached from at-or-above, is never revisited: for ANY F. (This alone is
the classical monotonicity of scalar autonomous flows.) -/
lemma up_gate (F : ℝ → ℝ) (C : ℝ → ℝ)
    (hC : ∀ t, HasDerivAt C (F (C t)) t)
    (b : ℝ) (hb : 0 < F b)
    (p q : ℝ) (hpq : p < q) (hp : b ≤ C p) :
    b < C q := by
  have hCc : Continuous C :=
    continuous_iff_continuousAt.mpr fun x => (hC x).continuousAt
  -- Stage 1: find p' ∈ [p, q) with b < C p'
  obtain ⟨p', hpp', hp'q, hbp'⟩ :
      ∃ p', p ≤ p' ∧ p' < q ∧ b < C p' := by
    rcases lt_or_eq_of_le hp with hlt | heq
    · exact ⟨p, le_refl p, hpq, hlt⟩
    · -- C p = b exactly; escape upward using the positive derivative
      have hb' : 0 < F (C p) := by rw [← heq]; exact hb
      have hslope := hasDerivAt_iff_tendsto_slope.mp (hC p)
      have hev : ∀ᶠ u in nhdsWithin p {p}ᶜ, 0 < slope C p u :=
        hslope.eventually (eventually_gt_nhds hb')
      have hev' : ∀ᶠ u in nhdsWithin p (Set.Ioi p), 0 < slope C p u :=
        hev.filter_mono (nhdsWithin_mono p fun x hx => ne_of_gt hx)
      have hmem : Set.Ioo p q ∈ nhdsWithin p (Set.Ioi p) :=
        Ioo_mem_nhdsGT hpq
      obtain ⟨u, hu_slope, hu_mem⟩ :=
        (hev'.and (Filter.eventually_of_mem hmem fun u hu => hu)).exists
      refine ⟨u, hu_mem.1.le, hu_mem.2, ?_⟩
      have hup : 0 < u - p := sub_pos.mpr hu_mem.1
      have := mul_pos hu_slope hup
      rw [slope_def_field] at this
      rw [div_mul_cancel₀ _ (ne_of_gt hup)] at this
      rw [heq]
      linarith
  -- Stage 2: no return to b
  by_contra hq
  rw [not_lt] at hq
  -- hq : C q ≤ b
  set S : Set ℝ := Set.Icc p' q ∩ {u | C u ≤ b} with hS
  have hSc : IsClosed S :=
    isClosed_Icc.inter (isClosed_le hCc continuous_const)
  have hSne : S.Nonempty := ⟨q, ⟨hp'q.le, le_refl q⟩, hq⟩
  have hSbdd : BddBelow S := ⟨p', fun x hx => hx.1.1⟩
  have hu₀ : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  set u₀ := sInf S with hu₀def
  have hp'u₀ : p' < u₀ := by
    rcases lt_or_eq_of_le hu₀.1.1 with h | h
    · exact h
    · exfalso
      have : C u₀ ≤ b := hu₀.2
      rw [← h] at this
      linarith
  have habove : ∀ u ∈ Set.Ico p' u₀, b < C u := by
    intro u hu
    by_contra hle
    rw [not_lt] at hle
    have huS : u ∈ S := ⟨⟨hu.1, le_trans hu.2.le hu₀.1.2⟩, hle⟩
    have := csInf_le hSbdd huS
    exact absurd this (not_le.mpr hu.2)
  have hCu₀ : C u₀ = b := by
    have hge : b ≤ C u₀ := by
      have htend : Filter.Tendsto C (nhdsWithin u₀ (Set.Iio u₀)) (nhds (C u₀)) :=
        (hCc.tendsto u₀).mono_left nhdsWithin_le_nhds
      have hmem : Set.Ico p' u₀ ∈ nhdsWithin u₀ (Set.Iio u₀) :=
        Ico_mem_nhdsLT hp'u₀
      exact ge_of_tendsto htend
        (Filter.eventually_of_mem hmem fun u hu => (habove u hu).le)
    exact le_antisymm hu₀.2 hge
  -- the derivative at u₀ is F b > 0, but the left slopes are negative
  have hd := hC u₀
  rw [hCu₀] at hd
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hslope' : Filter.Tendsto (slope C u₀) (nhdsWithin u₀ (Set.Iio u₀))
      (nhds (F b)) :=
    hslope.mono_left (nhdsWithin_mono u₀ fun x hx => ne_of_lt hx)
  have hmem : Set.Ico p' u₀ ∈ nhdsWithin u₀ (Set.Iio u₀) :=
    Ico_mem_nhdsLT hp'u₀
  have hnegslope : ∀ᶠ u in nhdsWithin u₀ (Set.Iio u₀), slope C u₀ u ≤ 0 := by
    refine Filter.eventually_of_mem hmem fun u hu => ?_
    rw [slope_def_field]
    have hnum : 0 < C u - C u₀ := by
      rw [hCu₀]
      exact sub_pos.mpr (habove u hu)
    have hden : u - u₀ < 0 := sub_neg.mpr hu.2
    exact (div_neg_of_pos_of_neg hnum hden).le
  have := le_of_tendsto hslope' hnegslope
  linarith

/-- Helper (uncounted) — **the mirror gate**, by the negation transform. -/
lemma down_gate (F : ℝ → ℝ) (C : ℝ → ℝ)
    (hC : ∀ t, HasDerivAt C (F (C t)) t)
    (a : ℝ) (ha : F a < 0)
    (p q : ℝ) (hpq : p < q) (hp : C p ≤ a) :
    C q < a := by
  have hC' : ∀ t, HasDerivAt (fun τ => -C τ) ((fun x => -F (-x)) (-C t)) t := by
    intro t
    have hval : (fun x => -F (-x)) (-C t) = -(F (C t)) := by
      simp only [neg_neg]
    rw [hval]
    exact (hC t).neg
  have hb : 0 < (fun x => -F (-x)) (-a) := by
    simp only [neg_neg]
    linarith
  have hp' : -a ≤ -C p := neg_le_neg hp
  have h := up_gate (fun x => -F (-x)) (fun τ => -C τ) hC' (-a) hb p q hpq hp'
  linarith

/-- **One variable cannot turn — for ANY law.** Under Ċ = F(C) with F an
ARBITRARY function — no continuity, no Lipschitz, nothing — the drift is
never negative at one time and positive at another. No fall-then-rise, and
no rise-then-fall. Falling and then rising would cross one level twice with
opposite slopes, and the slope at a level is fixed by the level. Whatever
turns a field carries state beyond its value. -/
theorem first_order_cannot_turn (F : ℝ → ℝ) (C : ℝ → ℝ)
    (hC : ∀ t, HasDerivAt C (F (C t)) t) :
    ¬ ∃ s t, F (C s) < 0 ∧ 0 < F (C t) := by
  rintro ⟨s, t, hneg, hpos⟩
  rcases lt_trichotomy s t with hst | hst | hst
  · -- falling first
    have h1 : C t < C s := down_gate F C hC (C s) hneg s t hst (le_refl _)
    have h2 : C t < C t := up_gate F C hC (C t) hpos s t hst h1.le
    exact lt_irrefl _ h2
  · rw [hst] at hneg
    linarith
  · -- rising first
    have h1 : C t < C s := up_gate F C hC (C t) hpos t s hst (le_refl _)
    have h2 : C s < C s := down_gate F C hC (C s) hneg t s hst h1.le
    exact lt_irrefl _ h2

/-- **Two variables can.** Promote the drift to its own state: Ċ = D, Ḋ = 1.
Then C(t) = t²/2 − t falls at t = 0, rests for one instant at t = 1, and
rises at t = 2 — a turn, with the zero of the drift momentary, not eternal. -/
theorem two_variables_can_turn :
    ∃ C D : ℝ → ℝ,
      (∀ t, HasDerivAt C (D t) t) ∧ (∀ t, HasDerivAt D 1 t) ∧
      D 0 < 0 ∧ D 1 = 0 ∧ 0 < D 2 := by
  refine ⟨fun t => t ^ 2 / 2 - t, fun t => t - 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := (h2.div_const 2).sub (hasDerivAt_id' t)
    exact h.congr_deriv (by ring)
  · intro t
    exact (hasDerivAt_id' t).sub_const 1
  · norm_num
  · norm_num
  · norm_num

/-- **The dome door — theorem 1's hypothesis is load-bearing.** C(t) = t³
solves Ċ = 3·|C|^(2/3); the drift vanishes at t = 0 — and the field moves
anyway: rest was momentary, not forever. By `first_order_rest_is_forever`,
this F therefore admits NO Lipschitz constant (no separate proof needed):
the Norton's-dome shape, as a witness. -/
theorem rest_needs_smoothness :
    ∃ F C : ℝ → ℝ, (∀ t, HasDerivAt C (F (C t)) t) ∧
      F (C 0) = 0 ∧ C 1 ≠ C 0 := by
  refine ⟨fun c => 3 * |c| ^ ((2 : ℝ) / 3), fun t => t ^ 3, ?_, ?_, ?_⟩
  · intro t
    have h : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    convert h using 1
    show 3 * |t ^ 3| ^ ((2 : ℝ) / 3) = 3 * t ^ 2
    rw [abs_pow, ← Real.rpow_natCast |t| 3, ← Real.rpow_mul (abs_nonneg t),
      show ((3 : ℕ) : ℝ) * (2 / 3) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]
  · show 3 * |(0 : ℝ) ^ 3| ^ ((2 : ℝ) / 3) = 0
    rw [show |(0 : ℝ) ^ 3| = 0 by norm_num,
      Real.zero_rpow (by norm_num : ((2 : ℝ) / 3) ≠ 0)]
    ring
  · norm_num

end PNSecondVariable

#print axioms PNSecondVariable.first_order_rest_is_forever
#print axioms PNSecondVariable.first_order_cannot_turn
#print axioms PNSecondVariable.two_variables_can_turn
#print axioms PNSecondVariable.rest_needs_smoothness
