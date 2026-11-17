/-
PN — THE LEDGER/TURN TOWER, `must_turn_v2` (THE FLOOR SQUEEZE)
11/09/2026 · Lean 4 + mathlib · repairs a recorded defect in `must_turn` (11/04).

Authority (canon Ch10 §6, read at source in COMPILATION 11022026 v1):
"The field cannot answer a blocked outlet by going still ... because Mu and
Law 1 together forbid the update rate from ever reaching zero. So the field
is caught: maximum activity, no room left to fall, no permission to stop."
Ruling (the author, 11/09): activity is tempo, not net flow; the turn mechanism is
formalized as a RATE bound on the drift, named `floor_squeeze`.

Setting: drift D := G − D_loss, with Ċ = D (hGL). New named data: D′, the
drift's own derivative (hD'), continuous (hD'c).

NAMED HYPOTHESIS `floor_squeeze` (hsq): for t ≥ 0, while C ≤ C_min + δ, the
drift is driven upward at rate at least ε:  ε ≤ D′(t).
It is assumed, not derived. The Mu floor is NOT a hypothesis of any theorem
in the contract part of this file; no proof below needs it.

CONTRACT (flight packet 11/09):
  must_turn_v2     — a time with Ċ > 0 exists inside an explicit window
                     after entry
  turn_time_bound  — a non-rising entrant's drift reaches zero within
                     |D(t₁)|/ε

ADDITIONS (beyond the contract; offered for ruling):
  turn_in_zone                   — the FIRST zero of the drift: it lies in
                                   the window, the field is still in the
                                   zone there, and it never rose before it
  activity_forms_exclusive       — v1's `floor_activity` and v2's
                                   `floor_squeeze` cannot both hold of a
                                   field that is non-rising in the zone
  squeeze_admits_falling_entrant — an explicit model satisfying every v2
                                   hypothesis together with the Mu floor,
                                   G ≥ 0, D_loss ≥ 0, and a falling entry
-/
import Mathlib

namespace PNLedgerV2

open intervalIntegral

variable (C G Dl D' : ℝ → ℝ) (Cmin : ℝ)

/-- A non-rising stretch cannot raise the field: if Ċ ≤ 0 on [a, b] then
C(b) ≤ C(a). -/
lemma nonrising_stays
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (a b : ℝ) (hab : a ≤ b)
    (hnp : ∀ s ∈ Set.Icc a b, G s - Dl s ≤ 0) :
    C b ≤ C a := by
  have hint : ∫ s in a..b, (G s - Dl s) = C b - C a :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hGL s)
      ((hGc.sub hDc).intervalIntegrable a b)
  have hle : (∫ s in a..b, (G s - Dl s)) ≤ ∫ _s in a..b, (0:ℝ) := by
    apply integral_mono_on hab ((hGc.sub hDc).intervalIntegrable a b)
      intervalIntegrable_const
    intro s hs
    exact hnp s hs
  rw [integral_const, smul_eq_mul, mul_zero] at hle
  linarith

/-- A squeezed stretch lifts the drift: if D′ ≥ ε on [a, b] then
D(a) + (b − a)·ε ≤ D(b). -/
lemma drift_gain
    (hD' : ∀ t, HasDerivAt (fun s => G s - Dl s) (D' t) t)
    (hD'c : Continuous D')
    (ε a b : ℝ) (hab : a ≤ b)
    (hsq : ∀ s ∈ Set.Icc a b, ε ≤ D' s) :
    (G a - Dl a) + (b - a) * ε ≤ G b - Dl b := by
  have hint : ∫ s in a..b, D' s = (G b - Dl b) - (G a - Dl a) :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hD' s)
      (hD'c.intervalIntegrable a b)
  have hle : (∫ _s in a..b, ε) ≤ ∫ s in a..b, D' s := by
    apply integral_mono_on hab intervalIntegrable_const
      (hD'c.intervalIntegrable a b)
    intro s hs
    exact hsq s hs
  rw [integral_const, smul_eq_mul] at hle
  linarith

/-! ## The contract -/

/-- **MUST TURN, v2.** A field in the zone at t₁ ≥ 0, under the floor
squeeze, has strictly positive drift at some time in the explicit window
[t₁, t₁ + max(0, −D(t₁))/ε + 1]. No floor hypothesis is used. -/
theorem must_turn_v2
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hD' : ∀ t, HasDerivAt (fun s => G s - Dl s) (D' t) t)
    (hD'c : Continuous D')
    (δ ε : ℝ) (hε : 0 < ε)
    (hsq : ∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε ≤ D' t)
    (t₁ : ℝ) (ht₁ : 0 ≤ t₁) (hnear : C t₁ ≤ Cmin + δ) :
    ∃ t ∈ Set.Icc t₁ (t₁ + max 0 (-(G t₁ - Dl t₁)) / ε + 1),
      0 < G t - Dl t := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  set T := t₁ + max 0 (-(G t₁ - Dl t₁)) / ε + 1 with hT
  have hm : 0 ≤ max 0 (-(G t₁ - Dl t₁)) := le_max_left _ _
  have hT1 : t₁ ≤ T := by
    have h0 : 0 ≤ max 0 (-(G t₁ - Dl t₁)) / ε := div_nonneg hm hε.le
    linarith
  have hzone : ∀ s ∈ Set.Icc t₁ T, ε ≤ D' s := by
    intro s hs
    have hCs : C s ≤ C t₁ :=
      nonrising_stays C G Dl hGL hGc hDc t₁ s hs.1
        (fun u hu => hcon u ⟨hu.1, le_trans hu.2 hs.2⟩)
    exact hsq s (le_trans ht₁ hs.1) (le_trans hCs hnear)
  have hgain := drift_gain G Dl D' hD' hD'c ε t₁ T hT1 hzone
  have hDT : G T - Dl T ≤ 0 := hcon T ⟨hT1, le_refl T⟩
  have hTe : (T - t₁) * ε = max 0 (-(G t₁ - Dl t₁)) + ε := by
    rw [hT]
    field_simp
    ring
  have hmax : -(G t₁ - Dl t₁) ≤ max 0 (-(G t₁ - Dl t₁)) := le_max_right _ _
  linarith

/-- **THE TURN-TIME BOUND.** A non-rising entrant (D(t₁) ≤ 0) under the
floor squeeze has its drift reach zero no later than t₁ + |D(t₁)|/ε. -/
theorem turn_time_bound
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hD' : ∀ t, HasDerivAt (fun s => G s - Dl s) (D' t) t)
    (hD'c : Continuous D')
    (δ ε : ℝ) (hε : 0 < ε)
    (hsq : ∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε ≤ D' t)
    (t₁ : ℝ) (ht₁ : 0 ≤ t₁) (hnear : C t₁ ≤ Cmin + δ)
    (hfall : G t₁ - Dl t₁ ≤ 0) :
    ∃ t ∈ Set.Icc t₁ (t₁ + (-(G t₁ - Dl t₁)) / ε), G t - Dl t = 0 := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  set T := t₁ + (-(G t₁ - Dl t₁)) / ε with hT
  have hT1 : t₁ ≤ T := by
    have h0 : 0 ≤ (-(G t₁ - Dl t₁)) / ε := div_nonneg (by linarith) hε.le
    linarith
  have hneg : ∀ s ∈ Set.Icc t₁ T, G s - Dl s < 0 := by
    intro s hs
    by_contra hns
    have hns' : 0 ≤ G s - Dl s := not_lt.mp hns
    have h0mem : (0:ℝ) ∈ Set.Icc (G t₁ - Dl t₁) (G s - Dl s) := ⟨hfall, hns'⟩
    obtain ⟨r, hr, hr0⟩ :=
      intermediate_value_Icc hs.1 (hGc.sub hDc).continuousOn h0mem
    exact hcon r ⟨hr.1, le_trans hr.2 hs.2⟩ hr0
  have hzone : ∀ s ∈ Set.Icc t₁ T, ε ≤ D' s := by
    intro s hs
    have hCs : C s ≤ C t₁ :=
      nonrising_stays C G Dl hGL hGc hDc t₁ s hs.1
        (fun u hu => (hneg u ⟨hu.1, le_trans hu.2 hs.2⟩).le)
    exact hsq s (le_trans ht₁ hs.1) (le_trans hCs hnear)
  have hgain := drift_gain G Dl D' hD' hD'c ε t₁ T hT1 hzone
  have hDT : G T - Dl T < 0 := hneg T ⟨hT1, le_refl T⟩
  have hTe : (T - t₁) * ε = -(G t₁ - Dl t₁) := by
    rw [hT]
    field_simp
    ring
  linarith

/-! ## Additions -/

/-- **THE TURN, LOCATED.** For a non-rising entrant under the floor squeeze
there is a FIRST time the drift vanishes: it lies within |D(t₁)|/ε of
entry, the field is still inside the zone there, and the field never rose
on the way. -/
theorem turn_in_zone
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hD' : ∀ t, HasDerivAt (fun s => G s - Dl s) (D' t) t)
    (hD'c : Continuous D')
    (δ ε : ℝ) (hε : 0 < ε)
    (hsq : ∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε ≤ D' t)
    (t₁ : ℝ) (ht₁ : 0 ≤ t₁) (hnear : C t₁ ≤ Cmin + δ)
    (hfall : G t₁ - Dl t₁ ≤ 0) :
    ∃ t ∈ Set.Icc t₁ (t₁ + (-(G t₁ - Dl t₁)) / ε),
      G t - Dl t = 0 ∧ C t ≤ Cmin + δ ∧
      ∀ s ∈ Set.Icc t₁ t, G s - Dl s ≤ 0 := by
  obtain ⟨t0, ht0, hz0⟩ :=
    turn_time_bound C G Dl D' Cmin hGL hGc hDc hD' hD'c δ ε hε hsq
      t₁ ht₁ hnear hfall
  set T := t₁ + (-(G t₁ - Dl t₁)) / ε with hT
  set Z : Set ℝ := Set.Icc t₁ T ∩ {t | G t - Dl t = 0} with hZ
  have hZc : IsClosed Z :=
    isClosed_Icc.inter (isClosed_eq (hGc.sub hDc) continuous_const)
  have hZne : Z.Nonempty := ⟨t0, ht0, hz0⟩
  have hZb : BddBelow Z := ⟨t₁, fun x hx => hx.1.1⟩
  have hs : sInf Z ∈ Z := hZc.csInf_mem hZne hZb
  have hbefore : ∀ u ∈ Set.Icc t₁ (sInf Z), G u - Dl u ≤ 0 := by
    intro u hu
    by_contra hpos
    have hpos' : 0 < G u - Dl u := not_le.mp hpos
    have h0mem : (0:ℝ) ∈ Set.Icc (G t₁ - Dl t₁) (G u - Dl u) :=
      ⟨hfall, hpos'.le⟩
    obtain ⟨r, hr, hr0⟩ :=
      intermediate_value_Icc hu.1 (hGc.sub hDc).continuousOn h0mem
    have hr0' : G r - Dl r = 0 := hr0
    have hrZ : r ∈ Z := ⟨⟨hr.1, le_trans hr.2 (le_trans hu.2 hs.1.2)⟩, hr0'⟩
    have hsr : sInf Z ≤ r := csInf_le hZb hrZ
    have hur : u = r := le_antisymm (le_trans hu.2 hsr) hr.2
    rw [hur] at hpos'
    linarith
  refine ⟨sInf Z, hs.1, hs.2, ?_, hbefore⟩
  have hCs : C (sInf Z) ≤ C t₁ :=
    nonrising_stays C G Dl hGL hGc hDc t₁ (sInf Z) hs.1.1 hbefore
  exact le_trans hCs hnear

/-- **v1 AND v2 ARE ALTERNATIVES, NOT A PAIR, FOR A FALLING ENTRANT.**
v1's `floor_activity` (|Ċ| ≥ ε′ throughout the zone) and v2's
`floor_squeeze` cannot both hold of a field that is non-rising in the zone
at some t₁ ≥ 0: the squeeze carries the drift through zero inside the zone,
which is the one value floor_activity forbids there. -/
theorem activity_forms_exclusive
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hD' : ∀ t, HasDerivAt (fun s => G s - Dl s) (D' t) t)
    (hD'c : Continuous D')
    (δ ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε')
    (hsq : ∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε ≤ D' t)
    (hFA : ∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε' ≤ |G t - Dl t|)
    (t₁ : ℝ) (ht₁ : 0 ≤ t₁) (hnear : C t₁ ≤ Cmin + δ)
    (hfall : G t₁ - Dl t₁ ≤ 0) :
    False := by
  obtain ⟨t, ht, h0, hz, -⟩ :=
    turn_in_zone C G Dl D' Cmin hGL hGc hDc hD' hD'c δ ε hε hsq
      t₁ ht₁ hnear hfall
  have h := hFA t (le_trans ht₁ ht.1) hz
  rw [h0, abs_zero] at h
  linarith

/-- **THE HYPOTHESES ARE JOINTLY SATISFIABLE WITH A FALLING ENTRY.** An
explicit model: C(t) = t²/2 − t + 3/4, G(t) = t² + t + 1, D_loss(t) = t² + 2,
so D(t) = t − 1 and D′ ≡ 1; C_min = 0, δ = 1, ε = 1, t₁ = 0. Every v2
hypothesis holds, the Mu floor holds for all time, G and D_loss are
nonnegative for all time, and the field enters the zone FALLING. This is
the defect v1 had and v2 does not. -/
theorem squeeze_admits_falling_entrant :
    ∃ (C G Dl D' : ℝ → ℝ) (Cmin δ ε t₁ : ℝ),
      (∀ t, HasDerivAt C (G t - Dl t) t) ∧ Continuous G ∧ Continuous Dl ∧
      (∀ t, HasDerivAt (fun s => G s - Dl s) (D' t) t) ∧ Continuous D' ∧
      0 < ε ∧ (∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε ≤ D' t) ∧
      0 ≤ t₁ ∧ C t₁ ≤ Cmin + δ ∧
      (∀ t, Cmin ≤ C t) ∧ (∀ t, 0 ≤ G t) ∧ (∀ t, 0 ≤ Dl t) ∧
      G t₁ - Dl t₁ < 0 := by
  refine ⟨fun t => t ^ 2 / 2 - t + 3 / 4, fun t => t ^ 2 + t + 1,
    fun t => t ^ 2 + 2, fun _ => 1, 0, 1, 1, 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := ((h2.div_const 2).sub (hasDerivAt_id' t)).add_const (3 / 4)
    exact h.congr_deriv (by ring)
  · fun_prop
  · fun_prop
  · intro t
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := ((h2.add (hasDerivAt_id' t)).add_const 1).sub (h2.add_const 2)
    exact h.congr_deriv (by ring)
  · exact continuous_const
  · norm_num
  · intro t _ _
    norm_num
  · norm_num
  · norm_num
  · intro t
    show (0:ℝ) ≤ t ^ 2 / 2 - t + 3 / 4
    nlinarith [sq_nonneg (t - 1)]
  · intro t
    show (0:ℝ) ≤ t ^ 2 + t + 1
    nlinarith [sq_nonneg (t + 1 / 2)]
  · intro t
    show (0:ℝ) ≤ t ^ 2 + 2
    positivity
  · norm_num

end PNLedgerV2

#print axioms PNLedgerV2.must_turn_v2
#print axioms PNLedgerV2.turn_time_bound
#print axioms PNLedgerV2.turn_in_zone
#print axioms PNLedgerV2.activity_forms_exclusive
#print axioms PNLedgerV2.squeeze_admits_falling_entrant

/-! ## Added by amendment (Ch6 review, ruled IN 11/09) — the scoped wall

  v1's `cannot_arrive` carried Perpetual Flow as a global clause
  (Ċ ≠ 0 at every t). Canon claims less and the proof uses less: the
  no-zero clause binds AT THE FLOOR (Ch10 §6: "At the floor, the net
  flow ... cannot be zero"); away from it Ċ = 0 is legal (Ch6 §1: Ċ
  "is NOT tempo"; v1's own `balance_patch`). Same proof body, with the
  hypothesis scoped to where canon prints it. v1's version stands; this
  is the canon-faithful face. -/

namespace PNLedgerV2

/-- **MU FORBIDS THE ARRIVAL — floor-scoped.** With the floor held, any
    touch of C_min is a local minimum, forcing the net flow to zero
    there; Perpetual Flow, claimed ONLY at the floor, forbids exactly
    that. So the field never reaches its floor. No clause about the net
    flow away from the floor is assumed. -/
theorem cannot_arrive_scoped (C G Dl : ℝ → ℝ) (Cmin : ℝ)
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hfloor : ∀ t, Cmin ≤ C t)
    (hPF : ∀ t, C t = Cmin → G t - Dl t ≠ 0) (t : ℝ) :
    Cmin < C t := by
  rcases lt_or_eq_of_le (hfloor t) with h | h
  · exact h
  · exfalso
    have hmin : IsLocalMin C t := by
      apply Filter.Eventually.of_forall
      intro y
      rw [← h]
      exact hfloor y
    exact hPF t h.symm (hmin.hasDerivAt_eq_zero (hGL t))

/-- **The scoping is real, not cosmetic:** a field that satisfies the
    floor-scoped clause while violating v1's global one. C = t² + 1
    over floor 0 never touches its floor (so the scoped clause holds
    vacuously) yet its net flow 2t vanishes at t = 0 — a legal rest
    away from the floor that v1's hypothesis would have forbidden. -/
theorem scoped_strictly_weaker :
    ∃ (C G Dl : ℝ → ℝ) (Cmin : ℝ),
      (∀ t, HasDerivAt C (G t - Dl t) t) ∧ (∀ t, Cmin ≤ C t) ∧
      (∀ t, C t = Cmin → G t - Dl t ≠ 0) ∧ ¬ (∀ t, G t - Dl t ≠ 0) := by
  refine ⟨fun t => t ^ 2 + 1, fun t => 2 * t, fun _ => 0, 0, ?_, ?_, ?_, ?_⟩
  · intro t
    have h := (hasDerivAt_pow 2 t).add_const (1:ℝ)
    simpa using h
  · intro t
    positivity
  · intro t ht
    exfalso
    have : (0:ℝ) < t ^ 2 + 1 := by positivity
    simp only at ht
    linarith
  · intro h
    exact h 0 (by simp)

end PNLedgerV2

#print axioms PNLedgerV2.cannot_arrive_scoped
#print axioms PNLedgerV2.scoped_strictly_weaker
