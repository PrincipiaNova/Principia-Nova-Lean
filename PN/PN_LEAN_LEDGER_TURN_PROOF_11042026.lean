/-
  PRINCIPIA NOVA — THE LEDGER/TURN TOWER, KERNEL-CERTIFIED
  11/04/2026 · Lean 4 + mathlib · Ch7 (the PN thermodynamic ledger),
  Ch8 §6 (the Generative Law's signs), Ch10 §6 (the Turn).

  The certified drift form dC/dt = G − D_loss (the Z-N program's raw
  material) integrated into the book's thermodynamic story: the budget,
  the arrow, the bound — and the Turn at the floor, by trichotomy,
  exactly as §10.6 prints it: "it cannot be negative — that would carry
  C beneath C_min, which Mu forbids. And it cannot be zero — a resting
  field is a still field, which Perpetual Flow forbids. Every value is
  ruled out but one. dC/dt must be positive."

  NAMED HYPOTHESES (the fences): G ≥ 0, D_loss ≥ 0 (Ch8 §6,
  axiom-grade, underived as ever); the Mu floor C ≥ C_min; Perpetual
  Flow as the nonzero-derivative clause; floor_activity (|Ċ| ≥ ε near
  the floor — §10.6's "maximum activity, no room left to fall, no
  permission to stop"; named now, derivable later from the tempo law);
  continuity for the FTC steps; uniform-patch time functions
  (position-dependence settled at N-2). S_max's full convergence stays
  Ch10's cosmological claim — only its honest budget bound is certified
  (ledger_dominated). The mirror note (floor_activity absent at the
  ceiling) lives in the results doc.
-/
import Mathlib

namespace PNLedger

open intervalIntegral Filter Topology

variable (C G Dl : ℝ → ℝ) (Cmin : ℝ)

/-! ## Stage 1 — the ledger -/

/-- **THE BUDGET IDENTITY:** integrate the certified drift form —
    ΔC = ∫G − ∫D_loss. Every change in coherence is exactly generative
    income minus recorded losses. The ledger balances. -/
theorem budget_identity (a b : ℝ)
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl) :
    C b - C a = (∫ t in a..b, G t) - ∫ t in a..b, Dl t := by
  have h1 : ∫ t in a..b, (G t - Dl t) = C b - C a :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hGL t)
      ((hGc.sub hDc).intervalIntegrable a b)
  rw [integral_sub (hGc.intervalIntegrable a b)
    (hDc.intervalIntegrable a b)] at h1
  linarith

/-- **THE ONTOLOGICAL SECOND LAW:** the ledger S(t) = ∫D_loss only
    grows — D_loss ≥ 0 pointwise (Ch8 §6, named), so every moment adds
    a line and no line is ever erased. -/
theorem ledger_monotone (hDc : Continuous Dl) (hD : ∀ t, 0 ≤ Dl t)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ s in (0:ℝ)..a, Dl s) ≤ ∫ s in (0:ℝ)..b, Dl s := by
  have hsplit : (∫ s in (0:ℝ)..a, Dl s) + ∫ s in a..b, Dl s
      = ∫ s in (0:ℝ)..b, Dl s :=
    integral_add_adjacent_intervals (hDc.intervalIntegrable 0 a)
      (hDc.intervalIntegrable a b)
  have hpos : 0 ≤ ∫ s in a..b, Dl s :=
    integral_nonneg hab (fun u _ => hD u)
  linarith

/-- **The balance patch:** where generation exactly pays for loss,
    coherence is conserved — ΔC = 0. Conservation as achieved balance,
    the flat pattern once more. -/
theorem balance_patch (a b : ℝ)
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hbal : ∀ t ∈ Set.uIcc a b, G t = Dl t) :
    C b = C a := by
  have h1 : ∫ t in a..b, (G t - Dl t) = C b - C a :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hGL t)
      ((hGc.sub hDc).intervalIntegrable a b)
  have h0 : ∫ t in a..b, (G t - Dl t) = 0 := by
    have heq : Set.EqOn (fun t => G t - Dl t) (fun _ => (0:ℝ))
        (Set.uIcc a b) := fun t ht => by
      simp [hbal t ht]
    rw [integral_congr heq]
    simp
  linarith

/-- **The honest S_max bound:** cumulative loss can exceed cumulative
    generation only by the initial savings above the floor —
    ∫D_loss ≤ ∫G + (C₀ − C_min). "You cannot lose more coherence than
    remains." (Full S_max < ∞ is Ch10's cosmological claim and stays
    fenced: it additionally needs ∫G finite.) -/
theorem ledger_dominated (b : ℝ)
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hfloor : ∀ t, Cmin ≤ C t) :
    (∫ t in (0:ℝ)..b, Dl t) ≤ (∫ t in (0:ℝ)..b, G t) + (C 0 - Cmin) := by
  have hbud := budget_identity C G Dl 0 b hGL hGc hDc
  linarith [hfloor b]

/-! ## Stage 2 — the Turn trio -/

/-- **No eternal uniform fade:** a field losing at least ε forever
    breaches any floor in finite time — so under Mu, the uniform fade
    is impossible. -/
theorem no_eternal_fade
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hfloor : ∀ t, Cmin ≤ C t) (ε : ℝ) (hε : 0 < ε) :
    ¬ ∀ t, 0 ≤ t → G t - Dl t ≤ -ε := by
  intro hfade
  set T := (C 0 - Cmin) / ε + 1 with hTdef
  have h0 : 0 ≤ C 0 - Cmin := by linarith [hfloor 0]
  have hT0 : (0:ℝ) ≤ T := by positivity
  have h1 : ∫ t in (0:ℝ)..T, (G t - Dl t) = C T - C 0 :=
    integral_eq_sub_of_hasDerivAt (fun t _ => hGL t)
      ((hGc.sub hDc).intervalIntegrable 0 T)
  have hmono : (∫ t in (0:ℝ)..T, (G t - Dl t))
      ≤ ∫ t in (0:ℝ)..T, (-ε : ℝ) := by
    apply integral_mono_on hT0 ((hGc.sub hDc).intervalIntegrable 0 T)
      (intervalIntegrable_const)
    intro u hu
    exact hfade u hu.1
  rw [integral_const, smul_eq_mul] at hmono
  have hCT : C T - C 0 ≤ (T - 0) * (-ε) := by
    rw [← h1]; exact hmono
  have hTe : T * ε = C 0 - Cmin + ε := by
    rw [hTdef]
    field_simp
  nlinarith [hfloor T]

/-- **THE TURN (the printed trichotomy):** at the floor, with the floor
    holding into the future, the derivative cannot be negative — the
    very next instant would breach Mu — and Perpetual Flow (NAMED: the
    derivative is not zero; "a resting field is a still field") rules
    out zero. Every value is ruled out but one: **dC/dt > 0.** -/
theorem the_turn (t₀ : ℝ)
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hat : C t₀ = Cmin)
    (hfloor_future : ∀ t, t₀ ≤ t → Cmin ≤ C t)
    (hPF : G t₀ - Dl t₀ ≠ 0) :
    0 < G t₀ - Dl t₀ := by
  have hslope : Tendsto (slope C t₀) (𝓝[>] t₀) (𝓝 (G t₀ - Dl t₀)) :=
    (hasDerivAt_iff_tendsto_slope.mp (hGL t₀)).mono_left
      (nhdsWithin_mono t₀ (fun x hx => ne_of_gt hx))
  have hnn : ∀ᶠ t in 𝓝[>] t₀, 0 ≤ slope C t₀ t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h1 : t₀ < t := ht
    have h2 : C t₀ ≤ C t := by
      rw [hat]
      exact hfloor_future t (le_of_lt h1)
    rw [slope_def_field]
    exact div_nonneg (by linarith) (by linarith)
  have hd0 : 0 ≤ G t₀ - Dl t₀ := ge_of_tendsto hslope hnn
  exact lt_of_le_of_ne hd0 (Ne.symm hPF)

/-- **MU FORBIDS THE ARRIVAL:** with the floor held everywhere, any
    interior touch of C_min is a local minimum, forcing the derivative
    to zero — which Perpetual Flow forbids. So the field never reaches
    its floor at all: the reach that cannot arrive, certified as
    unable to arrive. -/
theorem cannot_arrive
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hfloor : ∀ t, Cmin ≤ C t)
    (hPF : ∀ t, G t - Dl t ≠ 0) (t : ℝ) :
    Cmin < C t := by
  rcases lt_or_eq_of_le (hfloor t) with h | h
  · exact h
  · exfalso
    have hmin : IsLocalMin C t := by
      apply Filter.Eventually.of_forall
      intro y
      rw [← h]
      exact hfloor y
    exact hPF t (hmin.hasDerivAt_eq_zero (hGL t))

/-! ## Stage 3 — the capstone -/

/-- **MUST TURN — §10.6's arc as one theorem.** Once the thinning
    brings the field into the activity zone near its floor (canon's own
    premise: "as the universe nears C_min"), no decreasing option
    survives: a nonpositive drift keeps it in the zone, where
    floor_activity (NAMED: |Ċ| ≥ ε near the floor — "maximum activity,
    no room left to fall, no permission to stop") makes the fade
    uniform, and a uniform fade breaches Mu in finite time. Therefore
    **somewhere ahead the derivative is positive. The thinning ends;
    the reach turns.** -/
theorem must_turn
    (hGL : ∀ t, HasDerivAt C (G t - Dl t) t)
    (hGc : Continuous G) (hDc : Continuous Dl)
    (hfloor : ∀ t, Cmin ≤ C t)
    (δ ε : ℝ) (hε : 0 < ε)
    (hFA : ∀ t, 0 ≤ t → C t ≤ Cmin + δ → ε ≤ |G t - Dl t|)
    (t₁ : ℝ) (ht₁ : 0 ≤ t₁) (hnear : C t₁ ≤ Cmin + δ) :
    ∃ t, 0 ≤ t ∧ 0 < G t - Dl t := by
  by_contra hcon
  push Not at hcon
  -- the drift stays nonpositive, so the field never leaves the zone
  have hstay : ∀ u, t₁ ≤ u → C u ≤ Cmin + δ := by
    intro u hu
    have hint : ∫ s in t₁..u, (G s - Dl s) = C u - C t₁ :=
      integral_eq_sub_of_hasDerivAt (fun s _ => hGL s)
        ((hGc.sub hDc).intervalIntegrable t₁ u)
    have hnp : (∫ s in t₁..u, (G s - Dl s)) ≤ ∫ s in t₁..u, (0:ℝ) := by
      apply integral_mono_on hu ((hGc.sub hDc).intervalIntegrable t₁ u)
        (intervalIntegrable_const)
      intro s hs
      exact hcon s (le_trans ht₁ hs.1)
    rw [integral_const, smul_eq_mul, mul_zero] at hnp
    linarith
  -- in the zone, nonpositive + activity = uniform fade
  have hdrop : ∀ u, t₁ ≤ u → G u - Dl u ≤ -ε := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans ht₁ hu
    have habs := hFA u hu0 (hstay u hu)
    have hle := hcon u hu0
    rw [abs_of_nonpos hle] at habs
    linarith
  -- and the uniform fade breaches the floor
  set T := t₁ + (C t₁ - Cmin) / ε + 1 with hTdef
  have hT1 : t₁ ≤ T := by
    have h0 : 0 ≤ (C t₁ - Cmin) / ε :=
      div_nonneg (by linarith [hfloor t₁]) (le_of_lt hε)
    linarith
  have hint : ∫ s in t₁..T, (G s - Dl s) = C T - C t₁ :=
    integral_eq_sub_of_hasDerivAt (fun s _ => hGL s)
      ((hGc.sub hDc).intervalIntegrable t₁ T)
  have hmono : (∫ s in t₁..T, (G s - Dl s)) ≤ ∫ s in t₁..T, (-ε : ℝ) := by
    apply integral_mono_on hT1 ((hGc.sub hDc).intervalIntegrable t₁ T)
      (intervalIntegrable_const)
    intro s hs
    exact hdrop s hs.1
  rw [integral_const, smul_eq_mul] at hmono
  have hCT : C T - C t₁ ≤ (T - t₁) * (-ε) := by
    rw [← hint]; exact hmono
  have hTe : (T - t₁) * ε = C t₁ - Cmin + ε := by
    rw [hTdef]
    field_simp
    ring
  nlinarith [hfloor T]

end PNLedger

#print axioms PNLedger.budget_identity
#print axioms PNLedger.ledger_monotone
#print axioms PNLedger.balance_patch
#print axioms PNLedger.ledger_dominated
#print axioms PNLedger.no_eternal_fade
#print axioms PNLedger.the_turn
#print axioms PNLedger.cannot_arrive
#print axioms PNLedger.must_turn
