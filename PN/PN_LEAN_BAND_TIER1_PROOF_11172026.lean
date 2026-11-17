/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE BAND TOWER, TIER 1 · 11/17/2026 · Lean 4 + mathlib
Ch18 §11's printed "mathematical sketch" → theorems · FRAMEWORK-FREE FILE #3

Per flight packet PN_BAND_TIER1_FLIGHT_PACKET_11172026 (v2, amended
after independent review; all three rulings closed: regions / Fisher–Rao
weighted tier reserved / no composite feel-scalar).

Authorities (verbatim, verified at source 11/17):
· "C(t) = F(t) ∩ B(t)"  and  "C(t) = argmin_x ( ||x − F(t)|| + ||x − B(t)|| )"
· "Where these compressions overlap, they constrain each other. That
  constraint-space is what we call the 'felt present.'"
· Prediction 1: "consciousness breaks when forward and backward CPC diverge."

THE CLAIM GRAIN: bare metric space, ‖x−S‖ read as Metric.infDist (ruling 1).
Metric-independence is each theorem's own quantifier. NO PN premise appears in
any signature — the Consciousness Axiom is the reading; this file is the
geometry. Closedness, compactness and nonemptiness are NAMED fences
(mathlib's infDist to ∅ is 0 — packet amendment 2).

SUBSTITUTION (logged in the build record): the packet's arithmetic
noncompact-door witness (ℕ-grid vs shifted grid) requires closedness donors
the snapshot lacks (no ℕ→ℝ closed-embedding lemma); certified witness is the
x-axis and the exp graph in ℝ², same claim exactly: disjoint, closed,
infimum zero, never attained.

Free versus paid: in the overlap, minimizers satisfy both regions at zero
cost; broken, every candidate pays, and without compactness the minimum may
not be reached at all.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

open Metric

namespace PNBand

variable {X : Type*} [MetricSpace X]

/-- The printed variational objective: J(x) = ‖x − F‖ + ‖x − B‖, with ‖·−S‖
read as distance-to-set per the author's regions ruling (11/17). -/
noncomputable def J (F B : Set X) (x : X) : ℝ :=
  infDist x F + infDist x B

/-- Helper (uncounted): the objective is nonnegative. -/
theorem J_nonneg (F B : Set X) (x : X) : 0 ≤ J F B x :=
  add_nonneg infDist_nonneg infDist_nonneg

/-- **THEOREM 1 — the constraint-space is the intersection.** For closed
regions with nonempty overlap, in EVERY metric space: x minimizes the printed
objective iff x ∈ F ∩ B. Canon's felt present = the region satisfying both
compressions, at zero cost. Metric-independence is the quantifier itself. -/
theorem constraint_space_is_intersection
    (F B : Set X) (hF : IsClosed F) (hB : IsClosed B)
    (hne : (F ∩ B).Nonempty) (x : X) :
    (∀ y, J F B x ≤ J F B y) ↔ x ∈ F ∩ B := by
  obtain ⟨z, hzF, hzB⟩ := hne
  constructor
  · intro h
    have hJz : J F B z = 0 := by
      simp only [J, infDist_zero_of_mem hzF, infDist_zero_of_mem hzB, add_zero]
    have hle : J F B x ≤ 0 := hJz ▸ h z
    have h1 := infDist_nonneg (x := x) (s := F)
    have h2 := infDist_nonneg (x := x) (s := B)
    simp only [J] at hle
    have hFx : infDist x F = 0 := by linarith
    have hBx : infDist x B = 0 := by linarith
    exact ⟨(hF.mem_iff_infDist_zero ⟨z, hzF⟩).mpr hFx,
           (hB.mem_iff_infDist_zero ⟨z, hzB⟩).mpr hBx⟩
  · intro hx y
    have hx0 : J F B x = 0 := by
      simp only [J, infDist_zero_of_mem hx.1, infDist_zero_of_mem hx.2, add_zero]
    rw [hx0]
    exact J_nonneg F B y

/-- **THEOREM 2 — canon's two printed formulas are one statement.** The
geometric form IS the variational form's solution set: the minimizer set of
the argmin formula equals F ∩ B. "§11's two formulas are one statement,"
certified. -/
theorem geometric_equals_variational
    (F B : Set X) (hF : IsClosed F) (hB : IsClosed B)
    (hne : (F ∩ B).Nonempty) :
    {x | ∀ y, J F B x ≤ J F B y} = F ∩ B :=
  Set.ext fun x => constraint_space_is_intersection F B hF hB hne x

/-- **THEOREM 3 — Prediction 1's kernel face: the broken band costs.** F
compact, B closed, both NONEMPTY (named: mathlib's distance to ∅ is 0, which
would kill the claim), disjoint ⟹ the objective is bounded away from zero
UNIFORMLY: the minimum has left zero. "Consciousness breaks when forward and
backward CPC diverge" — the divergence is the positive floor under J. -/
theorem broken_band_positive
    (F B : Set X) (hFc : IsCompact F) (hB : IsClosed B)
    (hFne : F.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint F B) :
    ∃ ε > 0, ∀ x, ε ≤ J F B x := by
  obtain ⟨y₀, hy₀F, hy₀min⟩ :=
    hFc.exists_isMinOn hFne (Continuous.continuousOn (continuous_infDist_pt B))
  refine ⟨infDist y₀ B, ?_, ?_⟩
  · show 0 < infDist y₀ B
    exact (hB.notMem_iff_infDist_pos hBne).mp (Set.disjoint_left.mp hdisj hy₀F)
  · intro x
    by_contra hcon
    rw [not_le] at hcon
    have hxF : infDist x F < infDist y₀ B - infDist x B := by
      simp only [J] at hcon
      linarith
    obtain ⟨y, hyF, hy⟩ := (infDist_lt_iff hFne).mp hxF
    have h1 : infDist y₀ B ≤ infDist y B := isMinOn_iff.mp hy₀min y hyF
    have h2 : infDist y B ≤ infDist x B + dist y x := infDist_le_infDist_add_dist
    rw [dist_comm] at hy
    linarith

/-- **THEOREM 4 — the noncompact door (matched pair): the compactness fence
in Theorem 3 is SHARP.** Explicit disjoint closed regions — the x-axis and
the graph of exp in the plane — with infimum ZERO and the minimum NEVER
attained: the regions thin toward each other forever and never meet. Without
compactness, breaking the band can lose not just zero-cost but attainment
itself. (Asymptote-not-arrival, 6th appearance.) -/
theorem noncompact_door :
    ∃ F B : Set (ℝ × ℝ),
      IsClosed F ∧ IsClosed B ∧ F.Nonempty ∧ B.Nonempty ∧ Disjoint F B ∧
      (∀ p, 0 < J F B p) ∧
      (∀ ε > 0, ∃ p, J F B p < ε) := by
  refine ⟨{p | p.2 = 0}, {p | p.2 = Real.exp p.1},
    isClosed_eq continuous_snd continuous_const,
    isClosed_eq continuous_snd (Real.continuous_exp.comp continuous_fst),
    ⟨((0 : ℝ), (0 : ℝ)), rfl⟩, ⟨((0 : ℝ), Real.exp 0), rfl⟩, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.mpr fun p hpF hpB => ?_
    simp only [Set.mem_ofPred_eq] at hpF hpB
    have := Real.exp_pos p.1
    rw [hpF] at hpB
    linarith
  · intro p
    rcases (J_nonneg _ _ p).lt_or_eq with h | h
    · exact h
    · exfalso
      have hFcl : IsClosed {p : ℝ × ℝ | p.2 = 0} :=
        isClosed_eq continuous_snd continuous_const
      have hBcl : IsClosed {p : ℝ × ℝ | p.2 = Real.exp p.1} :=
        isClosed_eq continuous_snd (Real.continuous_exp.comp continuous_fst)
      have h1 := infDist_nonneg (x := p) (s := {p : ℝ × ℝ | p.2 = 0})
      have h2 := infDist_nonneg (x := p) (s := {p : ℝ × ℝ | p.2 = Real.exp p.1})
      simp only [J] at h
      have hF0 : infDist p {p : ℝ × ℝ | p.2 = 0} = 0 := by linarith
      have hB0 : infDist p {p : ℝ × ℝ | p.2 = Real.exp p.1} = 0 := by linarith
      have hpF : p ∈ {p : ℝ × ℝ | p.2 = 0} :=
        (hFcl.mem_iff_infDist_zero ⟨((0 : ℝ), (0 : ℝ)), rfl⟩).mpr hF0
      have hpB : p ∈ {p : ℝ × ℝ | p.2 = Real.exp p.1} :=
        (hBcl.mem_iff_infDist_zero ⟨((0 : ℝ), Real.exp 0), rfl⟩).mpr hB0
      simp only [Set.mem_ofPred_eq] at hpF hpB
      have := Real.exp_pos p.1
      rw [hpF] at hpB
      linarith
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨((-(n : ℝ)), (0 : ℝ)), ?_⟩
    have hmem : (((-(n : ℝ)), (0 : ℝ)) : ℝ × ℝ) ∈ {p : ℝ × ℝ | p.2 = 0} := rfl
    have hqmem : (((-(n : ℝ)), Real.exp (-(n : ℝ))) : ℝ × ℝ) ∈
        {p : ℝ × ℝ | p.2 = Real.exp p.1} := rfl
    have hF0 : infDist (((-(n : ℝ)), (0 : ℝ)) : ℝ × ℝ) {p : ℝ × ℝ | p.2 = 0} = 0 :=
      infDist_zero_of_mem hmem
    have hd : dist (0 : ℝ) (Real.exp (-(n : ℝ))) = Real.exp (-(n : ℝ)) := by
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
    have hBle : infDist (((-(n : ℝ)), (0 : ℝ)) : ℝ × ℝ)
        {p : ℝ × ℝ | p.2 = Real.exp p.1} ≤ Real.exp (-(n : ℝ)) := by
      refine le_trans (infDist_le_dist_of_mem hqmem) ?_
      rw [Prod.dist_eq, dist_self, hd]
      exact le_of_eq (max_eq_right (Real.exp_pos _).le)
    have hexp : Real.exp (-(n : ℝ)) ≤ 1 / ((n : ℝ) + 1) := by
      rw [Real.exp_neg, inv_eq_one_div]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have := Real.add_one_le_exp (n : ℝ)
      linarith
    have hlt : 1 / ((n : ℝ) + 1) < ε := by
      have h1 : 1 / ε < (n : ℝ) + 1 := lt_trans hn (by linarith)
      have h2 : 1 / ((n : ℝ) + 1) < 1 / (1 / ε) :=
        one_div_lt_one_div_of_lt (one_div_pos.mpr hε) h1
      rwa [one_div_one_div] at h2
    simp only [J]
    rw [hF0]
    linarith

/-- The smear objective in ℝ: regions {0} and {1}. -/
noncomputable def Js (x : ℝ) : ℝ := J ({0} : Set ℝ) ({1} : Set ℝ) x

/-- **THEOREM 5 — the smear witness (witness-grade, ℝ): when the overlap
empties, selection is lost.** With F = {0}, B = {1}: the objective equals 1
on ALL of [0,1] and exceeds 1 outside, so the minimizer set is the whole
segment — and the regions' intersection is empty, so every minimizer fails
at least one constraint. In the overlap regime the minimum is free; here it
is paid. Dissociation's formal face, claimed for this instance only. -/
theorem smear_witness :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, Js x = 1) ∧
    (∀ x : ℝ, 1 ≤ Js x) ∧
    ({x : ℝ | ∀ y, Js x ≤ Js y} = Set.Icc (0 : ℝ) 1) ∧
    (({0} : Set ℝ) ∩ ({1} : Set ℝ) = ∅) := by
  have hJs : ∀ x : ℝ, Js x = |x| + |x - 1| := by
    intro x
    simp only [Js, J, infDist_singleton, Real.dist_eq, sub_zero]
  have ha : ∀ x ∈ Set.Icc (0 : ℝ) 1, Js x = 1 := by
    intro x hx
    rw [hJs, abs_of_nonneg hx.1, abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0)]
    ring
  have hb : ∀ x : ℝ, 1 ≤ Js x := by
    intro x
    rw [hJs]
    rcases le_or_gt 0 x with h0 | h0
    · rcases le_or_gt x 1 with h1 | h1
      · rw [abs_of_nonneg h0, abs_of_nonpos (by linarith : x - 1 ≤ 0)]
        linarith
      · rw [abs_of_nonneg h0, abs_of_pos (by linarith : (0 : ℝ) < x - 1)]
        linarith
    · rw [abs_of_neg h0, abs_of_neg (by linarith : x - 1 < 0)]
      linarith
  have hc : {x : ℝ | ∀ y, Js x ≤ Js y} = Set.Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · intro h
      have h0 : Js 0 = 1 := ha 0 ⟨le_refl (0 : ℝ), zero_le_one⟩
      have hx1 : Js x ≤ 1 := h0 ▸ h 0
      constructor
      · by_contra hneg
        rw [not_le] at hneg
        rw [hJs, abs_of_neg hneg, abs_of_neg (by linarith : x - 1 < 0)] at hx1
        linarith
      · by_contra hbig
        rw [not_le] at hbig
        rw [hJs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x),
          abs_of_pos (by linarith : (0 : ℝ) < x - 1)] at hx1
        linarith
    · intro hx y
      rw [ha x ⟨hx.1, hx.2⟩]
      exact hb y
  have hd : (({0} : Set ℝ) ∩ ({1} : Set ℝ)) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl
    norm_num
  exact ⟨ha, hb, hc, hd⟩

end PNBand

#print axioms PNBand.constraint_space_is_intersection
#print axioms PNBand.geometric_equals_variational
#print axioms PNBand.broken_band_positive
#print axioms PNBand.noncompact_door
#print axioms PNBand.smear_witness
