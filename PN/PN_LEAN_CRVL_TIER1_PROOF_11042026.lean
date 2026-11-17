/-
  PRINCIPIA NOVA — CRVL TIER 1: THE COHERENCE-RELATIVE VELOCITY LAW
  11/04/2026 · Lean 4 + mathlib · Chapter 9 §4, Observer-Compliant Form.

  FIRST PURE-CHAPTER CERTIFICATION in the PN Lean program: the statement
  contract was drawn from Ch9's printed text (ruled by the author 11/04, with
  independent concurrence), then certified. Objects:

    c_max > 0            — the tempo ceiling, "the only truly universal
                           constant in the equation"
    g : ℝ → ℝ            — dimensionless tempo function of coherence
                           density; canon constraints NAMED as hypotheses:
                           0 < g C < 1 (Mu forbids frozen light and
                           realized maximum); monotone decreasing —
                           certified at BOTH readings (Antitone / StrictAnti),
                           strictness being the reading canon forces three
                           ways (the "means lower" parenthetical, the
                           Mars/void different-readings passage, the exp
                           tempo map of Z-G.5)
    cloc C = c_max·g(C)  — the local tempo limit
    kfac Cx Cy = g(Cx)/g(Cy) — the conversion factor between two regions'
                           clocks ("one evaluation of dT_x/dT_Earth").
                           LOCALITY CLAUSE (named, §24): each factor
                           depends only on the endpoint densities — an
                           assumption of the construction, not a theorem;
                           the groupoid algebra rides on it.
    α ∈ [0,1)            — fraction of the LOCAL limit; α < 1 is the
                           massive-object clause (Ch9 Principle 7);
                           light rides α = 1, outside this file's scope
                           by design, not oversight.

  THEOREMS
    mu_pair          : 0 < cloc C < c_max — no frozen light, no realized
                       ceiling: the Mu bounds doing work
    k_self           : kfac C C = 1   ("on Earth, k = 1" as a theorem)
    k_inv            : kfac X Y · kfac Y X = 1
    k_cocycle        : kfac X Z = kfac X Y · kfac Y Z — conversion
                       factors compose multiplicatively: composing
                       reparametrizations, never adding velocities
    k_gt_one_of_antitone : (plain Antitone) k > 1 ⟹ C_X < C_Y — what
                       non-strict monotonicity honestly buys
    k_order_iff      : (StrictAnti) k > 1 ⟺ C_X < C_Y — the full
                       equivalence strictness purchases
    earth_reading    : α·(k·cloc C_E) = α·cloc C_X — one motion, two
                       clocks: Earth's reading IS the local motion
    sr_ceiling_at_k1 : k = 1 ⟹ reading < c_E and separation < 2c_E —
                       SR's coordinate kinematics recovered exactly where
                       coherence is flat (the k = 1 limit, stated as the
                       ceilings §24 licenses: reparametrization fidelity,
                       NOT Lorentz boost composition, which is
                       architecturally outside CRVL's objects)
    falsifier_iff    : v_sep > 2c_E ⟺ αk > 1 — THE DISCRIMINATING
                       THRESHOLD as an equivalence
    discriminating_case : α = 0.8, k = 1.5 — canon's printed example:
                       locally sub-c, separation 2.4·c_E — kernel-checked
                       witness that the PN-distinctive regime is consistent
-/
import Mathlib

namespace CRVL

variable (g : ℝ → ℝ) (cmax : ℝ)

/-- The local tempo limit: c_x = c_max · g(C_x). -/
noncomputable def cloc (C : ℝ) : ℝ := cmax * g C

/-- The conversion factor between two regions' clocks: k_{X→Y} = g(C_X)/g(C_Y).
    Locality clause (named, §24): depends only on the endpoint densities. -/
noncomputable def kfac (Cx Cy : ℝ) : ℝ := g Cx / g Cy

/-- **The Mu pair:** 0 < c_x < c_max — no frozen light, no realized ceiling. -/
theorem mu_pair (hc : 0 < cmax) (hg0 : ∀ C, 0 < g C) (hg1 : ∀ C, g C < 1)
    (C : ℝ) : 0 < cloc g cmax C ∧ cloc g cmax C < cmax := by
  constructor
  · exact mul_pos hc (hg0 C)
  · calc cmax * g C < cmax * 1 := by
          exact mul_lt_mul_of_pos_left (hg1 C) hc
      _ = cmax := mul_one cmax

/-- "On Earth, k = 1 by definition" — as a theorem. -/
theorem k_self (hg0 : ∀ C, 0 < g C) (C : ℝ) : kfac g C C = 1 :=
  div_self (ne_of_gt (hg0 C))

/-- Reading X from Y and Y from X are exact inverses. -/
theorem k_inv (hg0 : ∀ C, 0 < g C) (Cx Cy : ℝ) :
    kfac g Cx Cy * kfac g Cy Cx = 1 := by
  have hx := ne_of_gt (hg0 Cx)
  have hy := ne_of_gt (hg0 Cy)
  unfold kfac
  field_simp

/-- **The cocycle: conversion factors compose multiplicatively** —
    k_{X→Z} = k_{X→Y} · k_{Y→Z}. Composing reparametrizations, never
    adding velocities; no path dependence among clocks. -/
theorem k_cocycle (hg0 : ∀ C, 0 < g C) (Cx Cy Cz : ℝ) :
    kfac g Cx Cz = kfac g Cx Cy * kfac g Cy Cz := by
  have hx := ne_of_gt (hg0 Cx)
  have hy := ne_of_gt (hg0 Cy)
  have hz := ne_of_gt (hg0 Cz)
  unfold kfac
  field_simp

/-- What plain (non-strict) monotonicity honestly buys: one direction. -/
theorem k_gt_one_of_antitone (hg0 : ∀ C, 0 < g C) (hmono : Antitone g)
    (Cx Cy : ℝ) (hk : 1 < kfac g Cx Cy) : Cx < Cy := by
  by_contra h
  push_neg at h
  have hle : g Cx ≤ g Cy := hmono h
  have : kfac g Cx Cy ≤ 1 := by
    unfold kfac
    rw [div_le_one (hg0 Cy)]
    exact hle
  linarith

/-- **The order equivalence strictness purchases** (StrictAnti g, the
    reading canon forces): k > 1 ⟺ C_X < C_Y — lower coherence density,
    higher tempo limit, in both directions. -/
theorem k_order_iff (hg0 : ∀ C, 0 < g C) (hmono : StrictAnti g)
    (Cx Cy : ℝ) : 1 < kfac g Cx Cy ↔ Cx < Cy := by
  constructor
  · exact k_gt_one_of_antitone g hg0 hmono.antitone Cx Cy
  · intro h
    have hgt : g Cy < g Cx := hmono h
    unfold kfac
    rw [lt_div_iff₀ (hg0 Cy)]
    linarith

/-- **One motion, two clocks:** Earth's reading α·k·c_E IS the local
    motion α·c_X, re-expressed. -/
theorem earth_reading (hg0 : ∀ C, 0 < g C) (Cx Ce α : ℝ) :
    α * (kfac g Cx Ce * cloc g cmax Ce) = α * cloc g cmax Cx := by
  have he := ne_of_gt (hg0 Ce)
  unfold kfac cloc
  field_simp

/-- **SR recovered where coherence is flat:** at k = 1, a massive object's
    reading stays under c_E and a two-body separation stays under 2·c_E —
    Special Relativity's coordinate ceilings, exact. (The k = 1 limit as
    §24 licenses it: reparametrization fidelity, not boost composition.) -/
theorem sr_ceiling_at_k1 (ce α k : ℝ) (hce : 0 < ce)
    (_hα0 : 0 ≤ α) (hα : α < 1) (hk : k = 1) :
    α * (k * ce) < ce ∧ 2 * α * k * ce < 2 * ce := by
  subst hk
  constructor
  · nlinarith
  · nlinarith

/-- **THE FALSIFIER AS AN IFF:** the separation reading exceeds SR's
    ceiling exactly when αk > 1 — the discriminating threshold of Ch9,
    in both directions. Below it, SR keeps jurisdiction; above it,
    only PN survives. -/
theorem falsifier_iff (ce α k : ℝ) (hce : 0 < ce) :
    2 * ce < 2 * α * k * ce ↔ 1 < α * k := by
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Canon's discriminating case, kernel-checked:** α = 0.8, k = 1.5 —
    locally sub-c (α < 1), threshold crossed (αk = 1.2 > 1), separation
    reading 2.4·c_E. The PN-distinctive regime is arithmetically
    consistent: no local violation, super-2c_E appearance. -/
theorem discriminating_case (ce : ℝ) :
    (0.8 : ℝ) < 1 ∧ (1 : ℝ) < 0.8 * 1.5
      ∧ 2 * 0.8 * 1.5 * ce = 2.4 * ce := by
  norm_num

end CRVL

#print axioms CRVL.mu_pair
#print axioms CRVL.k_self
#print axioms CRVL.k_inv
#print axioms CRVL.k_cocycle
#print axioms CRVL.k_gt_one_of_antitone
#print axioms CRVL.k_order_iff
#print axioms CRVL.earth_reading
#print axioms CRVL.sr_ceiling_at_k1
#print axioms CRVL.falsifier_iff
#print axioms CRVL.discriminating_case
