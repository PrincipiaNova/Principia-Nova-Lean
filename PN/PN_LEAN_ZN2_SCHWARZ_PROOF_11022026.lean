/-
  PRINCIPIA NOVA — Z-N.2 SCHWARZ POLISH: THE MIXED PARTIAL, DERIVED
  11/02/2026 · Lean 4 + mathlib.

  Z-N.2 Tier 2 carried the mixed partial as two-sided named data: one
  function m hypothesized to be both ∂t(px) and ∂x(pt). This file
  DISCHARGES that hypothesis: for a C² field, the two-sided m is a
  THEOREM — mathlib's symmetry of second derivatives (Schwarz), pulled
  through the curried-partials ↔ Fréchet-derivative translation.

  THEOREM schwarz_curried :
    for φ with C² uncurrying and curried partials pt, px:
    ∃ m, HasDerivAt (fun s => px s x) m t ∧ HasDerivAt (fun y => pt t y) m x
    — one value, certified from both slots. Exactly the ⟨m, hpxt, hptx⟩
    package Tier 2's theorems consume.

  The plumbing built here (lines in the plane, evaluation CLMs, partials
  as directional Fréchet derivatives) is the same material the Tier 3
  (PhysLean d = 2) bridge requires: prepaid trail work.
-/
import Mathlib

namespace PN

/-- Partial derivatives of a curried two-variable function agree with
    directional Fréchet derivatives of its uncurrying: the x-slot. -/
lemma px_eq_fderiv (φ px : ℝ → ℝ → ℝ)
    (hΦ : Differentiable ℝ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hpx : ∀ s y, HasDerivAt (fun v => φ s v) (px s y) y) (s y : ℝ) :
    px s y = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (s, y) ((0 : ℝ), (1 : ℝ)) := by
  have hline : HasDerivAt (fun v : ℝ => ((s, v) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y s).prodMk (hasDerivAt_id y)
  have hcomp := (hΦ (s, y)).hasFDerivAt.comp_hasDerivAt y hline
  exact (hpx s y).unique hcomp

/-- Same for the t-slot. -/
lemma pt_eq_fderiv (φ pt : ℝ → ℝ → ℝ)
    (hΦ : Differentiable ℝ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hpt : ∀ s y, HasDerivAt (fun u => φ u y) (pt s y) s) (s y : ℝ) :
    pt s y = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (s, y) ((1 : ℝ), (0 : ℝ)) := by
  have hline : HasDerivAt (fun u : ℝ => ((u, y) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have hcomp := (hΦ (s, y)).hasFDerivAt.comp_hasDerivAt s hline
  exact (hpt s y).unique hcomp

/-- **THE SCHWARZ SPLICE (kernel-checked):** for a C² field, the mixed
    partial exists as ONE value certified from BOTH slots — the two-sided
    data Z-N.2 Tier 2 hypothesized, now derived from smoothness alone. -/
theorem schwarz_curried (φ pt px : ℝ → ℝ → ℝ) (t x : ℝ)
    (hΦ : ContDiff ℝ 2 (fun p : ℝ × ℝ => φ p.1 p.2))
    (hpt : ∀ s y, HasDerivAt (fun u => φ u y) (pt s y) s)
    (hpx : ∀ s y, HasDerivAt (fun v => φ s v) (px s y) y) :
    ∃ mval : ℝ, HasDerivAt (fun s => px s x) mval t
      ∧ HasDerivAt (fun y => pt t y) mval x := by
  set Φ : ℝ × ℝ → ℝ := fun p => φ p.1 p.2 with hΦdef
  have hd1 : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ Φ) := hC1.differentiable one_ne_zero
  have hAll : ∀ p, HasFDerivAt Φ (fderiv ℝ Φ p) p := fun p => (hd1 p).hasFDerivAt
  -- the second derivative at (t, x), and its symmetry (Schwarz)
  have hf'' : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) (t, x)) (t, x) :=
    (hd2 (t, x)).hasFDerivAt
  have hsymm := second_derivative_symmetric hAll hf''
    ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
  refine ⟨fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)), ?_, ?_⟩
  · -- ∂t of px: differentiate s ↦ fderiv Φ (s, x) (0,1) along the t-line
    have hfun : (fun s => px s x)
        = fun s => fderiv ℝ Φ (s, x) ((0 : ℝ), (1 : ℝ)) :=
      funext fun s => px_eq_fderiv φ px hd1 hpx s x
    rw [hfun]
    have hline : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h2 := hf''.comp_hasDerivAt t hline
    have h3 := ((ContinuousLinearMap.apply ℝ ℝ
        (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)).hasFDerivAt).comp_hasDerivAt t h2
    exact h3
  · -- ∂x of pt: differentiate y ↦ fderiv Φ (t, y) (1,0) along the x-line,
    -- then swap the slots by Schwarz
    have hfun : (fun y => pt t y)
        = fun y => fderiv ℝ Φ (t, y) ((1 : ℝ), (0 : ℝ)) :=
      funext fun y => pt_eq_fderiv φ pt hd1 hpt t y
    rw [hfun]
    have hline : HasDerivAt (fun y : ℝ => ((t, y) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
    have h2 := hf''.comp_hasDerivAt x hline
    have h3 := ((ContinuousLinearMap.apply ℝ ℝ
        (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)).hasFDerivAt).comp_hasDerivAt x h2
    have h4 : fderiv ℝ (fderiv ℝ Φ) (t, x) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
        = fderiv ℝ (fderiv ℝ Φ) (t, x) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) :=
      hsymm.symm
    rw [← h4]
    exact h3

end PN

#print axioms PN.schwarz_curried
