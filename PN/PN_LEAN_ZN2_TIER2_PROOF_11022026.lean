/-
  PRINCIPIA NOVA — Z-N.2 TIER 2: FIELD STAGE, ANALYSIS GRADE
  11/02/2026 · Lean 4 + mathlib — real functions of TWO variables (t, x),
  honest partial derivatives, real division licensed by N > 0.

  UPGRADE OVER Z-N.2 TIER 1: ∂t and ∂x were abstract derivations there;
  here every partial is mathlib's HasDerivAt in the corresponding slot,
  and the product/quotient/chain rules are THEOREMS used, not axioms.

  THE MODEL (N-2 canon): L = φ_t²/(2N) − N·φ_x²/2 − N·V(φ), with
  position- and time-dependent lapse N(t,x) = τ_coh(C(t,x)).

  Functions (all ℝ → ℝ → ℝ, arguments (t, x)):
    φ — the field;  pt = ∂t φ;  px = ∂x φ;  ptt = ∂t pt;
    m — THE MIXED PARTIAL, certified from both sides (hpxt, hptx):
        one function proven to be ∂t px AND ∂x pt — Schwarz's
        conclusion carried as named two-sided data;
    bx = ∂x px;  n = N;  nt = ∂t N;  nx = ∂x N.

  Energy density and flux (real division):
    ρE = pt²/(2n) + n·(px²/2 + V(φ)),     f = −n·px·pt.

  hEL (Euler–Lagrange, denominators cleared, moved form):
    n·ptt + n³·V′(φ) = pt·nt + n²·nx·px + n³·bx

  THEOREMS
    energy_time_deriv    : ∂t ρE = (nt/n)·ρE + (nx·px·pt + n·bx·pt + n·px·m)
    flux_space_deriv     : ∂x f  = −(nx·px·pt + n·bx·pt + n·px·m)
    sourced_continuity   : ∂t ρE + ∂x f = (nt/n)·ρE     (canon N-2 law)
    arena_obstruction_x  : N·C constant in x ⟹ nx·c + n·cx = 0
                           (proved by DERIVATIVE UNIQUENESS: the product's
                           x-derivative is computed two ways and equated)
    obstruction_iff      : nx = 0 ⟺ cx = 0   (N > 0, C > 0)
                           — THE IRREMOVABILITY CORE at analysis grade
    flat_patch           : nt = 0 ⟹ ∂t ρE + ∂x f = 0  (pure flux)
-/
import Mathlib

namespace PN

variable (φ pt px ptt m bx n nt nx : ℝ → ℝ → ℝ) (V V' : ℝ → ℝ) (t x : ℝ)

/-- **∂t of the energy density, in canon shape.** -/
theorem energy_time_deriv
    (hNpos : ∀ s y, 0 < n s y)
    (hφt : HasDerivAt (fun s => φ s x) (pt t x) t)
    (hptt : HasDerivAt (fun s => pt s x) (ptt t x) t)
    (hpxt : HasDerivAt (fun s => px s x) (m t x) t)
    (hnt : HasDerivAt (fun s => n s x) (nt t x) t)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hEL : n t x * ptt t x + (n t x)^3 * V' (φ t x)
         = pt t x * nt t x + (n t x)^2 * nx t x * px t x + (n t x)^3 * bx t x) :
    HasDerivAt (fun s => (pt s x)^2 / (2 * n s x) + n s x * ((px s x)^2 / 2 + V (φ s x)))
      (nt t x / n t x * ((pt t x)^2 / (2 * n t x) + n t x * ((px t x)^2 / 2 + V (φ t x)))
        + (nx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
           + n t x * (px t x * m t x))) t := by
  have hn : n t x ≠ 0 := ne_of_gt (hNpos t x)
  have h2n : 2 * n t x ≠ 0 := by positivity
  have hkin := (hptt.pow 2).div (hnt.const_mul 2) h2n
  have hVc : HasDerivAt (fun s => V (φ s x)) (V' (φ t x) * pt t x) t :=
    (hV (φ t x)).comp t hφt
  have hin := ((hpxt.pow 2).div_const 2).add hVc
  have hpot := hnt.mul hin
  have htot := hkin.add hpot
  convert htot using 1
  have hELa : ptt t x = (pt t x * nt t x + (n t x)^2 * nx t x * px t x
      + (n t x)^3 * bx t x - (n t x)^3 * V' (φ t x)) / n t x := by
    rw [eq_div_iff hn]
    linear_combination hEL
  rw [hELa]
  push_cast
  field_simp
  simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply]
  ring

/-- **∂x of the energy flux f = −n·px·pt.** -/
theorem flux_space_deriv
    (hptx : HasDerivAt (fun y => pt t y) (m t x) x)
    (hpxx : HasDerivAt (fun y => px t y) (bx t x) x)
    (hnx : HasDerivAt (fun y => n t y) (nx t x) x) :
    HasDerivAt (fun y => -(n t y * (px t y * pt t y)))
      (-(nx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
         + n t x * (px t x * m t x))) x := by
  have hinner := hpxx.mul hptx
  have hprod := hnx.mul hinner
  have h := hprod.neg
  convert h using 1
  simp only [Pi.mul_apply]
  ring

/-- **Z-N.2 SOURCED CONTINUITY, analysis grade (canon shape):**
    ∂t ρE + ∂x f = (∂t N / N) · ρE — the flux intact, the source purely
    the time variation of the clock. -/
theorem sourced_continuity
    (hNpos : ∀ s y, 0 < n s y)
    (hφt : HasDerivAt (fun s => φ s x) (pt t x) t)
    (hptt : HasDerivAt (fun s => pt s x) (ptt t x) t)
    (hpxt : HasDerivAt (fun s => px s x) (m t x) t)
    (hptx : HasDerivAt (fun y => pt t y) (m t x) x)
    (hpxx : HasDerivAt (fun y => px t y) (bx t x) x)
    (hnt : HasDerivAt (fun s => n s x) (nt t x) t)
    (hnx : HasDerivAt (fun y => n t y) (nx t x) x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hEL : n t x * ptt t x + (n t x)^3 * V' (φ t x)
         = pt t x * nt t x + (n t x)^2 * nx t x * px t x + (n t x)^3 * bx t x)
    (Et Fx : ℝ)
    (hEt : HasDerivAt (fun s => (pt s x)^2 / (2 * n s x)
        + n s x * ((px s x)^2 / 2 + V (φ s x))) Et t)
    (hFx : HasDerivAt (fun y => -(n t y * (px t y * pt t y))) Fx x) :
    Et + Fx = nt t x / n t x
      * ((pt t x)^2 / (2 * n t x) + n t x * ((px t x)^2 / 2 + V (φ t x))) := by
  have h1 := energy_time_deriv φ pt px ptt m bx n nt nx V V' t x
    hNpos hφt hptt hpxt hnt hV hEL
  have h2 := flux_space_deriv pt px m bx n nx t x hptx hpxx hnx
  have e1 : Et = nt t x / n t x * ((pt t x)^2 / (2 * n t x)
      + n t x * ((px t x)^2 / 2 + V (φ t x)))
      + (nx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
         + n t x * (px t x * m t x)) := hEt.unique h1
  have e2 : Fx = -(nx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
      + n t x * (px t x * m t x)) := hFx.unique h2
  rw [e1, e2]
  ring

variable (c cx : ℝ → ℝ → ℝ)

/-- **The arena law kills the x-freedom of the clock** — proved by
    derivative uniqueness: N·C constant in x has x-derivative zero,
    and the product rule says that derivative is nx·c + n·cx. -/
theorem arena_obstruction_x (k : ℝ)
    (hk : ∀ y, n t y * c t y = k)
    (hnx : HasDerivAt (fun y => n t y) (nx t x) x)
    (hcx : HasDerivAt (fun y => c t y) (cx t x) x) :
    nx t x * c t x + n t x * cx t x = 0 := by
  have hprod := hnx.mul hcx
  have hconst : HasDerivAt (fun y => n t y * c t y) 0 x := by
    have : (fun y => n t y * c t y) = fun _ => k := funext hk
    rw [this]
    exact hasDerivAt_const x k
  exact hprod.unique hconst

/-- **Z-N.2 IRREMOVABILITY CORE, analysis grade:**
    under the arena law, ∂x N = 0 ⟺ ∂x C = 0 — the clock can be
    flattened exactly where the spatial coherence gradient vanishes.
    The obstruction IS ∇C: the object Chapter 5 names gravity. -/
theorem obstruction_iff (k : ℝ)
    (hNpos : ∀ s y, 0 < n s y) (hCpos : ∀ s y, 0 < c s y)
    (hk : ∀ y, n t y * c t y = k)
    (hnx : HasDerivAt (fun y => n t y) (nx t x) x)
    (hcx : HasDerivAt (fun y => c t y) (cx t x) x) :
    nx t x = 0 ↔ cx t x = 0 := by
  have hobs := arena_obstruction_x n nx t x c cx k hk hnx hcx
  have hn : n t x ≠ 0 := ne_of_gt (hNpos t x)
  have hc : c t x ≠ 0 := ne_of_gt (hCpos t x)
  constructor
  · intro h
    rw [h, zero_mul, zero_add] at hobs
    exact (mul_eq_zero.mp hobs).resolve_left hn
  · intro h
    rw [h, mul_zero, add_zero] at hobs
    exact (mul_eq_zero.mp hobs).resolve_right hc

/-- **Corollary: the flat-in-time patch** — where ∂t N = 0, the ledger is
    pure flux exchange: ∂t ρE + ∂x f = 0. -/
theorem flat_patch
    (hNpos : ∀ s y, 0 < n s y)
    (hφt : HasDerivAt (fun s => φ s x) (pt t x) t)
    (hptt : HasDerivAt (fun s => pt s x) (ptt t x) t)
    (hpxt : HasDerivAt (fun s => px s x) (m t x) t)
    (hptx : HasDerivAt (fun y => pt t y) (m t x) x)
    (hpxx : HasDerivAt (fun y => px t y) (bx t x) x)
    (hnt : HasDerivAt (fun s => n s x) (nt t x) t)
    (hnx : HasDerivAt (fun y => n t y) (nx t x) x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hEL : n t x * ptt t x + (n t x)^3 * V' (φ t x)
         = pt t x * nt t x + (n t x)^2 * nx t x * px t x + (n t x)^3 * bx t x)
    (Et Fx : ℝ)
    (hEt : HasDerivAt (fun s => (pt s x)^2 / (2 * n s x)
        + n s x * ((px s x)^2 / 2 + V (φ s x))) Et t)
    (hFx : HasDerivAt (fun y => -(n t y * (px t y * pt t y))) Fx x)
    (hflat : nt t x = 0) :
    Et + Fx = 0 := by
  have h := sourced_continuity φ pt px ptt m bx n nt nx V V' t x
    hNpos hφt hptt hpxt hptx hpxx hnt hnx hV hEL Et Fx hEt hFx
  rw [hflat] at h
  simpa using h

end PN

#print axioms PN.energy_time_deriv
#print axioms PN.flux_space_deriv
#print axioms PN.sourced_continuity
#print axioms PN.arena_obstruction_x
#print axioms PN.obstruction_iff
#print axioms PN.flat_patch
