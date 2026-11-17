/-
  PRINCIPIA NOVA — THE FORCED EXPONENTIAL (Z-G.5 §A), KERNEL-CERTIFIED
  11/04/2026 · Lean 4 + mathlib.

  Canon's claim (Z-G.2 Stage 1 / Z-G.5 §A): "sources add, tempo responds
  multiplicatively → unique map is exp; guarantees τ > 0 (Mu). Forced,
  not chosen." — Yilmaz POSITED the exponential metric map; PN FORCES it
  from the composition structure alone. This file closes the seam that
  sat beneath `tempo_map` (N-3), which took τ = exp(V_C/c²) as input:
  the exponential form is now derived, not assumed.

  THE HYPOTHESES, NAMED (the fence, per the review flag):
    hmul  — sources add, tempo multiplies: τ(V₁+V₂) = τ(V₁)·τ(V₂)
            (the Cauchy functional equation, multiplicative form —
            canon's composition structure)
    hpos  — τ > 0 (Mu: the clock never stops; also what licenses log)
    hcont — CONTINUITY: the regularity the Cauchy equation requires.
            Without it, pathological (Hamel-basis) solutions exist;
            mathlib's machinery (AddMonoidHom.toRealLinearMap) rightly
            demands it. A physical tempo map is continuous — but the
            hypothesis is NAMED, not smuggled.

  THEOREMS
    zero_calibrated    : τ(0) = 1 is FORCED — the zero-point of the
                         potential carries no freight (calibration
                         invariance's normalization, free)
    forced_exponential : THE THEOREM — any continuous positive solution
                         IS x ↦ exp(k·x), with k = log τ(1) explicit.
                         No existential hedge: the form, with its
                         constant, in closed form.
    mu_guarantee       : the forced form is positive everywhere — the
                         conclusion hands back Mu's guarantee for free
    exp_satisfies      : the converse bookend — exp(k·) satisfies the
                         composition equation (canon's own verification-
                         table identity, exp(k(x+y)) − exp(ky)·exp(kx)=0,
                         as kernel fact)
-/
import Mathlib

namespace PNExp

variable (f : ℝ → ℝ)

/-- **The zero-point is calibrated for free:** any positive solution of
    the composition equation has f(0) = 1 — no privileged zero-point
    freight survives the equation itself. -/
theorem zero_calibrated (hmul : ∀ x y, f (x + y) = f x * f y)
    (hpos : ∀ x, 0 < f x) : f 0 = 1 := by
  have h := hmul 0 0
  rw [add_zero] at h
  have h0 : f 0 ≠ 0 := ne_of_gt (hpos 0)
  field_simp at h
  linarith [h]

/-- **THE FORCED EXPONENTIAL (Z-G.5 §A):** sources add, tempo responds
    multiplicatively, the map is continuous and positive — then the map
    IS the exponential, with its constant in closed form:
    f(x) = exp(log f(1) · x). Yilmaz posited it; the composition
    structure forces it. Continuity is the named fence. -/
theorem forced_exponential (hmul : ∀ x y, f (x + y) = f x * f y)
    (hpos : ∀ x, 0 < f x) (hcont : Continuous f) (x : ℝ) :
    f x = Real.exp (Real.log (f 1) * x) := by
  -- the logarithmic shadow is additive
  set F : ℝ → ℝ := fun y => Real.log (f y) with hF
  have hadd : ∀ a b, F (a + b) = F a + F b := by
    intro a b
    simp only [hF]
    rw [hmul a b, Real.log_mul (ne_of_gt (hpos a)) (ne_of_gt (hpos b))]
  -- and continuous
  have hFcont : Continuous F := hcont.log (fun y => ne_of_gt (hpos y))
  -- mathlib's Cauchy machinery: continuous additive map on ℝ is linear
  let Fhom : ℝ →+ ℝ := AddMonoidHom.mk' F hadd
  let L := Fhom.toRealLinearMap hFcont
  have hLF : ∀ y, L y = F y := fun y =>
    congrFun (AddMonoidHom.coe_toRealLinearMap Fhom hFcont) y
  have hlin : F x = Real.log (f 1) * x := by
    have h1 : L x = L (x • (1 : ℝ)) := by norm_num
    have h2 : L (x • (1 : ℝ)) = x • L 1 := L.map_smul x 1
    have h3 : F x = x * F 1 := by
      rw [← hLF x, h1, h2, smul_eq_mul, hLF 1]
    rw [h3]
    simp only [hF]
    ring
  -- exponentiate back
  rw [← hlin]
  exact (Real.exp_log (hpos x)).symm

/-- **Mu's guarantee, returned by the conclusion:** the forced form is
    positive everywhere — the clock the equation forces can never stop. -/
theorem mu_guarantee (k x : ℝ) : 0 < Real.exp (k * x) := Real.exp_pos _

/-- **The converse bookend — canon's verification-table identity as
    kernel fact:** the exponential satisfies the composition equation,
    exp(k(x+y)) = exp(kx)·exp(ky). -/
theorem exp_satisfies (k x y : ℝ) :
    Real.exp (k * (x + y)) = Real.exp (k * x) * Real.exp (k * y) := by
  rw [← Real.exp_add]
  ring_nf

end PNExp

#print axioms PNExp.zero_calibrated
#print axioms PNExp.forced_exponential
#print axioms PNExp.mu_guarantee
#print axioms PNExp.exp_satisfies
