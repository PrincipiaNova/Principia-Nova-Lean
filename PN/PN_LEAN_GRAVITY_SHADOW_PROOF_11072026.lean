/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE GRAVITY SHADOW · 11/07/2026 · Lean 4 + mathlib
The gravity sector's first kernel entry: Ch5's shadow + Z-G's printed forms.

Authorities (canon, verbatim, verified at source, character-checked):
· Ch5 §3: "The coherence gradient in three-dimensional space obeys the same
  inverse-square falloff as the Newtonian gravitational field... a geometric
  property of any field diverging from a source in three dimensions."
· Ch5 §3 (Cavendish): "coherence gradients coexist additively... In the
  weak-field limit, coherence gradients superpose linearly" — gradient
  ADDITIVITY, weak-field; distinct from quantum superposition (Z Axiom 1),
  the two passages fencing each other through the low-curvature limit.
· Z-G.1: τ = exp(V_C/c²), ∇²V_C = 4πG·C_density (B2) · the
  Papapetrou (1954)/Yilmaz (1958) exponential metric — prior art named by
  canon itself, and here.
· Z-G.2: "Nordström 1913 failed because one scalar turned both dials by the
  same conformal factor → light (conformally blind) sails straight. Fix:
  one scalar τ wired reciprocally into time and space." · c_L = c·τ²
  ("Cone slope goes with tempo squared") · exp map "Forced, not chosen" —
  Z-G.5 §A, ALREADY KERNEL-CERTIFIED 11/04 (forced-exponential climb).
· Z-G.3: the point-mass residual M²e^(−2M/r)/r⁴ ∝ (∇V_C)² — "the 'vacuum'
  carries coherence-gradient stress."
· Z-G.4: no horizon ("tempo → 0, never reaches it... approaching but never
  reaching Mu") · throat R(r) = r·e^(M/r), min at r = M, R = e·M ·
  Kretschmann K = M²(28M² − 64Mr + 48r²)e^(−4M/r)/r⁸, K(M) = 12e⁻⁴/M⁴,
  K → 0 both ends; Schwarzschild comparator 48M²/r⁶ → ∞.

RULINGS (approved 11/07): radial/component grain — NOT GR-in-Lean
(no manifolds, no tensors; the certified objects are the printed component
functions and their 1D calculus, the grain Z-G itself computes at) · cone-
slope species for the Nordström table (deflection integrals stay sympy,
Z-G.4 campaign) · strong-field structural claims as calculus facts ·
candidate 14 recast: the printed residual IS (e^Φ·Φ′)², two
exponential powers and all · throat minimum stated GLOBAL (upgraded at certification) ·
STANDING RULING, SPENT BY DECISION: "Z-G.4 resolved as printed-form
certification; the derive-from-the-metric branch stays deferred as future
work" — the 11/02 queue's last Z-G entry closes here.

Fences: numeric test table (deflection arcsec, PPN, perihelion, shadow
+4.6%, ringdown, frame drag) stays sympy permanently · Ch5's "C is not a
pure scalar" rides — the radial model certifies the scalar shadow · aether/
rotation caveats ride as printed (Z-G.4 a–b) · the sourcing constant (G's
value) remains the open composition-law/Noether item · M > 0, r > 0, τ ≠ 0
named hypotheses throughout. PhysLean checked and ruled out: its Relativity
wing is special-relativistic only; no curved-metric donors exist anywhere —
no imitation donors (Higgs ruling-4 discipline).

Cross-reference (ruled in): `reciprocal_cone` is the banked
`slope_ratio_is_kfac` identity (CRVL Tier 2, 11/04) flanked by its two
failed comparators — one identity, two appearances; the new certified
content is the CONTRAST and the τ-cancellation reason-why.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNGravShadow

noncomputable section

open Real Filter

/-! ## MOVEMENT 1 — the Ch5 shadow: the apple, the lead ball -/

/-- **The inverse square is geometry, not gravity** (Ch5 §3's printed
sentence as an iff): a radial field conserves its flux through nested
shells precisely when it falls off as 1/r². Gauss bookkeeping — kin to the
Zeroth Law's `flux_balance`, one scale up. -/
theorem flux_inverse_square (F : ℝ → ℝ) (Φ₀ : ℝ) :
    (∀ r : ℝ, 0 < r → 4*Real.pi*r^2 * F r = Φ₀) ↔
    (∀ r : ℝ, 0 < r → F r = Φ₀/(4*Real.pi*r^2)) := by
  constructor
  · intro h r hr
    have h2 : 4*Real.pi*r^2 ≠ 0 := by positivity
    rw [eq_div_iff h2]
    linear_combination h r hr
  · intro h r hr
    have h2 : 4*Real.pi*r^2 ≠ 0 := by positivity
    rw [h r hr]
    field_simp

/-- **B2's vacuum solution** (Z-G.1's ∇²V_C = 4πG·C_density, away from the
source): the potential V = −M/r has slope M/r² (the inverse-square pull,
from the potential), curvature −2M/r³, and vanishing radial Laplacian
V″ + (2/r)V′ = 0 — harmonic where the source is not. -/
theorem potential_harmonic (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => -M/x) (M/r^2) r ∧
    HasDerivAt (fun x : ℝ => M/x^2) (-(2*M)/r^3) r ∧
    -(2*M)/r^3 + (2/r)*(M/r^2) = 0 := by
  refine ⟨?_, ?_, by field_simp; ring⟩
  · have h1 : HasDerivAt (fun x : ℝ => x⁻¹) (-(r^2)⁻¹) r := hasDerivAt_inv hr
    have h : HasDerivAt (fun x : ℝ => -M * x⁻¹) (-M * -(r^2)⁻¹) r :=
      h1.const_mul (-M)
    have hfun : (fun x : ℝ => -M * x⁻¹) = fun x : ℝ => -M/x := by
      funext x; rw [div_eq_mul_inv]
    have hval : -M * -(r^2)⁻¹ = M/r^2 := by
      field_simp
    rw [hfun, hval] at h
    exact h
  · have h2 : HasDerivAt (fun x : ℝ => x^2) (2*r) r := by
      simpa using hasDerivAt_pow 2 r
    have hinv : HasDerivAt (fun x : ℝ => (x^2)⁻¹) (-(2*r)/(r^2)^2) r :=
      h2.inv (pow_ne_zero 2 hr)
    have h : HasDerivAt (fun x : ℝ => M * (x^2)⁻¹) (M * (-(2*r)/(r^2)^2)) r :=
      hinv.const_mul M
    have hfun : (fun x : ℝ => M * (x^2)⁻¹) = fun x : ℝ => M/x^2 := by
      funext x; rw [div_eq_mul_inv]
    have hval : M * (-(2*r)/(r^2)^2) = -(2*M)/r^3 := by
      field_simp
    rw [hfun, hval] at h
    exact h

/-- **The Cavendish sentence at radial grain** (Ch5 §3, named in canon's own
words): coherence gradients coexist additively — two sources, two coexisting
pulls, the net response exactly their sum. Weak-field gradient additivity,
not quantum superposition. -/
theorem gradients_coexist_additively (V₁ V₂ : ℝ → ℝ) (g₁ g₂ r : ℝ)
    (h₁ : HasDerivAt V₁ g₁ r) (h₂ : HasDerivAt V₂ g₂ r) :
    HasDerivAt (fun x => V₁ x + V₂ x) (g₁ + g₂) r :=
  h₁.add h₂

/-! ## MOVEMENT 2 — the wiring that bent the light (Z-G.2's table, cone
grain). The null condition −g₀₀·1 + g_xx·s² = 0 fixes the light-cone slope
s at a point of tempo τ. Three wirings, three slopes: τ⁰, τ¹, τ². The
deflection integrals (0″ / 0.8756″ / 1.7512″) stay in the Z-G.4 sympy
campaign. -/

/-- **Nordström's blindness, certified** (Z-G.2: "one scalar turned both
dials by the same conformal factor → light sails straight"): under the
conformal wiring g = τ²η, the null condition forces slope² = 1 — **τ cancels
identically**. Light cannot see a dial turned twice the same way. The
wiring killed by the 1919 eclipse, for the reason canon prints. -/
theorem conformal_blindness (τ s : ℝ) (hτ : τ ≠ 0) :
    -τ^2 + τ^2 * s^2 = 0 ↔ s^2 = 1 := by
  have h2 : τ^2 ≠ 0 := pow_ne_zero 2 hτ
  constructor
  · intro h
    have h3 : τ^2 * (s^2 - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact absurd h' h2
    · linarith
  · intro h
    rw [h]
    ring

/-- The time-only wiring (g₀₀ = −τ², space flat): slope² = τ² — the
Newton-value wiring (0.8756″, half the observed deflection; also killed
1919). One dial is not enough. -/
theorem time_only_cone (τ s : ℝ) :
    -τ^2 + s^2 = 0 ↔ s^2 = τ^2 := by
  constructor <;> intro h <;> linarith

/-- **The reciprocal wiring — the two-dial identity c_L = c·τ², certified**
(Z-G.2's amendment to B1: "Cone slope goes with tempo squared"): under
g₀₀ = −τ², g_xx = τ⁻², the null condition forces slope² = τ⁴ — light speed
τ². The 1919 wiring. Cross-ref: the banked `slope_ratio_is_kfac` (CRVL
Tier 2, 11/04) — one identity, two appearances; the certified news here is
the three-slope CONTRAST: τ⁰ (blind), τ¹ (half), τ² (observed). -/
theorem reciprocal_cone (τ s : ℝ) (hτ : τ ≠ 0) :
    -τ^2 + s^2/τ^2 = 0 ↔ s^2 = τ^4 := by
  have h2 : τ^2 ≠ 0 := pow_ne_zero 2 hτ
  constructor
  · intro h
    have h3 : s^2/τ^2 = τ^2 := by linarith
    rw [div_eq_iff h2] at h3
    rw [h3]
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-! ## MOVEMENT 3 — the strong-field edge (Z-G.4's printed formulas as
calculus facts). Φ = −M/r, τ = e^Φ — the exponential map itself certified
as FORCED on 11/04 (Z-G.5 §A). -/

/-- **No horizon** (Z-G.4): g₀₀ = −e^(2Φ) never vanishes — e^(2Φ(r)) > 0
for every r. The certificate is `Real.exp_pos` doing exactly what canon
says the Mu bound does. -/
theorem no_horizon (M r : ℝ) : 0 < Real.exp (2*(-M/r)) :=
  Real.exp_pos _

/-- **Tempo approaches zero and never arrives** (Z-G.4: "tempo → 0, never
reaches it... the book's 'approaching but never reaching Mu'"): as r → 0⁺,
e^(2Φ) → 0 — while `no_horizon` holds at every r. Mu's
asymptote-not-arrival, fourth appearance in the record. -/
theorem tempo_asymptote (M : ℝ) (hM : 0 < M) :
    Tendsto (fun r : ℝ => Real.exp (2*(-M/r))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have h1 : Tendsto (fun r : ℝ => r⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun r : ℝ => (2*M) * r⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    h1.const_mul_atTop (by positivity)
  have h3 : Tendsto (fun r : ℝ => -((2*M) * r⁻¹)) (nhdsWithin 0 (Set.Ioi 0)) atBot :=
    tendsto_neg_atTop_atBot.comp h2
  have h4 := Real.tendsto_exp_atBot.comp h3
  refine h4.congr fun r => ?_
  simp only [Function.comp_apply]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- **The throat's slope** (Z-G.4): the areal radius R(r) = r·e^(M/r) has
R′(r) = e^(M/r)·(1 − M/r) exactly — zero precisely where r = M. -/
theorem throat_slope (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => x * Real.exp (M/x))
      (Real.exp (M/r) * (1 - M/r)) r := by
  have hVin : HasDerivAt (fun x : ℝ => M * x⁻¹) (M * -(r^2)⁻¹) r :=
    (hasDerivAt_inv hr).const_mul M
  have hVfun : (fun x : ℝ => M * x⁻¹) = fun x : ℝ => M/x := by
    funext x; rw [div_eq_mul_inv]
  rw [hVfun] at hVin
  have hexp := (Real.hasDerivAt_exp (M/r)).comp r hVin
  simp only [Function.comp_def] at hexp
  -- hexp : HasDerivAt (fun x => exp (M/x)) (exp (M/r) * (M * -(r^2)⁻¹)) r
  have hid : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id r
  have h := hid.mul hexp
  -- h : HasDerivAt (fun x => x * exp (M/x))
  --       (1 * exp (M/r) + r * (exp (M/r) * (M * -(r^2)⁻¹))) r
  have hval : 1 * Real.exp (M/r) + r * (Real.exp (M/r) * (M * -(r^2)⁻¹))
      = Real.exp (M/r) * (1 - M/r) := by
    field_simp
    ring
  rwa [hval] at h

/-- **The throat located** (Z-G.4): at r = M the slope vanishes and
R(M) = e·M — the convergence throat as a certified critical point, with the
printed minimum value. -/
theorem throat_critical (M : ℝ) (hM : M ≠ 0) :
    HasDerivAt (fun x : ℝ => x * Real.exp (M/x)) 0 M ∧
    M * Real.exp (M/M) = M * Real.exp 1 := by
  constructor
  · have h := throat_slope M M hM
    have hz : Real.exp (M/M) * (1 - M/M) = 0 := by
      rw [div_self hM]
      ring
    rwa [hz] at h
  · rw [div_self hM]

/-- **The throat's curvature** (re-derived, clean closed form): the slope
function S(r) = e^(M/r)(1 − M/r) has S′(r) = e^(M/r)·M²/r³ — strictly
positive for M ≠ 0, r > 0. The critical point curves up. -/
theorem throat_curvature (M r : ℝ) (hM : M ≠ 0) (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => Real.exp (M/x) * (1 - M/x))
      (Real.exp (M/r) * M^2/r^3) r ∧ 0 < Real.exp (M/r) * M^2/r^3 := by
  constructor
  · have hr' : r ≠ 0 := ne_of_gt hr
    have hVin : HasDerivAt (fun x : ℝ => M * x⁻¹) (M * -(r^2)⁻¹) r :=
      (hasDerivAt_inv hr').const_mul M
    have hVfun : (fun x : ℝ => M * x⁻¹) = fun x : ℝ => M/x := by
      funext x; rw [div_eq_mul_inv]
    rw [hVfun] at hVin
    have hexp := (Real.hasDerivAt_exp (M/r)).comp r hVin
    simp only [Function.comp_def] at hexp
    have hlin : HasDerivAt (fun x : ℝ => 1 - M/x) (-(M * -(r^2)⁻¹)) r :=
      hVin.const_sub 1
    have h := hexp.mul hlin
    have hval : (Real.exp (M/r) * (M * -(r^2)⁻¹)) * (1 - M/r)
        + Real.exp (M/r) * -(M * -(r^2)⁻¹)
        = Real.exp (M/r) * M^2/r^3 := by
      field_simp
      ring
    rwa [hval] at h
  · have h1 := Real.exp_pos (M/r)
    have h2 : 0 < M^2 := by positivity
    have h3 : 0 < r^3 := by positivity
    positivity

/-- **The throat is the GLOBAL minimum** (upgraded at certification — free and
stronger): for every r > 0, R(r) = r·e^(M/r) ≥ e·M, via the classic
exponential bound. Equality at r = M (`throat_critical`). No destination
claimed; a floor certified. (The proof needs no sign on M — the floor
holds for every real M; the physical case is M > 0.) -/
theorem throat_global_min (M r : ℝ) (hr : 0 < r) :
    M * Real.exp 1 ≤ r * Real.exp (M/r) := by
  have hb : M/r ≤ Real.exp (M/r - 1) := by
    have h := Real.add_one_le_exp (M/r - 1)
    linarith
  have hsplit : Real.exp (M/r) = Real.exp 1 * Real.exp (M/r - 1) := by
    rw [← Real.exp_add]
    ring_nf
  have h4 : M ≤ r * Real.exp (M/r - 1) := by
    have h := mul_le_mul_of_nonneg_left hb hr.le
    rwa [mul_div_cancel₀ M (ne_of_gt hr)] at h
  calc M * Real.exp 1
      ≤ (r * Real.exp (M/r - 1)) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos 1).le
    _ = r * Real.exp (M/r) := by rw [hsplit]; ring

/-- The Kretschmann scalar of the exponential metric (Z-G.4, printed form). -/
def K (M r : ℝ) : ℝ :=
  M^2 * (28*M^2 - 64*M*r + 48*r^2) * Real.exp (-4*M/r) / r^8

/-- **The throat's curvature invariant** (Z-G.4's printed number):
K(M) = 12e⁻⁴/M⁴ — the arithmetic 28 − 64 + 48 = 12, certified in place. -/
theorem kretschmann_at_throat (M : ℝ) (hM : M ≠ 0) :
    K M M = 12 * Real.exp (-4) / M^4 := by
  unfold K
  have harg : -4*M/M = (-4 : ℝ) := by
    field_simp
  rw [harg]
  field_simp
  ring

/-- **The invariant is strictly positive everywhere** — finiteness with
content: the quadratic 48r² − 64Mr + 28M² has negative discriminant
(3·(that) = (6r − 4M)² + 5M² + 32r²... certified by square witness), so
K(r) > 0 for every r > 0, M ≠ 0. No zero, no blow-up, no sign change. -/
theorem kretschmann_pos (M r : ℝ) (hM : M ≠ 0) (hr : 0 < r) :
    0 < K M r := by
  unfold K
  have hquad : 0 < 28*M^2 - 64*M*r + 48*r^2 := by
    nlinarith [sq_nonneg (6*r - 4*M), sq_nonneg M, sq_nonneg (M - r)]
  have hexp := Real.exp_pos (-4*M/r)
  have hM2 : 0 < M^2 := by positivity
  have hr8 : 0 < r^8 := by positivity
  positivity

/-- **No singularity** (Z-G.4: "K → 0 as r → ∞ and as r → 0"): the hard
end certified — as r → 0⁺ the exponential kills the pole and K → 0.
No infinite tidal force where GR has one. -/
theorem no_singularity_limit (M : ℝ) (hM : 0 < M) :
    Tendsto (K M) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Step 1: u^8 · e^(−4Mu) → 0 at infinity (the exponential beats the pole)
  have hg : Tendsto (fun u : ℝ => u^8 * Real.exp (-(4*M*u))) atTop (nhds 0) := by
    have hpow := tendsto_pow_mul_exp_neg_atTop_nhds_zero 8
    have hcomp : Tendsto (fun u : ℝ => 4*M*u) atTop atTop := by
      have hid : Tendsto (fun u : ℝ => u) atTop atTop := tendsto_id
      exact hid.const_mul_atTop (by positivity)
    have h0 := hpow.comp hcomp
    simp only [Function.comp_def] at h0
    -- h0 : Tendsto (fun u => (4*M*u)^8 * exp (-(4*M*u))) atTop (nhds 0)
    have h1 := h0.const_mul (((4*M)^8)⁻¹)
    rw [mul_zero] at h1
    refine h1.congr fun u => ?_
    have h4M : ((4:ℝ)*M)^8 ≠ 0 := by positivity
    field_simp
  -- Step 2: compose with r ↦ r⁻¹ to land at 0⁺
  have hcompinv := hg.comp tendsto_inv_nhdsGT_zero
  simp only [Function.comp_def] at hcompinv
  -- Step 3: the polynomial factor tends to its value at 0
  have hpoly : Tendsto (fun r : ℝ => M^2 * (28*M^2 - 64*M*r + 48*r^2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (M^2 * (28*M^2 - 64*M*0 + 48*0^2))) :=
    (Continuous.tendsto (by continuity) 0).mono_left nhdsWithin_le_nhds
  -- Step 4: product → const · 0 = 0
  have h := hpoly.mul hcompinv
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (r:ℝ) ≠ 0 := ne_of_gt hr
  show M^2 * (28*M^2 - 64*M*r + 48*r^2) * ((r⁻¹)^8 * Real.exp (-(4*M*r⁻¹)))
      = K M r
  unfold K
  have harg : -4*M/r = -(4*M*r⁻¹) := by
    rw [div_eq_mul_inv]
    ring
  rw [harg]
  field_simp

/-- **The Schwarzschild door** (matched pair): the GR comparator
48M²/r⁶ → ∞ as r → 0⁺ — the curvature blow-up the exponential metric
removes, exhibited. Wall and door, §14.3 house style. -/
theorem schwarzschild_door (M : ℝ) (hM : M ≠ 0) :
    Tendsto (fun r : ℝ => 48*M^2/r^6) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have h1 : Tendsto (fun r : ℝ => r⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have h6 : Tendsto (fun x : ℝ => x^6) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have h2 := h6.comp h1
  have h3 := h2.const_mul_atTop (show (0:ℝ) < 48*M^2 by positivity)
  refine h3.congr fun r => ?_
  simp only [Function.comp_apply]
  rw [div_eq_mul_inv]
  ring

/-- **The vacuum's gradient stress** (Z-G.3, recast): the printed
point-mass residual M²e^(−2M/r)/r⁴ IS the square of the tempo-weighted
gradient — (e^Φ·Φ′)² with Φ = −M/r, both exponential powers accounted.
Canon's "∝ (∇V_C)²" sentence as a term-for-term identity: the 'vacuum'
carries coherence-gradient stress. -/
theorem gradient_stress_identity (M r : ℝ) (hr : r ≠ 0) :
    M^2 * Real.exp (-2*M/r) / r^4
      = (Real.exp (-M/r) * (M/r^2))^2 := by
  have hexp : (Real.exp (-M/r))^2 = Real.exp (-2*M/r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hexp, div_pow]
  field_simp

end

end PNGravShadow

#print axioms PNGravShadow.flux_inverse_square
#print axioms PNGravShadow.potential_harmonic
#print axioms PNGravShadow.gradients_coexist_additively
#print axioms PNGravShadow.conformal_blindness
#print axioms PNGravShadow.time_only_cone
#print axioms PNGravShadow.reciprocal_cone
#print axioms PNGravShadow.no_horizon
#print axioms PNGravShadow.tempo_asymptote
#print axioms PNGravShadow.throat_slope
#print axioms PNGravShadow.throat_critical
#print axioms PNGravShadow.throat_curvature
#print axioms PNGravShadow.throat_global_min
#print axioms PNGravShadow.kretschmann_at_throat
#print axioms PNGravShadow.kretschmann_pos
#print axioms PNGravShadow.no_singularity_limit
#print axioms PNGravShadow.schwarzschild_door
#print axioms PNGravShadow.gradient_stress_identity
