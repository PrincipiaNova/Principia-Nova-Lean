/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE FRW ANCHOR, KERNEL-CERTIFIED · 11/07/2026 · Lean 4 + mathlib

Authority (canon, Z-N.2 anchor paragraph): "Run on an expanding background —
the mainstream's own conceded instance of the Noether failure — it returns the
radiation redshift law dE/dt = −(ȧ/a)·E symbolically, and a numerical mode
integration holds the adiabatic invariant E·a constant to one part in a
thousand while E itself falls by half across a doubling of the scale factor."

Standing fence (Z-N.4): "the FRW numeric gate remains the symbolic run's
record, since proof kernels do not run numeric campaigns." The sympy column
holds the integration; this file holds the EXACT law those numbers were
approximating. Two columns, pointing at each other, neither doing the
other's job.

STRUCTURAL POINT, LED WITH: ZERO PN PREMISES APPEAR IN ANY SIGNATURE.
The anchor's epistemic job in Z-N.2 was to run before the framework's objects
entered — the calibration shot on the textbook case. This file mirrors that
status: pure textbook cosmology, no framework hypotheses, kernel-grade,
sitting beside the files where PN's premises are worn openly.

Fences: a(t) > 0 (scale-factor positivity); differentiability of E and a
carried as HasDerivAt hypotheses (regularity, named); statements on the whole
time axis (interval scoping is a routine restriction). E(t₀) ≠ 0 named in the
ratio corollary only — the product form, primary, needs no such hypothesis
(amendment honored: the product E·a can be constant at zero).
Deliberately out: the numeric mode integration (sympy's record, permanently);
any lapse↔1/a weld to the N-1 drift law (the records ran the anchor
standalone; that weld is a g_grav-species ruling for another day, if ever).
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNFRW

/-- **The adiabatic invariant.** The printed law dE/dt = −(ȧ/a)·E, with the
scale factor positive, forces d(E·a)/dt = 0: the product rule turns the
redshift law into the invariant — the −Eȧ and +Eȧ cancel exactly. -/
theorem adiabatic_invariant (E a da : ℝ → ℝ) (t : ℝ)
    (hlaw : HasDerivAt E (-(da t / a t) * E t) t)
    (ha : HasDerivAt a (da t) t)
    (hapos : 0 < a t) :
    HasDerivAt (fun s => E s * a s) 0 t := by
  have h := hlaw.mul ha
  have hane : a t ≠ 0 := ne_of_gt hapos
  convert h using 1
  field_simp
  ring

/-- **The invariant is constant**: E·a takes the same value at every time. -/
theorem invariant_constant (E a da : ℝ → ℝ)
    (hlaw : ∀ t, HasDerivAt E (-(da t / a t) * E t) t)
    (ha : ∀ t, HasDerivAt a (da t) t)
    (hapos : ∀ t, 0 < a t) :
    ∀ s t : ℝ, E t * a t = E s * a s := by
  intro s t
  have hinv : ∀ u, HasDerivAt (fun r => E r * a r) 0 u := fun u =>
    adiabatic_invariant E a da u (hlaw u) (ha u) (hapos u)
  have hdiff : Differentiable ℝ (fun r => E r * a r) := fun u =>
    (hinv u).differentiableAt
  have hderiv : ∀ u, deriv (fun r => E r * a r) u = 0 := fun u =>
    (hinv u).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv t s

/-- **The redshift law, product form (PRIMARY).** E(t₁)·a(t₁) = E(t₀)·a(t₀):
canon's adiabatic invariant as an exact equality, no hypothesis beyond the
law itself. (Amendment honored: the product form carries no E ≠ 0 clause.) -/
theorem redshift_product (E a da : ℝ → ℝ) (t₀ t₁ : ℝ)
    (hlaw : ∀ t, HasDerivAt E (-(da t / a t) * E t) t)
    (ha : ∀ t, HasDerivAt a (da t) t)
    (hapos : ∀ t, 0 < a t) :
    E t₁ * a t₁ = E t₀ * a t₀ :=
  invariant_constant E a da hlaw ha hapos t₀ t₁

/-- **The redshift law, ratio form (corollary).** E(t₁)/E(t₀) = a(t₀)/a(t₁) —
the textbook 1+z law — with the physical nondegeneracy E(t₀) ≠ 0 NAMED
(the one line of honesty the ratio needs that the product does not). -/
theorem redshift_ratio (E a da : ℝ → ℝ) (t₀ t₁ : ℝ)
    (hlaw : ∀ t, HasDerivAt E (-(da t / a t) * E t) t)
    (ha : ∀ t, HasDerivAt a (da t) t)
    (hapos : ∀ t, 0 < a t)
    (hE0 : E t₀ ≠ 0) :
    E t₁ / E t₀ = a t₀ / a t₁ := by
  have hprod := redshift_product E a da t₀ t₁ hlaw ha hapos
  have ha1 : a t₁ ≠ 0 := ne_of_gt (hapos t₁)
  rw [div_eq_div_iff hE0 ha1]
  linarith [hprod]

/-- **The halving witness — THE anchor theorem.** The scale factor doubles ⟹
the energy exactly halves. The sympy column held this to one part in a
thousand across a numerical mode integration; the kernel column holds it to
equality. The numeric gate stays sympy's record; this is the exact law it
was approximating. -/
theorem halving_witness (E a da : ℝ → ℝ) (t₀ t₁ : ℝ)
    (hlaw : ∀ t, HasDerivAt E (-(da t / a t) * E t) t)
    (ha : ∀ t, HasDerivAt a (da t) t)
    (hapos : ∀ t, 0 < a t)
    (hdouble : a t₁ = 2 * a t₀) :
    E t₁ = E t₀ / 2 := by
  have hprod := redshift_product E a da t₀ t₁ hlaw ha hapos
  have ha0 : a t₀ ≠ 0 := ne_of_gt (hapos t₀)
  rw [hdouble] at hprod
  have h2 : E t₁ * 2 * a t₀ = E t₀ * a t₀ := by ring_nf; ring_nf at hprod; linarith
  have h3 : E t₁ * 2 = E t₀ := mul_right_cancel₀ ha0 h2
  linarith

/-- **The flat-clock bookend.** ȧ ≡ 0 ⟹ E is constant: exact conservation
where the clock is flat. The FOURTH appearance of the flat-clock pattern in
the program — substrate (`substrate_conservation`), kinematic
(`sr_ceiling_at_k1`), mechanical (`newtonian_first_integral`), and now
cosmological. -/
theorem flat_clock_bookend (E a da : ℝ → ℝ)
    (hlaw : ∀ t, HasDerivAt E (-(da t / a t) * E t) t)
    (hflat : ∀ t, da t = 0) :
    ∀ s t : ℝ, E t = E s := by
  intro s t
  have hE0 : ∀ u, HasDerivAt E 0 u := by
    intro u
    have h := hlaw u
    simpa [hflat u] using h
  have hdiff : Differentiable ℝ E := fun u => (hE0 u).differentiableAt
  have hderiv : ∀ u, deriv E u = 0 := fun u => (hE0 u).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv t s

end PNFRW

#print axioms PNFRW.adiabatic_invariant
#print axioms PNFRW.invariant_constant
#print axioms PNFRW.redshift_product
#print axioms PNFRW.redshift_ratio
#print axioms PNFRW.halving_witness
#print axioms PNFRW.flat_clock_bookend
