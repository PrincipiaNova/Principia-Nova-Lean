/-
  PRINCIPIA NOVA — Z-N.1 DRIFT LAW: TIER 2 (ANALYSIS GRADE)
  11/02/2026 · Lean 4 + mathlib — real functions, honest derivatives.

  UPGRADE OVER TIER 1 (PN_LEAN_ZN1_PROOF_10292026.lean):
  Tier 1 proved the drift law over an abstract commutative algebra with
  a formal derivation — the algebra was certified, but d/dt was a symbol.
  Here every object is a genuine real function of time and d/dt is
  mathlib's HasDerivAt: the chain rule, product rule and quotient rule
  are THEOREMS used, not axioms assumed. Division is real division,
  licensed by N > 0 (the lapse is a clock rate; clocks tick forward).

  THE MODEL (Z-N.1, canon): L = q̇²/(2N) − N·V(q), lapse N = τ_coh.
  Euler–Lagrange equation, denominators cleared:
      N·a = v·Ṅ − N³·V′(q)        (hEL below)
  Energy:  E(t) = v(t)²/(2·N(t)) + N(t)·V(q(t))   — with real division.

  THEOREM drift_law   :  E′(t) = (Ṅ(t)/N(t)) · E(t)
  THEOREM flat_clock  :  Ṅ(t) = 0  →  E′(t) = 0
  THEOREM substrate_conservation :  (E/N)′(t) = 0
      — the substrate-time energy E_s = E/N is EXACTLY conserved:
        the same identity read in the substrate's own clock.

  Scope, stated plainly: the EL equation enters as a hypothesis about
  real functions (exactly as the sympy runs take it on-shell). Deriving
  EL from the action functional inside Lean is the remaining layer
  (mathlib's calculus of variations is thin; PhysLean inventory next).
-/
import Mathlib

namespace PN

/-- **Z-N.1 drift law, analysis grade.**
    Real functions, mathlib derivatives, real division (N > 0).
    From the Euler–Lagrange equation of L = q̇²/(2N) − N·V alone:
    the energy E = v²/(2N) + N·V(q) drifts as E′ = (Ṅ/N)·E. -/
theorem drift_law
    (q v a N N' V V' : ℝ → ℝ) (t : ℝ)
    (hNpos : ∀ s, 0 < N s)
    (hq : ∀ s, HasDerivAt q (v s) s)
    (hv : HasDerivAt v (a t) t)
    (hN : HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hEL : N t * a t = v t * N' t - (N t)^3 * V' (q t)) :
    HasDerivAt (fun s => (v s)^2 / (2 * N s) + N s * V (q s))
      ((N' t / N t) * ((v t)^2 / (2 * N t) + N t * V (q t))) t := by
  have hNt : N t ≠ 0 := ne_of_gt (hNpos t)
  have h2Nt : 2 * N t ≠ 0 := by positivity
  -- kinetic piece: v²/(2N), built from raw mathlib combinators
  have hnum := hv.pow 2
  have hden : HasDerivAt (fun s => 2 * N s) (2 * N' t) t := hN.const_mul 2
  have hkin := hnum.div hden h2Nt
  -- potential piece: N·V(q), chain rule then product rule
  have hVq : HasDerivAt (fun s => V (q s)) (V' (q t) * v t) t :=
    (hV (q t)).comp t (hq t)
  have hpot := hN.mul hVq
  -- assemble; all algebra deferred to the endgame
  have htot := hkin.add hpot
  convert htot using 1
  have hELa : a t = (v t * N' t - (N t)^3 * V' (q t)) / N t := by
    rw [eq_div_iff hNt]
    linear_combination hEL
  rw [hELa]
  push_cast
  field_simp
  simp only [Pi.pow_apply]
  ring

/-- **Corollary: flat clock ⇒ exact conservation.** -/
theorem flat_clock
    (q v a N N' V V' : ℝ → ℝ) (t : ℝ)
    (hNpos : ∀ s, 0 < N s)
    (hq : ∀ s, HasDerivAt q (v s) s)
    (hv : HasDerivAt v (a t) t)
    (hN : HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hEL : N t * a t = v t * N' t - (N t)^3 * V' (q t))
    (hflat : N' t = 0) :
    HasDerivAt (fun s => (v s)^2 / (2 * N s) + N s * V (q s)) 0 t := by
  have h := drift_law q v a N N' V V' t hNpos hq hv hN hV hEL
  convert h using 1
  rw [hflat]
  simp

/-- **Corollary: substrate-time conservation, E_s = E/N exactly conserved.**
    The drift law and the substrate conservation are ONE identity read in
    two clocks: dE_s/dt = (E′N − EN′)/N² = 0 follows from E′ = (N′/N)E. -/
theorem substrate_conservation
    (q v a N N' V V' : ℝ → ℝ) (t : ℝ)
    (hNpos : ∀ s, 0 < N s)
    (hq : ∀ s, HasDerivAt q (v s) s)
    (hv : HasDerivAt v (a t) t)
    (hN : ∀ s, HasDerivAt N (N' s) s)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hEL : N t * a t = v t * N' t - (N t)^3 * V' (q t)) :
    HasDerivAt (fun s => ((v s)^2 / (2 * N s) + N s * V (q s)) / N s) 0 t := by
  have hNt : N t ≠ 0 := ne_of_gt (hNpos t)
  have hE := drift_law q v a N N' V V' t hNpos hq hv (hN t) hV hEL
  have h := hE.div (hN t) hNt
  convert h using 1
  field_simp
  ring

end PN

#print axioms PN.drift_law
#print axioms PN.flat_clock
#print axioms PN.substrate_conservation
