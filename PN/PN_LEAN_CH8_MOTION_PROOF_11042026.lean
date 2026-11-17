/-
  PRINCIPIA NOVA — THE CH8 MOTION PACKAGE: GRADIENT MOTION, TWO REGIMES
  AND THE BRIDGE, KERNEL-CERTIFIED · 11/04/2026 · Lean 4 + mathlib.

  TWO PRINTED LAWS, ONE CHAPTER:
    Law 2 (Ch8 §3):      a = (k_s/τ_coh)·∇C          (second order)
    Equation 1 (Ch8 §4,
      established Ch4):  dx/dt = F(x) + α_f·ρ·∇C     (first order)
  Canon owns their relationship (Z §14.4): "Pure gradient flow is
  first-order (overdamped) dynamics... The two coincide in the presence
  of strong dissipation" — scope clause quoted in the results doc.

  THE RECORD: the campaign's original lemma claimed the monotone climb for
  "the motion law" without regimes; the fresh canon read caught that it
  fails for the printed Law 2 (a thrown apple climbs against the
  gradient while the law holds). Corrected: the climb lives in Equation
  1's regime; Law 2 gets its honest sign statement (alignment). The
  failure that pays.

  Setting: E a real inner product space (general dimension); the
  gradient is honest Fréchet data (hC: C's derivative at p is ⟪g p, ·⟫);
  k_s, τ, α_f·ρ, γ positive BY NAME; F ≡ 0 named for Regime B.
-/
import Mathlib

namespace PNMotion

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (C : E → ℝ) (g : E → E) (x v a : ℝ → E)

/-! ## Regime A — Law 2 as printed: a = (k_s/τ)·∇C -/

/-- **Acceleration never opposes the gradient:** ⟨a, ∇C⟩ = (k_s/τ)·‖∇C‖².
    "There is no push. There is no pull. There is only a landscape with
    a shape, and the shape has a direction" — as an identity. -/
theorem acceleration_aligned (ks τ t : ℝ)
    (hlaw : a t = (ks / τ) • g (x t)) :
    ⟪a t, g (x t)⟫ = (ks / τ) * ‖g (x t)‖ ^ 2 := by
  rw [hlaw, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- Positive coupling, positive tempo: the alignment is non-negative —
    the acceleration's gradient component never points downhill. -/
theorem no_opposition (ks τ t : ℝ) (hks : 0 < ks) (hτ : 0 < τ)
    (hlaw : a t = (ks / τ) • g (x t)) :
    0 ≤ ⟪a t, g (x t)⟫ := by
  rw [acceleration_aligned g x a ks τ t hlaw]
  positivity

/-- **Equilibrium iff flat:** acceleration vanishes exactly where the
    coherence gradient does. -/
theorem equilibrium_iff (ks τ t : ℝ) (hks : ks ≠ 0) (hτ : τ ≠ 0)
    (hlaw : a t = (ks / τ) • g (x t)) :
    a t = 0 ↔ g (x t) = 0 := by
  rw [hlaw, smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (div_ne_zero hks hτ)
    · exact h
  · exact Or.inr

/-- **The coherence rate along the motion:** dC/dt = ⟪∇C, v⟫ — the chain
    rule on the trajectory; the "nagging pull," quantified. -/
theorem coherence_rate_along_path (t : ℝ)
    (hC : HasFDerivAt C ((innerSL ℝ (g (x t))) : E →L[ℝ] ℝ) (x t))
    (hx : HasDerivAt x (v t) t) :
    HasDerivAt (fun s => C (x s)) ⟪g (x t), v t⟫ t := by
  have h := hC.comp_hasDerivAt t hx
  simp only [innerSL_apply_apply] at h
  exact h

/-- **The Newtonian limit, certified (uniform tempo):** along Law 2's
    motion, ½‖v‖² − (k_s/τ)·C is CONSERVED — the coherence field is the
    potential; "Same number. Same prediction. Different ontology."
    Third appearance of the flat-clock pattern: conservation exact
    where tempo is uniform. -/
theorem newtonian_first_integral (ks τ t : ℝ)
    (hC : HasFDerivAt C ((innerSL ℝ (g (x t))) : E →L[ℝ] ℝ) (x t))
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v (a t) t)
    (hlaw : a t = (ks / τ) • g (x t)) :
    HasDerivAt (fun s => (1 / 2) * ‖v s‖ ^ 2 - (ks / τ) * C (x s)) 0 t := by
  have hvv := hv.inner ℝ hv
  have hnorm : HasDerivAt (fun s => (1 / 2) * ‖v s‖ ^ 2) ⟪a t, v t⟫ t := by
    have h1 : (fun s => (1 / 2) * ‖v s‖ ^ 2)
        = fun s => (1 / 2) * ⟪v s, v s⟫ := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    rw [h1]
    have h2 := hvv.const_mul (1 / 2 : ℝ)
    convert h2 using 1
    rw [real_inner_comm (v t) (a t)]
    ring
  have hCt : HasDerivAt (fun s => (ks / τ) * C (x s))
      ((ks / τ) * ⟪g (x t), v t⟫) t :=
    (coherence_rate_along_path C g x v t hC hx).const_mul (ks / τ)
  have htot := hnorm.sub hCt
  convert htot using 1
  rw [hlaw, real_inner_smul_left]
  ring

/-! ## Regime B — Equation 1 as printed: dx/dt = F(x) + α_f·ρ·∇C,
    with F ≡ 0 (pure coherence drive, NAMED) -/

/-- **The monotone climb, in its home regime:** when velocity follows
    the gradient (Equation 1, F ≡ 0), coherence is non-decreasing along
    the motion: dC/dt = α_f·ρ·‖∇C‖² ≥ 0. The campaign's original lemma,
    corrected to its printed home. -/
theorem flow_regime_climb (αρ t : ℝ) (hαρ : 0 < αρ)
    (hC : HasFDerivAt C ((innerSL ℝ (g (x t))) : E →L[ℝ] ℝ) (x t))
    (hflow : HasDerivAt x (αρ • g (x t)) t) :
    HasDerivAt (fun s => C (x s)) (αρ * ‖g (x t)‖ ^ 2) t
      ∧ 0 ≤ αρ * ‖g (x t)‖ ^ 2 := by
  constructor
  · have h := hC.comp_hasDerivAt t hflow
    have h2 : (innerSL ℝ (g (x t))) (αρ • g (x t))
        = αρ * ‖g (x t)‖ ^ 2 := by
      simp [real_inner_smul_right, real_inner_self_eq_norm_sq]
    rwa [h2] at h
  · positivity

/-- **The climb stalls exactly where the landscape is flat.** -/
theorem flow_stationary_iff (αρ : ℝ) (hαρ : 0 < αρ) (p : E) :
    αρ * ‖g p‖ ^ 2 = 0 ↔ g p = 0 := by
  constructor
  · intro h
    have h2 : ‖g p‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (ne_of_gt hαρ)
      · exact h'
    have h3 : ‖g p‖ = 0 := by nlinarith [norm_nonneg (g p)]
    exact norm_eq_zero.mp h3
  · intro h
    rw [h]
    simp

/-! ## The bridge — one law, two limits (Z §14.4) -/

/-- **THE OVERDAMPED BRIDGE:** add linear drag to Law 2 —
    a = (k_s/τ)·∇C − γ·v — and at the drag-balanced steady state (a = 0)
    the velocity IS the flow law: v = (k_s/(γτ))·∇C. Regime B is Regime
    A's terminal velocity under dissipation: not two laws — one law,
    two limits. γ > 0 and τ > 0 named; Z §14.4 is the authority. -/
theorem overdamped_bridge (ks τ γ t : ℝ) (hτ : 0 < τ) (hγ : 0 < γ)
    (hdrag : a t = (ks / τ) • g (x t) - γ • v t)
    (hsteady : a t = 0) :
    v t = (ks / (γ * τ)) • g (x t) := by
  have h : (ks / τ) • g (x t) - γ • v t = 0 := by
    rw [← hdrag, hsteady]
  have h2 : (ks / τ) • g (x t) = γ • v t := sub_eq_zero.mp h
  have h3 : v t = γ⁻¹ • ((ks / τ) • g (x t)) := by
    rw [h2, smul_smul, inv_mul_cancel₀ (ne_of_gt hγ), one_smul]
  rw [h3, smul_smul]
  congr 1
  field_simp

end PNMotion

#print axioms PNMotion.acceleration_aligned
#print axioms PNMotion.no_opposition
#print axioms PNMotion.equilibrium_iff
#print axioms PNMotion.coherence_rate_along_path
#print axioms PNMotion.newtonian_first_integral
#print axioms PNMotion.flow_regime_climb
#print axioms PNMotion.flow_stationary_iff
#print axioms PNMotion.overdamped_bridge
