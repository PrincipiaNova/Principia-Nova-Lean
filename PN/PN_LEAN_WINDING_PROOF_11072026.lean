/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE WINDING TOWER (CH8 §6 / CH20 §8 / §22), KERNEL-CERTIFIED
11/07/2026 · Lean 4 + mathlib · AXIOM 3's TOPOLOGICAL FACE — THE THIRD FACE

Authority (canon, verbatim, all three sections checked character-level):
· Ch8 §6: "W_C = (1/2π)∮∇φ_C·dl ∈ ℤ ... It either winds around once, or
  twice, or not at all. 1, 2, 0. Never 1.5. Never 0.7." · "You cannot
  gradually unwind a winding number from 1 to 0 ... The only way to change
  it is to tear the field — a discrete, discontinuous event."
· Ch20 §8: "the CMD motif library IS a topology library ... cannot change by
  smooth deformation, only by discrete reorganization events" · and the
  PRINTED FENCE: "thermal fluctuations are stochastic, not smooth ... The
  protection is not a wall. It is a very deep well."
· §22: "dW/dt = 0 under smooth deformation ... tears typically create
  defects in ± pairs with net zero — σ therefore monitors individual
  winding numbers, never only their sum."

FORMULATION (ruled): phase-data — the loop carried by its phase θ along the
parameter, the lift given as NAMED DATA (hθ; gradient-as-data species).
Canon's own formula is already in phase terms, so this formalizes the
object the book prints, not the π₁ classification it never claims.
Deferred lemma marked: `phase_lift_exists` (classical path-lifting through
the exp covering) would discharge the hθ fence in every signature at once,
purely additively.

THE MATCHED PAIR (Ch20's sentence in kernel form): `no_gradual_unwinding`
certifies the WALL against continuous deformation; `discrete_jump_witness`
exhibits the DOOR — and proves its own discontinuity FROM the wall theorem.
The continuity hypothesis is load-bearing because canon printed the
boundary itself: smooth cannot change W; stochastic can.

Fences: phase lift named (hθ); continuity/differentiability named;
invariance certified as connected-family constancy — never π₁(S¹) ≅ ℤ,
which canon never claims. Statement-level coverage only.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNWind

open intervalIntegral

/-- **The integer** — "Never 1.5. Never 0.7." A closed loop (the phase
returns: e^{iθ₁} = e^{iθ₀}) forces the total phase change into 2πℤ, and the
winding number (θ₁ − θ₀)/2π is an integer. Topology demands integers, via
the periodicity of exp (donor: `Complex.exp_eq_exp_iff_exists_int`). -/
theorem winding_integer (θ₀ θ₁ : ℝ)
    (hclose : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₀ * Complex.I)) :
    ∃ k : ℤ, θ₁ - θ₀ = 2 * Real.pi * k ∧ (θ₁ - θ₀) / (2 * Real.pi) = k := by
  rw [Complex.exp_eq_exp_iff_exists_int] at hclose
  obtain ⟨n, hn⟩ := hclose
  have hn' : (θ₁ : ℂ) * Complex.I
      = ((θ₀ : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
    rw [hn]; ring
  have hC := mul_right_cancel₀ Complex.I_ne_zero hn'
  have hR : θ₁ = θ₀ + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hC
  refine ⟨n, by linear_combination hR, ?_⟩
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp
  linear_combination hR

/-- **The printed formula** — W = (1/2π)∮∇φ·dl as the integral of the phase
derivative: the FTC bridge from canon's loop integral to the endpoint
difference the integer theorem counts. -/
theorem winding_via_integral (θ dθ : ℝ → ℝ)
    (hθ : ∀ t, HasDerivAt θ (dθ t) t)
    (hcont : Continuous dθ) :
    (1 / (2 * Real.pi)) * ∫ t in (0:ℝ)..1, dθ t = (θ 1 - θ 0) / (2 * Real.pi) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hθ t)
    (hcont.intervalIntegrable 0 1)]
  ring

/-- **THE WALL — "you cannot gradually unwind a winding number from 1 to 0."**
A continuous deformation family whose winding is integer-valued at every
parameter is CONSTANT: the integral form of canon's dW/dt = 0 under smooth
deformation. The continuity hypothesis is canon's own printed boundary
(Ch20: "stochastic, not smooth") — load-bearing, not convenient. Proof: a
continuous path between distinct integers must pass through k + ½, which no
integer-valued function reaches (intermediate value). -/
theorem no_gradual_unwinding (W : ℝ → ℝ) (hcont : Continuous W)
    (hint : ∀ s, ∃ k : ℤ, W s = k) :
    ∀ s₁ s₂ : ℝ, W s₁ = W s₂ := by
  have key : ∀ a b : ℝ, a ≤ b → W a = W b := by
    intro a b hab
    by_contra hne
    obtain ⟨ka, hka⟩ := hint a
    obtain ⟨kb, hkb⟩ := hint b
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hk : (ka : ℝ) < kb := by rw [← hka, ← hkb]; exact hlt
      have hkz : ka < kb := by exact_mod_cast hk
      have hstep : (ka : ℝ) + 1 ≤ kb := by exact_mod_cast hkz
      have hmid : (ka : ℝ) + 1 / 2 ∈ Set.Icc (W a) (W b) := by
        constructor
        · rw [hka]; linarith
        · rw [hkb]; linarith
      obtain ⟨s, _, hs⟩ := intermediate_value_Icc hab hcont.continuousOn hmid
      obtain ⟨m, hm⟩ := hint s
      rw [hm] at hs
      have h2 : (2 * m : ℤ) = 2 * ka + 1 := by
        have h2R : ((2 * m : ℤ) : ℝ) = ((2 * ka + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast h2R
      omega
    · have hk : (kb : ℝ) < ka := by rw [← hka, ← hkb]; exact hlt
      have hkz : kb < ka := by exact_mod_cast hk
      have hstep : (kb : ℝ) + 1 ≤ ka := by exact_mod_cast hkz
      have hmid : (kb : ℝ) + 1 / 2 ∈ Set.Icc (W b) (W a) := by
        constructor
        · rw [hkb]; linarith
        · rw [hka]; linarith
      obtain ⟨s, _, hs⟩ := intermediate_value_Icc' hab hcont.continuousOn hmid
      obtain ⟨m, hm⟩ := hint s
      rw [hm] at hs
      have h2 : (2 * m : ℤ) = 2 * kb + 1 := by
        have h2R : ((2 * m : ℤ) : ℝ) = ((2 * kb + 1 : ℤ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast h2R
      omega
  intro s₁ s₂
  rcases le_total s₁ s₂ with h | h
  · exact key s₁ s₂ h
  · exact (key s₂ s₁ h).symm

/-- **The tear quantum** — "a discrete, discontinuous event": when a winding
number changes at all, it changes by at least one whole click. -/
theorem tear_quantum (W₁ W₂ : ℤ) (h : W₁ ≠ W₂) : 1 ≤ |W₁ - W₂| :=
  Int.one_le_abs (sub_ne_zero.mpr h)

/-- **The trivial loop** — constant phase, zero winding: k_self = 1's
topological cousin. The three-faces connection (trivial loop = trivial
winding) as a one-liner. -/
theorem trivial_loop (θ : ℝ → ℝ) (hconst : ∀ t, θ t = θ 0) :
    (θ 1 - θ 0) / (2 * Real.pi) = (0 : ℤ) := by
  rw [hconst 1]
  simp

/-- **The pair-creation blind spot** — §22's printed design consequence:
a ± pair appears, the total is unchanged (0 + 0 = 1 + (−1)), the individuals
are not. σ must monitor individual winding numbers, never only their sum. -/
theorem pair_creation_blind_spot :
    (0 : ℤ) + 0 = 1 + (-1) ∧ (1 : ℤ) ≠ 0 ∧ (-1 : ℤ) ≠ 0 := by
  norm_num

/-- **THE DOOR — the sharpness shot.** An integer-valued deformation family
that DOES change its winding exists — and it is necessarily discontinuous,
proved from the wall theorem itself (contrapositive of
`no_gradual_unwinding`). Ch20's sentence in kernel form: the protection is
a wall against continuous paths and a door for discrete events — "not a
wall... a very deep well," with the door exactly where continuity fails. -/
theorem discrete_jump_witness :
    ∃ W : ℝ → ℝ, (∀ s, ∃ k : ℤ, W s = k) ∧ W 0 ≠ W 1 ∧ ¬Continuous W := by
  classical
  refine ⟨fun s => if s < 1 then (0 : ℝ) else 1, fun s => ?_, ?_, ?_⟩
  · by_cases h : s < 1
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · norm_num
  · intro hc
    have hint : ∀ s : ℝ, ∃ k : ℤ, (if s < 1 then (0 : ℝ) else 1) = k := by
      intro s
      by_cases h : s < 1
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    have := no_gradual_unwinding _ hc hint 0 1
    norm_num at this

end PNWind

#print axioms PNWind.winding_integer
#print axioms PNWind.winding_via_integral
#print axioms PNWind.no_gradual_unwinding
#print axioms PNWind.tear_quantum
#print axioms PNWind.trivial_loop
#print axioms PNWind.pair_creation_blind_spot
#print axioms PNWind.discrete_jump_witness
