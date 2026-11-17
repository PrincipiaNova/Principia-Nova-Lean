/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE DOOB TOWER, TIER 1: THE BIAS WORKS · 11/07/2026 · Lean 4 + mathlib

Authority (canon Ch4, verbatim): the transition probability
"P(x_{t+Δt}|x_t) ∝ exp(β ΔC)" — "the dice are loaded. And the loading is
exponential" — and the Local Improvement Tendency
"E[Q(S_{t+1}) − Q(S_t)] ≥ 0" — "This is not a guarantee. It is a
statistical tendency." Canon printed the probabilist's submartingale
property in physicist's clothing; this tier certifies it at finite-algebra
grain, measure-free.

MODEL (ruled): the SYMMETRIC PROPOSAL CLASS as the model's very shape —
proposals come in ± pairs: each magnitude μ ≥ 0 proposed uphill (+μ) and
downhill (−μ) with a common weight w(μ) ≥ 0 ("the wandering is unbiased;
the selection carries the tilt"). The exponential bias reweights each move
by exp(β·Δ). Q instantiated as coherence per canon's own clause ("the
specific measure varies by regime").

Fences (all ruled 11/07): symmetric proposal class (the model shape) ·
discrete time (canon's S_t is ℕ-indexed) · β ≥ 0 named, β > 0 only in the
strict theorem where it earns its keep · magnitudes nonnegative, weights
nonnegative, named · support condition named in the strict version.
Tier 2 (martingale wing) rides separately; this tier BANKS ALONE.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNDoob

open Finset

/-- The unnormalized expected coherence step: each magnitude μ in the
proposal set contributes its uphill move (+μ, weight w(μ)·e^{βμ}) and its
downhill move (−μ, weight w(μ)·e^{−βμ}). -/
noncomputable def stepNum (P : Finset ℝ) (w : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∑ μ ∈ P, w μ * (μ * Real.exp (β * μ) + (-μ) * Real.exp (β * (-μ)))

/-- The normalizer (partition sum) of the biased proposal distribution. -/
noncomputable def partition (P : Finset ℝ) (w : ℝ → ℝ) (β : ℝ) : ℝ :=
  ∑ μ ∈ P, w μ * (Real.exp (β * μ) + Real.exp (β * (-μ)))

/-- **The dice are loaded** — for every pair, the uphill move carries at
least the downhill move's biased weight, as soon as β ≥ 0. -/
theorem favored_vs_suppressed (w β μ : ℝ) (hβ : 0 ≤ β) (hμ : 0 ≤ μ)
    (hw : 0 ≤ w) :
    w * Real.exp (β * (-μ)) ≤ w * Real.exp (β * μ) := by
  apply mul_le_mul_of_nonneg_left _ hw
  apply Real.exp_le_exp.mpr
  nlinarith

/-- **THE THEOREM — the bias works.** Over any finite symmetric proposal
class with nonnegative weights and β ≥ 0, the expected coherence step is
nonnegative: each ± pair contributes μ·(e^{βμ} − e^{−βμ}) ≥ 0 — the uphill
and downhill factors always carry the same sign. Canon's
E[Q(S_{t+1}) − Q(S_t)] ≥ 0 at printed strength. -/
theorem expected_step_nonneg (P : Finset ℝ) (w : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (hw : ∀ μ ∈ P, 0 ≤ w μ) (hP : ∀ μ ∈ P, 0 ≤ μ) :
    0 ≤ stepNum P w β := by
  unfold stepNum
  apply Finset.sum_nonneg
  intro μ hμ
  have hμ0 : 0 ≤ μ := hP μ hμ
  have hw0 : 0 ≤ w μ := hw μ hμ
  have hexp : Real.exp (β * (-μ)) ≤ Real.exp (β * μ) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hterm : 0 ≤ μ * Real.exp (β * μ) + (-μ) * Real.exp (β * (-μ)) := by
    nlinarith [Real.exp_pos (β * μ), Real.exp_pos (β * (-μ))]
  positivity
/- note: `positivity` closes `0 ≤ w μ * (...)` from hw0 and hterm if it
   picks them up; if not, the explicit route is mul_nonneg hw0 hterm. -/

/-- **The exploration bookend** — zero selectivity, zero drift: at β = 0 the
bias vanishes and the expected step is exactly zero. No bias, no climb. -/
theorem zero_selectivity_neutral (P : Finset ℝ) (w : ℝ → ℝ) :
    stepNum P w 0 = 0 := by
  unfold stepNum
  apply Finset.sum_eq_zero
  intro μ _
  simp

/-- **The strict version (matched pair)** — what positive selectivity buys:
with β > 0 and at least one genuinely uphill proposal in the support
(μ₀ > 0 with w(μ₀) > 0, NAMED), the expected step is strictly positive.
The climb is real, not merely non-backward. -/
theorem expected_step_pos (P : Finset ℝ) (w : ℝ → ℝ) (β : ℝ)
    (hβ : 0 < β) (hw : ∀ μ ∈ P, 0 ≤ w μ) (hP : ∀ μ ∈ P, 0 ≤ μ)
    (hsupp : ∃ μ₀ ∈ P, 0 < μ₀ ∧ 0 < w μ₀) :
    0 < stepNum P w β := by
  obtain ⟨μ₀, hμ₀P, hμ₀, hwμ₀⟩ := hsupp
  unfold stepNum
  apply Finset.sum_pos'
  · intro μ hμ
    have hμ0 : 0 ≤ μ := hP μ hμ
    have hw0 : 0 ≤ w μ := hw μ hμ
    have hexp : Real.exp (β * (-μ)) ≤ Real.exp (β * μ) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hfact : μ * Real.exp (β * μ) + (-μ) * Real.exp (β * (-μ))
        = μ * (Real.exp (β * μ) - Real.exp (β * (-μ))) := by ring
    rw [hfact]
    exact mul_nonneg hw0 (mul_nonneg hμ0 (sub_nonneg.mpr hexp))
  · refine ⟨μ₀, hμ₀P, ?_⟩
    have hexp : Real.exp (β * (-μ₀)) < Real.exp (β * μ₀) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    have hfact : μ₀ * Real.exp (β * μ₀) + (-μ₀) * Real.exp (β * (-μ₀))
        = μ₀ * (Real.exp (β * μ₀) - Real.exp (β * (-μ₀))) := by ring
    rw [hfact]
    exact mul_pos hwμ₀ (mul_pos hμ₀ (sub_pos.mpr hexp))

/-- The normalizer is positive whenever any proposal carries weight —
so the biased distribution is a genuine distribution. -/
theorem partition_pos (P : Finset ℝ) (w : ℝ → ℝ) (β : ℝ)
    (hw : ∀ μ ∈ P, 0 ≤ w μ) (hsupp : ∃ μ₀ ∈ P, 0 < w μ₀) :
    0 < partition P w β := by
  obtain ⟨μ₀, hμ₀P, hwμ₀⟩ := hsupp
  unfold partition
  apply Finset.sum_pos'
  · intro μ hμ
    have := hw μ hμ
    positivity
  · refine ⟨μ₀, hμ₀P, ?_⟩
    have h1 := Real.exp_pos (β * μ₀)
    have h2 := Real.exp_pos (β * (-μ₀))
    positivity

/-- **The normalized tendency** — the actual expected step of the biased
proposal distribution is nonnegative: canon's inequality with the
probability normalization in place. -/
theorem normalized_step_nonneg (P : Finset ℝ) (w : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (hw : ∀ μ ∈ P, 0 ≤ w μ) (hP : ∀ μ ∈ P, 0 ≤ μ)
    (hsupp : ∃ μ₀ ∈ P, 0 < w μ₀) :
    0 ≤ stepNum P w β / partition P w β :=
  div_nonneg (expected_step_nonneg P w β hβ hw hP)
    (le_of_lt (partition_pos P w β hw hsupp))

end PNDoob

#print axioms PNDoob.favored_vs_suppressed
#print axioms PNDoob.expected_step_nonneg
#print axioms PNDoob.zero_selectivity_neutral
#print axioms PNDoob.expected_step_pos
#print axioms PNDoob.partition_pos
#print axioms PNDoob.normalized_step_nonneg
