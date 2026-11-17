/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE HIGGS EXPEDITION, TIER 2 · 11/07/2026 · Lean 4 + PhysLean
The handshake file: canon's hat against the community's own formal record.

THE PROGRAM'S FIRST PHYSICS-FORMALIZATION CONSUMPTION. PhysLean
(Physlib.Particles.StandardModel.HiggsBoson.Potential) carries the Standard
Model Higgs potential under its own name — structure Potential {μ2, 𝓵},
toFun = −μ2‖φ‖² + 𝓵‖φ‖⁴ over HiggsField × SpaceTime. The theorems below
are statement-fidelity checks: canon Z §14.1's printed quantities (the
potential's form, the minimum ring, the vacuum depth, the stability
direction) equal PhysLean's, under the explicit dictionary
P.μ2 = μ² and P.𝓵 = λ, carried as NAMED HYPOTHESES in every signature —
no convention is assumed silently. λ is spelled `lam` (Lean binder).

Ruling honored (11/07, ruling 4 — emphatic): Tier 2 exists
ONLY because the PhysLean module builds in our snapshot (verified: 3,368
jobs, clean). The donors are the community's own record; a hand-rebuilt
imitation would be a mirror pretending to be a witness, and would have
stayed out.

THE THREE HONESTIES (canon §14.3) ride here exactly as in Tier 1:
finite ≠ small (CC not resolved) · gauge-covariant cutoff OPEN (§16) ·
hierarchy stands until Λ_μ is specified. m_H² = 2μ² is certified in
Tier 1; its naturalness is NOT claimed anywhere. Canon's own alternative —
mass from topology, not a scalar's vacuum value (§19) — points at the
banked winding tower. The gauge sector (Ch8 §11) stays prose.
═══════════════════════════════════════════════════════════════════════════════
-/
import Physlib.Particles.StandardModel.HiggsBoson.Potential

namespace PNHiggsT2

open StandardModel HiggsField
open scoped StandardModel.HiggsField

/-- **The master donor, consumed**: PhysLean's own global-minimum
characterization, both phases in one theorem — broken (0 ≤ μ2: the rim
‖φ‖² = μ2/(2𝓵)) and unbroken (μ2 < 0: the origin). The community's record
of the Mexican hat's floor, held. -/
theorem physlean_minimum_consumed (P : Potential) (h𝓵 : 0 < P.𝓵)
    (φ : HiggsField) (x : SpaceTime) :
    IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    (0 ≤ P.μ2 ∧ ‖φ‖_H^2 x = P.μ2 / (2 * P.𝓵)) ∨ (P.μ2 < 0 ∧ φ x = 0) :=
  P.isMinOn_iff_field_of_𝓵_pos h𝓵 φ x

/-- **The potential-form handshake**: under the dictionary, PhysLean's
toFun IS canon's V read through |Φ|² — the §14.1 hat and the formalized
hat are the same polynomial in the norm-squared. Both sides chose the
same hat; the factor-of-2 trap does not exist. -/
theorem potential_form_handshake (P : Potential) (μ lam : ℝ)
    (hμ : P.μ2 = μ^2) (hlam : P.𝓵 = lam) (φ : HiggsField) (x : SpaceTime) :
    P.toFun φ x = -μ^2 * (‖φ‖_H^2 x) + lam * (‖φ‖_H^2 x)^2 := by
  rw [Potential.toFun, hμ, hlam]
  ring

/-- **The convention handshake** (§14.1's minimum ring, statement-fidelity):
under the dictionary, PhysLean's global-minimum condition is EXACTLY
canon's rim condition |Φ|² = μ²/(2λ) — the flight plan's audit table as a
theorem. -/
theorem convention_handshake (P : Potential) (μ lam : ℝ)
    (hμ : P.μ2 = μ^2) (hlam : P.𝓵 = lam) (hlam0 : 0 < lam)
    (φ : HiggsField) (x : SpaceTime) :
    IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
    ‖φ‖_H^2 x = μ^2 / (2*lam) := by
  have h𝓵 : 0 < P.𝓵 := by rw [hlam]; exact hlam0
  have hμ2 : 0 ≤ P.μ2 := by rw [hμ]; positivity
  rw [P.isMinOn_iff_field_of_μSq_nonneg_𝓵_pos h𝓵 hμ2 φ x, hμ, hlam]

/-- **The vacuum-depth handshake**: canon's floor −μ⁴/(4λ) (Tier 1's
`vacuum_depth`) is PhysLean's own bound −μ2²/(4𝓵) under the dictionary —
the bound holds everywhere (donor: pos_𝓵_quadDiscrim_zero_bound) and is
attained exactly at the global minima (donor: isMinOn_iff_of_μSq_nonneg).
Two formalizations, one number. -/
theorem vacuum_depth_handshake (P : Potential) (μ lam : ℝ)
    (hμ : P.μ2 = μ^2) (hlam : P.𝓵 = lam) (hlam0 : 0 < lam) :
    (∀ (φ : HiggsField) (x : SpaceTime), -μ^4/(4*lam) ≤ P.toFun φ x) ∧
    (∀ (φ : HiggsField) (x : SpaceTime),
      IsMinOn (fun (φ, x) => P.toFun φ x) Set.univ (φ, x) ↔
      P.toFun φ x = -μ^4/(4*lam)) := by
  have h𝓵 : 0 < P.𝓵 := by rw [hlam]; exact hlam0
  have hμ2 : 0 ≤ P.μ2 := by rw [hμ]; positivity
  have hdepth : -P.μ2^2/(4*P.𝓵) = -μ^4/(4*lam) := by
    rw [hμ, hlam]; ring
  constructor
  · intro φ x
    rw [← hdepth]
    exact P.pos_𝓵_quadDiscrim_zero_bound h𝓵 φ x
  · intro φ x
    rw [← hdepth]
    exact P.isMinOn_iff_of_μSq_nonneg_𝓵_pos h𝓵 hμ2 φ x

/-- **The stability direction** (§14.1's λ > 0 doing its printed job):
λ > 0 suffices for the potential to be bounded below, and boundedness
forces λ ≥ 0. Stated as two directions, not an iff — PhysLean leaves the
λ = 0 edge informal (it depends on the sign of μ2), and the ladder never
climbs above what the donor proves. -/
theorem stability_direction (P : Potential) :
    (0 < P.𝓵 → P.IsBounded) ∧ (P.IsBounded → 0 ≤ P.𝓵) :=
  ⟨P.isBounded_of_𝓵_pos, P.isBounded_𝓵_nonneg⟩

end PNHiggsT2

#print axioms PNHiggsT2.physlean_minimum_consumed
#print axioms PNHiggsT2.potential_form_handshake
#print axioms PNHiggsT2.convention_handshake
#print axioms PNHiggsT2.vacuum_depth_handshake
#print axioms PNHiggsT2.stability_direction
