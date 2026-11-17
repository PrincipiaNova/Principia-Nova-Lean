/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE HIGGS EXPEDITION, TIER 1 · 11/07/2026 · Lean 4 + mathlib
Canon Z §13–14: the Mexican hat, at radial grain.

Authority (canon, verbatim, verified at source): Z §14.1 —
V(Φ) = −μ²|Φ|² + λ|Φ|⁴, μ² > 0, λ > 0; minima on the ring |Φ| = μ/√(2λ);
Φ = (1/√2)(v+h)e^(iθ/v) with v = μ/√λ; m_H² = 2μ² (restated §14.6: "Same
local physics, different global structure"). Z §13 (narrative) + §14.2 echo:
Φ = 0 "was a classical maximum to begin with, so excluding it removes a
state the field never occupied anyway" — excluded, not destabilized.
§14.2: the Mu annulus ε_μ ≤ |Φ| ≤ Φ_max. §14.3: the Mu-bounded vacuum sum
is finite. §14.4: C[Φ] = −V(Φ) (minimal form), P ∝ exp(βΔC) = exp(−βΔV).

Rulings (all approved 11/07): radial grain (the hat is
radial; canon's own demonstration is radial) · hat_profile carries Z §13's
correction as a second-derivative sign · matched pairs (annulus wall+door;
finite-sum wall + divergence door) · boltzmann_bridge in as the one-line
weld to the certified PMD/Doob towers (the Ch4 law).

THE THREE HONESTIES (canon §14.3, pre-printed fences, riding verbatim):
(1) finite is not the same as small — the cosmological constant problem is
NOT resolved here; (2) a hard momentum cutoff is not automatically
gauge-invariant — a gauge-covariant Mu bound is an OPEN problem (§16);
(3) the hierarchy problem stands until Λ_μ is specified — Λ_μ = Λ(C_max)
is the same open specification that blocks the vacuum-energy calculation.
What canon offers instead is mass from topology, not a scalar's vacuum
value (§19) — and that pointer lands on a banked certificate: the winding
tower (PN_LEAN_WINDING_*_11072026), certified before this file was written.

Scope fences: the gauge sector (SU(2)×U(1), Goldstone eating, W/Z masses —
canon Chapter 8 §11) stays prose · §14.5's tempo-linked capture stays prose
· C[Φ] enters only in minimal form C = −V · ε_μ, Φ_max, β are named
hypotheses wherever they appear. λ is spelled `lam` (λ is Lean's binder).
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNHiggs

noncomputable section

/-- Canon §14.1's potential at radial grain: V(r) = −μ²r² + λr⁴ on r = |Φ|. -/
def V (μ lam r : ℝ) : ℝ := -μ^2 * r^2 + lam * r^4

/-! ## MOVEMENT 1 — the hat's profile (calculus grain): critical points and
the curvature signs, including Z §13's printed correction -/

/-- The radial slope of the hat: V′(r) = 2r(2λr² − μ²), everywhere. -/
theorem hat_slope (μ lam r : ℝ) :
    HasDerivAt (V μ lam) (2*r*(2*lam*r^2 - μ^2)) r := by
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*r) r := by
    simpa using hasDerivAt_pow 2 r
  have h4 : HasDerivAt (fun x : ℝ => x^4) (4*r^3) r := by
    simpa using hasDerivAt_pow 4 r
  have h := (h2.const_mul (-μ^2)).add (h4.const_mul lam)
  have hval : -μ^2*(2*r) + lam*(4*r^3) = 2*r*(2*lam*r^2 - μ^2) := by ring
  rw [hval] at h
  exact h

/-- The symmetric point is critical: V′(0) = 0. -/
theorem origin_critical (μ lam : ℝ) : HasDerivAt (V μ lam) 0 0 := by
  have h := hat_slope μ lam 0
  simpa using h

/-- The rim is critical: V′(r) = 0 wherever r² = μ²/(2λ). -/
theorem rim_critical (μ lam r : ℝ) (hlam : lam ≠ 0) (hr : r^2 = μ^2/(2*lam)) :
    HasDerivAt (V μ lam) 0 r := by
  have h := hat_slope μ lam r
  have hz : 2*r*(2*lam*r^2 - μ^2) = 0 := by
    rw [hr]; field_simp; ring
  rwa [hz] at h

/-- The curvature of the hat: V″(r) = −2μ² + 12λr² (the slope's slope),
everywhere. -/
theorem hat_curvature (μ lam r : ℝ) :
    HasDerivAt (fun x => 2*x*(2*lam*x^2 - μ^2)) (-2*μ^2 + 12*lam*r^2) r := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id r
  have h3 : HasDerivAt (fun x : ℝ => x^3) (3*r^2) r := by
    simpa using hasDerivAt_pow 3 r
  have h : HasDerivAt (fun x : ℝ => 4*lam * x^3 + -(2*μ^2) * x)
      (4*lam*(3*r^2) + -(2*μ^2)*1) r :=
    (h3.const_mul (4*lam)).add (h1.const_mul (-(2*μ^2)))
  have hfun : (fun x : ℝ => 4*lam * x^3 + -(2*μ^2) * x)
      = fun x : ℝ => 2*x*(2*lam*x^2 - μ^2) := by
    funext x; ring
  have hval : 4*lam*(3*r^2) + -(2*μ^2)*1 = -2*μ^2 + 12*lam*r^2 := by ring
  rw [hfun, hval] at h
  exact h

/-- **Z §13's printed correction, certified**: at the symmetric point the
curvature is V″(0) = −2μ² < 0 — "Φ = 0 was a classical maximum to begin
with." The false vacuum sits on the hat's crown, not in a dip. -/
theorem origin_is_maximum (μ lam : ℝ) (hμ : μ ≠ 0) :
    HasDerivAt (fun x => 2*x*(2*lam*x^2 - μ^2)) (-(2*μ^2)) 0 ∧ -(2*μ^2) < 0 := by
  constructor
  · have h := hat_curvature μ lam 0
    have : -2*μ^2 + 12*lam*0^2 = -(2*μ^2) := by ring
    rwa [this] at h
  · have : 0 < μ^2 := by positivity
    linarith

/-- At the rim the curvature is V″(r*) = +4μ² > 0 — the trough curves up:
the vacuum ring is a ring of minima, and the restoring stiffness 4μ² is the
radial precursor of m_H² = 2μ² (the ½ from |Φ|² = (v+h)²/2 — see
`higgs_mass`). -/
theorem rim_curvature_positive (μ lam r : ℝ) (hμ : μ ≠ 0) (hlam : lam ≠ 0)
    (hr : r^2 = μ^2/(2*lam)) :
    HasDerivAt (fun x => 2*x*(2*lam*x^2 - μ^2)) (4*μ^2) r ∧ 0 < 4*μ^2 := by
  constructor
  · have h := hat_curvature μ lam r
    have : -2*μ^2 + 12*lam*r^2 = 4*μ^2 := by
      rw [hr]; field_simp; ring
    rwa [this] at h
  · positivity

/-! ## MOVEMENT 2 — the hat's floor (algebraic grain): the whole shape in one
identity, then the global minimum as an iff -/

/-- **The whole hat in one line** — complete the square:
V(r) = λ(r² − μ²/(2λ))² − μ⁴/(4λ). Every global statement below falls out
of this identity. -/
theorem hat_square_identity (μ lam r : ℝ) (hlam : lam ≠ 0) :
    V μ lam r = lam * (r^2 - μ^2/(2*lam))^2 - μ^4/(4*lam) := by
  simp only [V]
  field_simp
  ring

/-- The rim floors the field: −μ⁴/(4λ) ≤ V(r) for every r. The vacuum
energy density canon's hat implies, as a global bound. -/
theorem rim_global_min (μ lam : ℝ) (hlam : 0 < lam) (r : ℝ) :
    -(μ^4/(4*lam)) ≤ V μ lam r := by
  rw [hat_square_identity μ lam r (ne_of_gt hlam)]
  have h : 0 ≤ lam * (r^2 - μ^2/(2*lam))^2 := by positivity
  linarith

/-- **The vacuum depth**: on the rim, V = −μ⁴/(4λ) exactly — the number
Tier 2 handshakes against PhysLean's own bound −μ2²/(4𝓵). -/
theorem vacuum_depth (μ lam r : ℝ) (hlam : lam ≠ 0) (hr : r^2 = μ^2/(2*lam)) :
    V μ lam r = -(μ^4/(4*lam)) := by
  rw [hat_square_identity μ lam r hlam, hr]
  simp

/-- **The minimum located, iff** (§14.1's "minima at |Φ| = μ/√(2λ)" at
radial grain): the floor is attained exactly on the ring r² = μ²/(2λ) —
the same characterization PhysLean's `isMinOn_iff` machinery carries. -/
theorem minimum_iff (μ lam r : ℝ) (hlam : 0 < lam) :
    V μ lam r = -(μ^4/(4*lam)) ↔ r^2 = μ^2/(2*lam) := by
  rw [hat_square_identity μ lam r (ne_of_gt hlam)]
  constructor
  · intro h
    have h1 : lam * (r^2 - μ^2/(2*lam))^2 = 0 := by linarith
    have h2 : (r^2 - μ^2/(2*lam))^2 = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact absurd h' (ne_of_gt hlam)
      · exact h'
    have h3 : r^2 - μ^2/(2*lam) = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  · intro h
    rw [h]
    simp

/-- **§14.1's two printed forms are one fact**: the rim condition
|Φ|² = v²/2 = μ²/(2λ) holds iff v = μ/√λ squared, i.e. v² = μ²/λ. The
1/√2 parametrization bookkeeping, certified — this is where a factor-of-2
error would have lived. -/
theorem vev_reconciliation (μ lam v : ℝ) (hlam : lam ≠ 0) :
    v^2/2 = μ^2/(2*lam) ↔ v^2 = μ^2/lam := by
  rw [div_eq_div_iff (by norm_num) (by positivity), eq_div_iff hlam]
  constructor <;> intro h <;> nlinarith [h]

/-! ## MOVEMENT 3 — the Higgs mass (§14.1 + §14.6, one stone) -/

/-- The radial energy density through |Φ|² = r²/2: Wᵣ(r) = −μ²r²/2 + λr⁴/4.
The fluctuation energy is W(h) = Wᵣ(v + h) — see `fluctuation_slope`. -/
def Wr (μ lam r : ℝ) : ℝ := -μ^2 * r^2/2 + lam * r^4/4

/-- The slope of the radial energy: Wᵣ′(r) = −μ²r + λr³, everywhere. -/
theorem Wr_slope (μ lam r : ℝ) :
    HasDerivAt (Wr μ lam) (-μ^2*r + lam*r^3) r := by
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*r) r := by
    simpa using hasDerivAt_pow 2 r
  have h4 : HasDerivAt (fun x : ℝ => x^4) (4*r^3) r := by
    simpa using hasDerivAt_pow 4 r
  have h : HasDerivAt (fun x : ℝ => -μ^2/2 * x^2 + lam/4 * x^4)
      (-μ^2/2 * (2*r) + lam/4 * (4*r^3)) r :=
    (h2.const_mul (-μ^2/2)).add (h4.const_mul (lam/4))
  have hfun : (fun x : ℝ => -μ^2/2 * x^2 + lam/4 * x^4) = Wr μ lam := by
    funext x; simp only [Wr]; ring
  have hval : -μ^2/2 * (2*r) + lam/4 * (4*r^3) = -μ^2*r + lam*r^3 := by ring
  rw [hfun, hval] at h
  exact h

/-- The fluctuation slope (chain rule through the shift h ↦ v + h):
d/dh Wᵣ(v+h) = −μ²(v+h) + λ(v+h)³, everywhere. -/
theorem fluctuation_slope (μ lam v h₀ : ℝ) :
    HasDerivAt (fun h => Wr μ lam (v + h)) (-μ^2*(v+h₀) + lam*(v+h₀)^3) h₀ := by
  have hin : HasDerivAt (fun h : ℝ => v + h) 1 h₀ := by
    simpa using (hasDerivAt_id h₀).const_add v
  have hout : HasDerivAt (Wr μ lam) (-μ^2*(v+h₀) + lam*(v+h₀)^3) (v + h₀) :=
    Wr_slope μ lam (v + h₀)
  have h := hout.comp h₀ hin
  simp only [Function.comp_def, mul_one] at h
  exact h

/-- **m_H² = 2μ², certified** (§14.1, restated §14.6 as the local-physics
checkpoint): with the vacuum at v² = μ²/λ, the second derivative of the
radial energy in the fluctuation h at h = 0 is exactly 2μ² — the
derivative of the fluctuation slope, taken at the vacuum. "Expanding
around the vacuum, the Higgs mass remains m_H² = ∂²V/∂h²|₀ = 2μ²...
Same local physics, different global structure." -/
theorem higgs_mass (μ lam v : ℝ) (hlam : lam ≠ 0) (hv : v^2 = μ^2/lam) :
    HasDerivAt (fun h => -μ^2*(v+h) + lam*(v+h)^3) (2*μ^2) 0 := by
  have hin : HasDerivAt (fun h : ℝ => v + h) 1 (0:ℝ) := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add v
  have hout : HasDerivAt (fun r : ℝ => -μ^2 * r + lam * r^3)
      (-μ^2 + 3*lam*v^2) (v + 0) := by
    have h1 : HasDerivAt (fun x : ℝ => x) 1 (v+0) := hasDerivAt_id _
    have h3 : HasDerivAt (fun x : ℝ => x^3) (3*(v+0)^2) (v+0) := by
      simpa using hasDerivAt_pow 3 (v+0)
    have h : HasDerivAt (fun x : ℝ => -μ^2 * x + lam * x^3)
        (-μ^2 * 1 + lam * (3*(v+0)^2)) (v+0) :=
      (h1.const_mul (-μ^2)).add (h3.const_mul lam)
    have hval : -μ^2 * 1 + lam * (3*(v+0)^2) = -μ^2 + 3*lam*v^2 := by ring
    rwa [hval] at h
  have h := hout.comp (0:ℝ) hin
  have hval2 : (-μ^2 + 3*lam*v^2) * 1 = 2*μ^2 := by
    have hlv : lam * v^2 = μ^2 := by
      rw [hv]; field_simp
    nlinarith [hlv]
  rw [hval2] at h
  simp only [Function.comp_def] at h
  exact h

/-! ## MOVEMENT 4 — the Mu annulus (§14.2): matched pair.
Wall: the vacuum lives in the annulus. Door: the symmetric point is
EXCLUDED, NOT DESTABILIZED — it is outside the state space by construction
(this theorem), and it was a maximum anyway (`origin_is_maximum`). The
pair IS the distinction. -/

/-- **The annulus hosts the vacuum**: under the named §14.2 hypotheses
ε_μ ≤ r* ≤ Φ_max, the global minimizer of the hat lies inside the Mu
annulus [ε_μ, Φ_max]. -/
theorem annulus_hosts_vacuum (μ lam ε Φmax rstar : ℝ) (hlam : 0 < lam)
    (hr : rstar^2 = μ^2/(2*lam)) (hεr : ε ≤ rstar) (hΦ : rstar ≤ Φmax) :
    rstar ∈ Set.Icc ε Φmax ∧ ∀ r, V μ lam rstar ≤ V μ lam r := by
  refine ⟨⟨hεr, hΦ⟩, fun r => ?_⟩
  rw [vacuum_depth μ lam rstar (ne_of_gt hlam) hr]
  exact rim_global_min μ lam hlam r

/-- **The symmetric point is excluded** (ε_μ > 0): Φ = 0 is not in the
annulus — outside the manifold's state space, removed by construction
rather than by dynamics. "Excluding it removes a state the field never
occupied anyway." -/
theorem symmetric_point_excluded (ε Φmax : ℝ) (hε : 0 < ε) :
    (0:ℝ) ∉ Set.Icc ε Φmax := by
  intro h
  exact absurd h.1 (not_le.mpr hε)

/-! ## MOVEMENT 5 — the vacuum sum (§14.3): matched pair.
Wall: the Mu-bounded sum is finite by construction. Door: without the
bound, positive mode energies cannot sum — the divergence the cutoff
closes. THE THREE HONESTIES RIDE HERE (header): finite ≠ small; the
gauge-covariant cutoff is open (§16); the hierarchy problem stands until
Λ_μ is specified. -/

/-- **The Mu-bounded vacuum sum is a finite real** (§14.3 at stated grain):
over any finite set of modes with nonnegative energies, Σ ωₖ/2 exists and
is nonnegative. Finiteness is by construction — which is exactly canon's
claim, no more. -/
theorem vacuum_sum_finite (s : Finset ℕ) (ω : ℕ → ℝ) (hω : ∀ k, 0 ≤ ω k) :
    0 ≤ ∑ k ∈ s, ω k / 2 :=
  Finset.sum_nonneg fun k _ => div_nonneg (hω k) (by norm_num)

/-- **The door the cutoff closes**: with no bound, mode energies bounded
below by any c > 0 are not summable — the half-quanta pile up without
limit. The divergence §14.3 removes, exhibited. -/
theorem unbounded_sum_diverges (c : ℝ) (hc : 0 < c) (ω : ℕ → ℝ)
    (hω : ∀ k, c ≤ ω k) :
    ¬ Summable (fun k : ℕ => ω k / 2) := by
  intro h
  have h0 := h.tendsto_atTop_zero
  have hlt : ∀ᶠ k in Filter.atTop, ω k / 2 < c/2 :=
    h0.eventually_lt_const (by linarith)
  obtain ⟨k, hk⟩ := hlt.exists
  have : c/2 ≤ ω k / 2 := by linarith [hω k]
  linarith

/-! ## MOVEMENT 6 — the Boltzmann weld (§14.4) -/

/-- **C = −V wires basin selection into the certified towers**: with the
coherence functional in minimal form C[Φ] = −V(Φ), the §14.4 law
P ∝ exp(βΔC) is literally the Ch4 law exp(−βΔV) — the same exponential
weighting whose locking, concentration, and drift theorems are already
kernel-certified (PMD tower: argmax_favored, lock_limit; Doob tower:
expected_step_pos, doob_tower). Basin capture on the rim runs on banked
machinery. -/
theorem boltzmann_bridge {α : Type*} (β : ℝ) (Vf : α → ℝ) (a b : α) :
    Real.exp (β * ((-Vf a) - (-Vf b))) = Real.exp (-(β * (Vf a - Vf b))) := by
  congr 1
  ring

end

end PNHiggs

#print axioms PNHiggs.hat_slope
#print axioms PNHiggs.origin_critical
#print axioms PNHiggs.rim_critical
#print axioms PNHiggs.hat_curvature
#print axioms PNHiggs.origin_is_maximum
#print axioms PNHiggs.rim_curvature_positive
#print axioms PNHiggs.hat_square_identity
#print axioms PNHiggs.rim_global_min
#print axioms PNHiggs.vacuum_depth
#print axioms PNHiggs.minimum_iff
#print axioms PNHiggs.vev_reconciliation
#print axioms PNHiggs.Wr_slope
#print axioms PNHiggs.fluctuation_slope
#print axioms PNHiggs.higgs_mass
#print axioms PNHiggs.annulus_hosts_vacuum
#print axioms PNHiggs.symmetric_point_excluded
#print axioms PNHiggs.vacuum_sum_finite
#print axioms PNHiggs.unbounded_sum_diverges
#print axioms PNHiggs.boltzmann_bridge
