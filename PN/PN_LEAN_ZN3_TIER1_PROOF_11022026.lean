/-
  PRINCIPIA NOVA — Z-N.3 TIER 1: THE CANON-METRIC CHAIN, KERNEL-CERTIFIED
  11/02/2026 · Lean 4 + mathlib.

  THE N-3 CHAIN (sympy record: PN_NOETHER_RUN_N3_RESULTS_10292026):
  the Z-G.1 metric assembles the matter Lagrangian; the tempo map
  τ = exp(V_C/c²) turns the coherence potential into the clock; the
  B2 Poisson law + Green's-function sign turns the Generative Law
  into the potential's drift. This file certifies every ALGEBRAIC and
  CALCULUS link of that chain, with the two canon fences printed in
  the signatures:

  · hkernel — the Green's-function kernel step V̇_C = −κ_P(G − D_loss)
    (localized-source scope) rides as a NAMED HYPOTHESIS, never
    discharged: exactly the book's printed fence (Z-G.3).
  · hledger — the sourced energy ledger at massless matter + mode
    equipartition, dE/dt = 2(τ̇/τ)E: the shape CERTIFIED at the field
    stage by the Z-N.2 tower (PN_LEAN_ZN2_TIER3), named here rather
    than re-derived.

  THEOREMS
    metric_reduction      : τ⁻²·[½(1/τ²)p_t² − ½τ²g_x² − V]
                              = p_t²/(2τ⁴) − g_x²/2 − V/τ²
                            (the gradient term exits with NO τ — the
                             reciprocal-wiring fingerprint, static form)
    kinetic_coupling      : d/dt [p_t²/(2τ⁴)] = −4(τ̇/τ)·E_kin
    potential_coupling    : d/dt [V/τ²]       = −2(τ̇/τ)·E_V
    gradient_decoupling   : d/dt [g_x²/2]     = 0
                            (the (+4, −2, 0) triple: the PASS-PLUS
                             wiring finding, dynamic form)
    explicit_source       : −dL/dt|fields-fixed = (τ̇/τ)(4E_kin − 2E_V)
    tempo_map             : τ = exp(V_C/c²) ⟹ τ̇ = (V̇_C/c²)·τ
    tempo_pos             : the clock never stops: τ > 0
    clock_rate_from_kernel: with hkernel, τ̇ = (−κ_P(G−D_loss)/c²)·τ
    canon_drift           : THE CAPSTONE — the clock rate is FORCED by
                            derivative uniqueness, and
                            dE/dt = −(2κ_P/c²)·(G − D_loss)·E
-/
import Mathlib

namespace PN3

/-! ## The metric assembly (Z-G.1), pure algebra -/

/-- **The canon metric reduces the matter Lagrangian** — √−g = τ⁻²,
    −g^tt = 1/τ², g^xx = τ² assemble to L = p_t²/(2τ⁴) − g_x²/2 − V/τ².
    The gradient term carries NO power of the clock: the reciprocal
    wiring (the same τ²/τ⁻² choice that passes the 1919 eclipse)
    decouples gradient energy, statically. -/
theorem metric_reduction (τ pt gx V : ℝ) (hτ : τ ≠ 0) :
    (1 / τ ^ 2) * (1 / 2 * (1 / τ ^ 2) * pt ^ 2 - 1 / 2 * τ ^ 2 * gx ^ 2 - V)
      = pt ^ 2 / (2 * τ ^ 4) - gx ^ 2 / 2 - V / τ ^ 2 := by
  field_simp

/-! ## The wiring fingerprint (+4, −2, 0), dynamic form -/

variable (τf : ℝ → ℝ) (τ' pt gx V : ℝ) (t : ℝ)

/-- Kinetic energy couples to the clock at −4(τ̇/τ). -/
theorem kinetic_coupling (hτ : HasDerivAt τf τ' t) (h0 : τf t ≠ 0) :
    HasDerivAt (fun s => pt ^ 2 / (2 * (τf s) ^ 4))
      (-(4 * (τ' / τf t)) * (pt ^ 2 / (2 * (τf t) ^ 4))) t := by
  have hden : HasDerivAt (fun s => 2 * (τf s) ^ 4) (2 * (4 * (τf t) ^ 3 * τ')) t := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hτ.pow 4).const_mul 2
  have h2 : 2 * (τf t) ^ 4 ≠ 0 := by positivity
  have h := (hasDerivAt_const t (pt ^ 2)).div hden h2
  convert h using 1
  field_simp
  ring

/-- Potential energy couples to the clock at −2(τ̇/τ). -/
theorem potential_coupling (hτ : HasDerivAt τf τ' t) (h0 : τf t ≠ 0) :
    HasDerivAt (fun s => V / (τf s) ^ 2)
      (-(2 * (τ' / τf t)) * (V / (τf t) ^ 2)) t := by
  have hden : HasDerivAt (fun s => (τf s) ^ 2) (2 * τf t * τ') t := by
    have h := hτ.pow 2
    convert h using 1
    push_cast
    ring
  have h2 : (τf t) ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have h := (hasDerivAt_const t V).div hden h2
  convert h using 1
  field_simp
  ring

/-- Gradient energy decouples from the clock ENTIRELY: coefficient 0.
    The wiring that bends starlight correctly leaves this fingerprint. -/
theorem gradient_decoupling :
    HasDerivAt (fun _ : ℝ => gx ^ 2 / 2) 0 t :=
  hasDerivAt_const t (gx ^ 2 / 2)

/-- **The explicit source, exact (run result 2):** with the fields held
    fixed, −dL/dt = (τ̇/τ)·(4·E_kin − 2·E_V) — the gradient absent. -/
theorem explicit_source (hτ : HasDerivAt τf τ' t) (h0 : τf t ≠ 0) :
    HasDerivAt (fun s => pt ^ 2 / (2 * (τf s) ^ 4) - gx ^ 2 / 2 - V / (τf s) ^ 2)
      (-((τ' / τf t) * (4 * (pt ^ 2 / (2 * (τf t) ^ 4)) - 2 * (V / (τf t) ^ 2)))) t := by
  have hk := kinetic_coupling τf τ' pt t hτ h0
  have hg := gradient_decoupling gx t
  have hp := potential_coupling τf τ' V t hτ h0
  have h := (hk.sub hg).sub hp
  convert h using 1
  field_simp
  ring

/-! ## The tempo map (Z-G.1) -/

variable (Vc : ℝ → ℝ) (Vc' c : ℝ)

/-- **The tempo map, honest chain rule:** τ = exp(V_C/c²) gives
    τ̇ = (V̇_C/c²)·τ, i.e. τ̇/τ = V̇_C/c². -/
theorem tempo_map (hVc : HasDerivAt Vc Vc' t) :
    HasDerivAt (fun s => Real.exp (Vc s / c ^ 2))
      ((Vc' / c ^ 2) * Real.exp (Vc t / c ^ 2)) t := by
  have h := (hVc.div_const (c ^ 2)).exp
  simpa [mul_comm] using h

/-- The clock never stops: τ = exp(V_C/c²) > 0 everywhere. -/
theorem tempo_pos : 0 < Real.exp (Vc t / c ^ 2) := Real.exp_pos _

/-! ## The kernel step, NAMED, and the canon drift -/

variable (κP Gg Dl : ℝ)

/-- **The clock rate with the kernel step named:** given the
    Green's-function step V̇_C = −κ_P(G − D_loss) — the B2 Poisson law
    with the localized-source sign, the book's printed fence, carried
    here as the hypothesis `hkernel` and never discharged — the clock
    rate is τ̇/τ = −κ_P(G − D_loss)/c². -/
theorem clock_rate_from_kernel (hVc : HasDerivAt Vc Vc' t)
    (hkernel : Vc' = -(κP * (Gg - Dl))) :
    HasDerivAt (fun s => Real.exp (Vc s / c ^ 2))
      ((-(κP * (Gg - Dl)) / c ^ 2) * Real.exp (Vc t / c ^ 2)) t := by
  have h := tempo_map t Vc Vc' c hVc
  rw [hkernel] at h
  exact h

/-- **THE CAPSTONE — Z-N.3 at canon grade: the drift law in the book's
    own symbols.** The rate the ledger runs at is not chosen: any rate
    certified against the tempo clock is FORCED by derivative uniqueness
    to be V̇_C/c². With the kernel step named (`hkernel`) and the sourced
    ledger at massless matter + mode equipartition named (`hledger` —
    the shape the Z-N.2 tower certified from δS = 0), the energy drifts:

        dE/dt = −(2κ_P/c²)·(G − D_loss)·E

    Coherence builds → the well deepens (B2) → the clock slows (tempo
    map) → coordinate energy drains. Three formalisms, one sign. -/
theorem canon_drift (E : ℝ → ℝ) (rate : ℝ)
    (hVc : HasDerivAt Vc Vc' t)
    (hrate : HasDerivAt (fun s => Real.exp (Vc s / c ^ 2))
      (rate * Real.exp (Vc t / c ^ 2)) t)
    (hkernel : Vc' = -(κP * (Gg - Dl)))
    (hledger : HasDerivAt E (2 * rate * E t) t) :
    HasDerivAt E (-(2 * κP / c ^ 2) * (Gg - Dl) * E t) t := by
  have htm := tempo_map t Vc Vc' c hVc
  have hu : rate * Real.exp (Vc t / c ^ 2)
      = (Vc' / c ^ 2) * Real.exp (Vc t / c ^ 2) := hrate.unique htm
  have hr : rate = Vc' / c ^ 2 :=
    mul_right_cancel₀ (Real.exp_ne_zero _) hu
  convert hledger using 1
  rw [hr, hkernel]
  ring

/-- Flat-clock corollary: where G = D_loss, the drift vanishes —
    conservation exact where the clock is flat. -/
theorem flat_clock_limit (E : ℝ → ℝ) (rate : ℝ)
    (hVc : HasDerivAt Vc Vc' t)
    (hrate : HasDerivAt (fun s => Real.exp (Vc s / c ^ 2))
      (rate * Real.exp (Vc t / c ^ 2)) t)
    (hkernel : Vc' = -(κP * (Gg - Dl)))
    (hledger : HasDerivAt E (2 * rate * E t) t)
    (hflat : Gg = Dl) :
    HasDerivAt E 0 t := by
  have h := canon_drift t Vc Vc' c κP Gg Dl E rate hVc hrate hkernel hledger
  rw [hflat] at h
  simpa using h

end PN3

#print axioms PN3.metric_reduction
#print axioms PN3.kinetic_coupling
#print axioms PN3.potential_coupling
#print axioms PN3.gradient_decoupling
#print axioms PN3.explicit_source
#print axioms PN3.tempo_map
#print axioms PN3.tempo_pos
#print axioms PN3.clock_rate_from_kernel
#print axioms PN3.canon_drift
#print axioms PN3.flat_clock_limit
