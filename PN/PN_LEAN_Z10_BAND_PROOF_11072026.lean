/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE §10 PALEY–WIENER CHECK · 11/07/2026 · Lean 4 + mathlib
The last stone of the ruled campaign set.

Authority (canon Z §10 "Operators and Dynamics", verbatim, verified at
source): the Mu-bounded effective subspace ℋ_eff = band-limited
states — "itself a named, well-studied object: the Paley–Wiener space" —
free evolution ψ̃ₜ(p) = e^(−ip²t/2mħ)·ψ̃₀(p); "The phase factor does not
change the support"; "ψ₀ ∈ ℋ_eff ⟹ ψₜ ∈ ℋ_eff for all t... The boundary
is never crossed." And the printed door: "convolution enlarges support...
Mu-compatibility is a genuine constraint on interactions, not a property
they have for free" — the open frontier, canon's own claim, which the
witness below proves EXISTS without mapping it. Canon frames the
classification as "the manifold's analogue of renormalizability"; the door
witness is the kernel's handshake with that paragraph — the selection
principle has a certified reason to exist.

Rulings (all approved): momentum-side grain — canon's own demonstration
lives there, so the kernel certifies the printed argument, not a rebuilt
L² unitary framing (which stays classical prose) · support-predicate model
(usual species) · convolution door IN at discrete grain (polynomial
multiplication IS coefficient convolution; witness-grade, named).

Doc lines (ruled in, prose): `spectral_weight_frozen` is the §5 certificate
`hamiltonian_writes_nothing` at Fourier grain — THE TURNING WRITES NOTHING,
two chapters, one engine, two files that now cite each other. And this file
is the formal floor under Ch13's locking machinery and Ch14's Zeno
dissolution ("repeated locking, not freezing"): between measurements only
phase turns (thms 1–3); each measurement re-locks (the PMD tower); only
channels move weight (§5). Zeno-as-repeated-locking: deferred, unqueued.

Phase normal form: e^(−ip²t/2mħ) is written exp(↑θ·I) with
θ = −(p²t)/(2mħ) : ℝ — the printed exponent, coerced once.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNZ10

/-- The Mu band: amplitudes vanish beyond the momentum bound — the
support-fence predicate for canon's ℋ_eff (the Paley–Wiener space, at
momentum-side grain). -/
def InBand (pmax : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ p : ℝ, pmax < |p| → f p = 0

/-- **"The phase factor does not change the support."** A unit phase never
vanishes, so multiplying by it moves no zero in either direction: the
support is exactly preserved. -/
theorem phase_preserves_support (φ : ℝ → ℝ) (f : ℝ → ℂ) (p : ℝ) :
    Complex.exp (↑(φ p) * Complex.I) * f p = 0 ↔ f p = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (Complex.exp_ne_zero _)
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- **"The boundary is never crossed."** The boxed implication at printed
grain: a state in the Mu band stays in the Mu band under free evolution,
for every time — the free phase e^(−ip²t/2mħ) written out. Dynamical
invariance of the Mu-bounded region, kinematic (no watching required). -/
theorem mu_band_invariant (pmax t m ℏ : ℝ) (ψ₀ : ℝ → ℂ)
    (h : InBand pmax ψ₀) :
    InBand pmax fun p =>
      Complex.exp ((((-(p ^ 2 * t) / (2 * m * ℏ) : ℝ)) : ℂ) * Complex.I) * ψ₀ p := by
  intro p hp
  simp only [h p hp, mul_zero]

/-- **The turning writes nothing — Fourier grain.** Free evolution turns
the phase and touches nothing else: every spectral weight is pointwise
frozen, |ψ̃ₜ(p)| = |ψ̃₀(p)|. The same certified shape as §5's
Tr(ρ[H,ρ]) = 0 — two chapters, one engine. Between measurements, there is
nothing for drift to accumulate in the mode weights (the formal floor
under Ch13's locking story and Ch14's Zeno dissolution). -/
theorem spectral_weight_frozen (t m ℏ : ℝ) (ψ₀ : ℝ → ℂ) (p : ℝ) :
    ‖Complex.exp ((((-(p ^ 2 * t) / (2 * m * ℏ) : ℝ)) : ℂ) * Complex.I) * ψ₀ p‖
      = ‖ψ₀ p‖ := by
  rw [norm_mul]
  have h1 : ‖Complex.exp ((((-(p ^ 2 * t) / (2 * m * ℏ) : ℝ)) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]

/-- **THE DOOR — the open frontier exists.** Convolution enlarges support:
at discrete grain (polynomial multiplication IS coefficient convolution),
two band-limited objects — each supported within degree 1 — convolve to
degree exactly 2, out past the band. Canon's claim certified at witness
strength: "Mu-compatibility is a genuine constraint on interactions, not a
property they have for free." The classification of Mu-compatible
interactions remains the open research frontier canon declares — the
witness proves the frontier exists; it does not map it. -/
theorem convolution_door :
    ∃ p q : Polynomial ℝ,
      p.natDegree ≤ 1 ∧ q.natDegree ≤ 1 ∧ (p * q).natDegree = 2 := by
  have hdeg : (Polynomial.X + Polynomial.C (1 : ℝ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C 1
  have hne : (Polynomial.X + Polynomial.C (1 : ℝ)) ≠ 0 :=
    Polynomial.X_add_C_ne_zero 1
  refine ⟨_, _, hdeg.le, hdeg.le, ?_⟩
  rw [Polynomial.natDegree_mul hne hne, hdeg]

end PNZ10

#print axioms PNZ10.phase_preserves_support
#print axioms PNZ10.mu_band_invariant
#print axioms PNZ10.spectral_weight_frozen
#print axioms PNZ10.convolution_door
