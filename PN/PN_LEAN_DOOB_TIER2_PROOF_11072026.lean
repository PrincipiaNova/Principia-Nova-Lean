/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE DOOB TOWER, TIER 2: THE LEDGER'S EXPECTED FACE · 11/07/2026
Lean 4 + mathlib — the martingale wing (first time the program walks it).

Same physics as Tier 1, lifted to full probability-theoretic grain:
filtrations, conditional expectation, mathlib's Submartingale and the
discrete Doob decomposition. Plus the one statement that exists only at
this grain: the process SPLITS, by theorem, into a drift-free fluctuation
(a martingale) and a predictable compensator that only writes forward.

Authority: canon Ch4's Local Improvement Tendency E[Q(S_{t+1}) − Q(S_t)] ≥ 0
("not a guarantee... a statistical tendency") — the submartingale property
in the book's own voice — entering here as the NAMED hypothesis
`himprove` in conditional form, at mathlib's grain.

THE WELD, PROSE ONLY (amendment ruled 11/07): the compensator is the budget
identity's expected face — the deterministic shadow of ∫(G − D_loss) — KIN
to Ch7's certified ledger S = ∫D_loss, not identified with it. A formal
identification would be a g∼τ²-species cross-section ruling; deferred.

Fences: discrete time (ℕ — canon's own S_t grain) · regularity at mathlib's
grain, named (StronglyAdapted, Integrable, SigmaFiniteFiltration — the
HasDerivAt-citizenship of the stochastic column) · Q instantiated as
coherence per canon's "the specific measure varies by regime."
Tier 1 (banked separately) certifies the tendency in the finite model;
this tier takes the tendency as premise and delivers the decomposition.
The formal Tier-1→Tier-2 bridge (constructing the Markov measure from the
proposal model) is deferred as a construction expedition.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

open MeasureTheory

namespace PNDoob2

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {C : ℕ → Ω → ℝ}

/-- **Canon's tendency ⟹ submartingale.** The Local Improvement Tendency in
conditional form — the expected step given the present is nonnegative
(`himprove`, canon's printed inequality as named hypothesis) — makes the
coherence process a submartingale, at mathlib's own definition. -/
theorem submartingale_of_improvement_tendency [SigmaFiniteFiltration μ ℱ]
    (hadp : StronglyAdapted ℱ C) (hint : ∀ n, Integrable (C n) μ)
    (himprove : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[C j - C i | ℱ i]) :
    Submartingale C ℱ μ :=
  submartingale_iff_condExp_sub_nonneg.mpr ⟨hadp, hint, himprove⟩

/-- **The Doob split** — the process separates, by theorem, into fluctuation
plus drift: martingale part + predictable part = C. Consumed from mathlib's
discrete Doob decomposition. -/
theorem doob_split (ℱ : Filtration ℕ m0) (μ : Measure Ω) (C : ℕ → Ω → ℝ) :
    martingalePart C ℱ μ + predictablePart C ℱ μ = C :=
  martingalePart_add_predictablePart ℱ μ C

/-- **The fluctuation is fair** — the martingale part carries no drift:
it is a genuine martingale. The noise, certified noise. -/
theorem fluctuation_is_fair [SigmaFiniteFiltration μ ℱ]
    (hadp : StronglyAdapted ℱ C) (hint : ∀ n, Integrable (C n) μ) :
    Martingale (martingalePart C ℱ μ) ℱ μ :=
  martingale_martingalePart hadp hint

/-- **The compensator only writes forward** — for a submartingale, the
predictable part is almost surely monotone: the drift accumulates and never
erases. (Prose weld, per ruling: this is the budget identity's expected
face — kin to Ch7's ledger, not identified with it.) -/
theorem compensator_monotone (hsub : Submartingale C ℱ μ) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart C ℱ μ · ω) :=
  hsub.monotone_predictablePart

/-- The compensator starts at zero and never goes below it. -/
theorem compensator_nonneg (hsub : Submartingale C ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart C ℱ μ n ω :=
  hsub.predictablePart_nonneg

/-- **CAPSTONE — the Doob tower.** From canon's Local Improvement Tendency
(named, conditional form) and the stochastic column's regularity fences:
the coherence process is a submartingale; it splits exactly into a fair
fluctuation plus a predictable drift; and that drift is almost surely
monotone and nonnegative — the expected climb, separated from the noise by
theorem, writing forward only. -/
theorem doob_tower [SigmaFiniteFiltration μ ℱ]
    (hadp : StronglyAdapted ℱ C) (hint : ∀ n, Integrable (C n) μ)
    (himprove : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[C j - C i | ℱ i]) :
    Submartingale C ℱ μ ∧
    martingalePart C ℱ μ + predictablePart C ℱ μ = C ∧
    Martingale (martingalePart C ℱ μ) ℱ μ ∧
    (∀ᵐ ω ∂μ, Monotone (predictablePart C ℱ μ · ω)) ∧
    (∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart C ℱ μ n ω) := by
  have hsub := submartingale_of_improvement_tendency hadp hint himprove
  exact ⟨hsub, doob_split ℱ μ C, fluctuation_is_fair hadp hint,
    compensator_monotone hsub, compensator_nonneg hsub⟩

end PNDoob2

#print axioms PNDoob2.submartingale_of_improvement_tendency
#print axioms PNDoob2.doob_split
#print axioms PNDoob2.fluctuation_is_fair
#print axioms PNDoob2.compensator_monotone
#print axioms PNDoob2.compensator_nonneg
#print axioms PNDoob2.doob_tower
