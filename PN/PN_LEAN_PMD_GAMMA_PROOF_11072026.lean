/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE PMD SELECTION + Γ-DIAL TOWER · 11/07/2026 · Lean 4 + mathlib
CHAPTER 5'S FIRST KERNEL ENTRY · ninth climb of the day

Authorities (verbatim, character-checked; flight plan PN_PMD_GAMMA_
FLIGHT_PLAN_11072026, approved with amendments 1–3, all honored):
· Ch4 (certified as the Doob tower): P ∝ exp(βΔC); β the selectivity;
  high-β locks, low-β explores.
· Ch5 §3: PMD "not as a new axiom, but as a consequence of what Chapter 4
  already established... the inevitable result of F_coh and P ∝ exp(βΔC)."
· Ch5 §4: δ∫D dt = 0 — "the coherence framework's equivalent of the
  principle of least action." CANON'S OWN FENCE: "not meant for
  computation" — so the E–L treatment stays out; only the OBJECTIVE's
  two faces enter, welded by the certified budget identity.
· Ch6 (AMENDMENT 1 — authority corrected from Ch7; canon self-cites
  "D_loss = τ · Γ (Chapter 6)" in Ch10 and Ch13): the bridge equation
  D_loss = τ_coh·Γ; Γ ∈ [0,1] with BOTH ends "Mu-forbidden in practice";
  S = ∫τ_coh·Γ dt. Ch7 supplies the ledger side (already certified).
· Ch13 §4, BY SCOPE RULING (11/07): admitted as LIMIT-READING ONLY —
  "only one mode remains structurally stable" enters exclusively as the
  exact β → ∞ limit, paired with its finite-β Mu guarantee. The Ch13
  skip otherwise stands; lock-strength regimes stay parked.

Rulings honored: finite-mode model (UNIFORM base weights in theorem 1,
amendment 2; top mode in support structural, amendment 3) · StrictAnti
C↔D link named · unique strict maximum named in the lock limit · fixed-G
clause named · tempo-law link named as hypothesis, never identification.
No ≈ anywhere: all =, ≥, and exact limits (Tendsto atTop quantifies over
finite β only — the asymptote-not-arrival reading, cannot_arrive's family).
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

open Filter

namespace PNPMD

/-! ## MOVEMENT 1 — PMD Selection (Ch4 → Ch5, with Ch13 §4 as limit) -/

/-- **Selection at any selectivity.** Uniform base weights (amendment 2):
the biased weight of a mode is exp(β·C). The most coherent mode carries
the largest weight for every β ≥ 0, strictly when β > 0 and it strictly
leads. -/
theorem argmax_favored {ι : Type*} (M : Finset ι) (C : ι → ℝ) (β : ℝ)
    (i₀ : ι) (hmax : ∀ j ∈ M, C j ≤ C i₀) (hβ : 0 ≤ β) :
    (∀ j ∈ M, Real.exp (β * C j) ≤ Real.exp (β * C i₀)) ∧
    (0 < β → ∀ j ∈ M, C j < C i₀ → Real.exp (β * C j) < Real.exp (β * C i₀)) := by
  constructor
  · intro j hj
    apply Real.exp_le_exp.mpr
    nlinarith [hmax j hj]
  · intro hβ0 j _ hlt
    apply Real.exp_lt_exp.mpr
    nlinarith

/-- **THE LOCK LIMIT — Ch13 §4's sentence as an exact limit.** With a
unique strict maximum (NAMED) in the support (structural: i₀ ∈ M), the
biased distribution's weight on the most coherent mode tends to 1 as
β → ∞: "only one mode remains structurally stable", certified as the
high-selectivity idealization. Proved over finite β only — the asymptote
is approached, never occupied. -/
theorem lock_limit {ι : Type*} [DecidableEq ι] (M : Finset ι) (C : ι → ℝ)
    (i₀ : ι) (hi₀ : i₀ ∈ M)
    (hstrict : ∀ j ∈ M, j ≠ i₀ → C j < C i₀) :
    Tendsto (fun β : ℝ => Real.exp (β * C i₀) / ∑ j ∈ M, Real.exp (β * C j))
      atTop (nhds 1) := by
  -- Rewrite the share as 1 / ∑ exp(β·(C j − C i₀)).
  have hrw : ∀ β : ℝ,
      Real.exp (β * C i₀) / ∑ j ∈ M, Real.exp (β * C j)
        = 1 / ∑ j ∈ M, Real.exp (β * (C j - C i₀)) := by
    intro β
    have hsum : ∑ j ∈ M, Real.exp (β * C j)
        = Real.exp (β * C i₀) * ∑ j ∈ M, Real.exp (β * (C j - C i₀)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Real.exp_add]
      ring_nf
    rw [hsum, div_mul_eq_div_div, div_self (ne_of_gt (Real.exp_pos _))]
  -- The denominator tends to 1: the i₀ term is identically 1, rivals → 0.
  -- Finite sum of limits (inline helper: the snapshot lacks a named lemma).
  have hsum_tendsto : ∀ (s : Finset ι) (a : ι → ℝ),
      (∀ j ∈ s, Tendsto (fun β : ℝ => Real.exp (β * (C j - C i₀)))
        atTop (nhds (a j))) →
      Tendsto (fun β : ℝ => ∑ j ∈ s, Real.exp (β * (C j - C i₀)))
        atTop (nhds (∑ j ∈ s, a j)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro a _; simp
    | insert i t hit ih =>
        intro a h
        simp only [Finset.sum_insert hit]
        exact (h i (Finset.mem_insert_self i t)).add
          (ih a fun j hj => h j (Finset.mem_insert_of_mem hj))
  have hterm : ∀ j ∈ M, Tendsto (fun β : ℝ => Real.exp (β * (C j - C i₀)))
      atTop (nhds (if j = i₀ then 1 else 0)) := by
    intro j hj
    by_cases hji : j = i₀
    · subst hji
      simp
    · rw [show (if j = i₀ then (1:ℝ) else 0) = 0 from by simp [hji]]
      have hneg : C j - C i₀ < 0 := sub_neg.mpr (hstrict j hj hji)
      have hbot : Tendsto (fun β : ℝ => β * (C j - C i₀)) atTop atBot :=
        Tendsto.atTop_mul_const_of_neg hneg tendsto_id
      exact Real.tendsto_exp_atBot.comp hbot
  have hden : Tendsto (fun β : ℝ => ∑ j ∈ M, Real.exp (β * (C j - C i₀)))
      atTop (nhds 1) := by
    have h := hsum_tendsto M _ hterm
    have hval : (∑ j ∈ M, if j = i₀ then (1:ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' M i₀ fun _ => (1:ℝ)]
      simp [hi₀]
    rwa [hval] at h
  have hlim : Tendsto (fun β : ℝ =>
      (∑ j ∈ M, Real.exp (β * (C j - C i₀)))⁻¹) atTop (nhds 1) := by
    have h := hden.inv₀ one_ne_zero
    simpa using h
  refine Tendsto.congr (fun β => ?_) hlim
  rw [hrw β, one_div]

/-- **The Mu guarantee (matched pair).** At every FINITE β, every mode in
the support keeps a strictly positive share: the lock is approached,
never occupied at finite selectivity. -/
theorem partial_lock {ι : Type*} (M : Finset ι) (C : ι → ℝ) (β : ℝ)
    (hM : M.Nonempty) (j : ι) (_hj : j ∈ M) :
    0 < Real.exp (β * C j) / ∑ k ∈ M, Real.exp (β * C k) := by
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos (fun k _ => Real.exp_pos _) hM

/-- **PMD equivalence — Chapter 5's first kernel entry.** Under the NAMED
strictly anti-monotone link between coherence and decoherence (StrictAnti
species), maximizing coherence IS minimizing decoherence: the selected
mode is the same mode under either reading. -/
theorem pmd_equivalence {ι : Type*} {D : ℝ → ℝ} (hanti : StrictAnti D)
    (M : Finset ι) (C : ι → ℝ) (i₀ : ι) :
    (∀ j ∈ M, C j ≤ C i₀) ↔ (∀ j ∈ M, D (C i₀) ≤ D (C j)) := by
  have key : ∀ a b : ℝ, a ≤ b ↔ D b ≤ D a := by
    intro a b
    constructor
    · intro h
      rcases eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact (hanti hlt).le
    · intro h
      by_contra hab
      rw [not_le] at hab
      exact absurd (hanti hab) (not_lt.mpr h)
  constructor <;> intro h j hj
  · exact (key (C j) (C i₀)).mp (h j hj)
  · exact (key (C j) (C i₀)).mpr (h j hj)

/-! ## MOVEMENT 2 — the variational objective's two faces (Ch5 §4 ↔ Ch7) -/

/-- **The objective equivalence.** For two evolutions with the same
generative income (fixed-G clause, NAMED — canon's own reduced-form
scope), each obeying the budget identity ΔC = G − D (the certified
Ledger-tower identity's algebraic shadow): losing less IS climbing more,
in both the weak and strict senses. The kernel-sized piece of
δ∫D dt = 0 — the objective, not the E–L machinery, which canon itself
labels "not meant for computation." -/
theorem pmd_objective_equivalence (G ΔC₁ ΔC₂ D₁ D₂ : ℝ)
    (h₁ : ΔC₁ = G - D₁) (h₂ : ΔC₂ = G - D₂) :
    (D₁ ≤ D₂ ↔ ΔC₂ ≤ ΔC₁) ∧ (D₁ < D₂ ↔ ΔC₂ < ΔC₁) := by
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-! ## MOVEMENT 3 — the Γ-dial annex (Ch6's printed equations) -/

/-- **The bridge equation's grain** — D_loss = τ_coh·Γ is nonnegative on
the physical domain and monotone in each dial: leakier updates lose more,
faster updates lose more. -/
theorem bridge_equation (τ Γ₁ Γ₂ τ₁ τ₂ Γ : ℝ)
    (hτ : 0 ≤ τ) (hΓ : 0 ≤ Γ) (_hτ₁ : 0 ≤ τ₁) (hΓ₁ : 0 ≤ Γ₁) :
    0 ≤ τ * Γ ∧
    (Γ₁ ≤ Γ₂ → τ * Γ₁ ≤ τ * Γ₂) ∧
    (τ₁ ≤ τ₂ → τ₁ * Γ₁ ≤ τ₂ * Γ₁) := by
  refine ⟨mul_nonneg hτ hΓ, fun h => ?_, fun h => ?_⟩
  · exact mul_le_mul_of_nonneg_left h hτ
  · exact mul_le_mul_of_nonneg_right h hΓ₁

/-- **The Mu dial** — with Γ strictly inside (0,1) (NAMED fence: canon
prints both ends as "Mu-forbidden in practice") and a positive update
rate: the loss is real (0 < τΓ) and never the whole update (τΓ < τ).
Some structure always lost, some always kept. -/
theorem gamma_mu_bounds (τ Γ : ℝ) (hτ : 0 < τ) (h0 : 0 < Γ) (h1 : Γ < 1) :
    0 < τ * Γ ∧ τ * Γ < τ := by
  constructor
  · exact mul_pos hτ h0
  · nlinarith

/-- **The entropy decomposition welded to the ledger.** Canon's
S = ∫τ_coh·Γ dt: if the entropy's pointwise rate is τ·Γ (the bridge
equation as HasDerivAt data), the FTC returns the printed integral —
the certified Ledger-tower S = ∫D_loss gains its Ch6 decomposition. -/
theorem entropy_decomposition (S τc Γc : ℝ → ℝ) (a b : ℝ)
    (hS : ∀ t, HasDerivAt S (τc t * Γc t) t)
    (hcont : Continuous fun t => τc t * Γc t) :
    ∫ t in a..b, τc t * Γc t = S b - S a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hS t)
    ((hcont.intervalIntegrable a b))

/-- **The floor mirror gains its equation.** Under the NAMED tempo-law
link τ_coh = C_floor/C (hypothesis, never identification): at fixed
loss-efficiency, D_loss = Γ·C_floor/C is strictly larger where coherence
is lower — loss runs fastest at the floor. The Ledger/Turn mirror note
(why the floor must turn), now as an inequality. -/
theorem floor_mirror (Γ Cfloor C₁ C₂ : ℝ)
    (hΓ : 0 < Γ) (hf : 0 < Cfloor) (h1 : 0 < C₁) (hlt : C₁ < C₂) :
    Γ * (Cfloor / C₂) < Γ * (Cfloor / C₁) := by
  apply mul_lt_mul_of_pos_left _ hΓ
  exact div_lt_div_of_pos_left hf h1 hlt

end PNPMD

#print axioms PNPMD.argmax_favored
#print axioms PNPMD.lock_limit
#print axioms PNPMD.partial_lock
#print axioms PNPMD.pmd_equivalence
#print axioms PNPMD.pmd_objective_equivalence
#print axioms PNPMD.bridge_equation
#print axioms PNPMD.gamma_mu_bounds
#print axioms PNPMD.entropy_decomposition
#print axioms PNPMD.floor_mirror
