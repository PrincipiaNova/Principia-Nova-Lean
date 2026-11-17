/-
═══════════════════════════════════════════════════════════════════════════════
PN §22 SKELETON — THE SELF-IDENTITY REQUIREMENT (THEOREM 6), KERNEL-CERTIFIED
11/07/2026 · Lean 4 + mathlib

TIER 1 — the bounds algebra: μ-bounded coverage ratio, escape bound (uniform =
and concentrated-strict), Corollary 6.1 (geometric first-drift time), frozen-σ
rigidity (Case 2), the tempo differential, and the capstone trichotomy.

TIER 2 — the model and the two donors: CΩ_strict (canon's printed STRICT CASE
of the operational category — "transitions in which no relation is dissolved" —
as a preorder category, instance from mathlib), the Yoneda floor consumed from
mathlib's fully proved Yoneda lemma, and the Rice ceiling consumed from
mathlib's Rice theorem.

MODEL SCOPE (rides in the name): CΩ_strict is the strict case ONLY. The wider
transition class preserving R_core alone, the vorticity/Hamiltonian template,
the winding-number monitor engineering, and the Kolmogorov-complexity leg of
Premise 2 (no mathlib donor exists) all stay canon prose. On a preorder, the
Yoneda determination is deliberately minimal — "mutually related is equal" —
which is the honest size of Axiom 3's categorical face at exactly this model.

NAMED FENCES: hfloor/hceiling (σ present / catalogue never complete — Premises
3+4 / Premise 2 + Generative Law), hdrift (p_drift > 0, canon's premise),
hp1 (p < 1), linear growth rates a < b with hstart (catalogue begins above its
asymptotic fate) in tempo_differential, and hpreserves/hdeforms (canon's own
nontriviality witnesses; the identification of "preserves Y(Ω)" with a Rice
class is canon's printed, hedged claim — the fence the kernel keeps).

Statement-level coverage only. §22 is NOT certified "as a whole."
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

set_option maxHeartbeats 1600000

open CategoryTheory Filter

namespace PN22

/-! ## TIER 1 — the bounds algebra -/

/-- **μ-bounded coverage.** σ present (hfloor: the Yoneda floor — the catalogue
cannot be empty) and never complete (hceiling: undecidability + Generative Law)
force the coverage ratio strictly inside (0,1): never perfectly blind, never
perfectly seeing — the standard Mu form. -/
theorem mu_bounded_coverage (m n : ℕ) (hfloor : 0 < m) (hceiling : m < n) :
    0 < (m : ℝ) / n ∧ (m : ℝ) / n < 1 := by
  have hn : 0 < n := hfloor.trans hceiling
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hfloor
  refine ⟨div_pos hmR hnR, ?_⟩
  rw [div_lt_one hnR]
  exact_mod_cast hceiling

/-- **Escape bound, uniform landing.** Drift landing uniformly on the defects
present escapes detection with probability exactly 1 − ρ(t): canon's
P(undetected | drift) ≥ 1 − ρ with equality in the uniform case. Finite model:
D = defects present, S = defects monitored. -/
theorem escape_bound_uniform {α : Type*} [DecidableEq α] (D S : Finset α)
    (hS : S ⊆ D) (hD : D.Nonempty) :
    ((D \ S).card : ℝ) / D.card = 1 - (S.card : ℝ) / D.card := by
  have hle : S.card ≤ D.card := Finset.card_le_card hS
  have hD0 : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hD
  have hint : S ∩ D = S := Finset.inter_eq_left.mpr hS
  rw [Finset.card_sdiff, hint, Nat.cast_sub hle]
  field_simp

/-- **Case 1, blind.** σ absent (empty catalogue, ρ = 0): every drift escapes —
the bound saturates at 1. -/
theorem no_sigma_blind {α : Type*} [DecidableEq α] (D : Finset α)
    (hD : D.Nonempty) :
    ((D \ (∅ : Finset α)).card : ℝ) / D.card = 1 := by
  have hD0 : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hD
  rw [Finset.sdiff_empty]
  field_simp

/-- **Concentrated landing beats the uniform bound strictly.** When σ is present
(ρ > 0) and drift concentrates in the newest, unmonitored structure — canon's
expected case under the Generative Law — its escape probability 1 strictly
exceeds 1 − ρ: canon's strict inequality. -/
theorem escape_concentrated_strict {α : Type*} [DecidableEq α] (D S : Finset α)
    (_hS : S ⊆ D) (hSne : S.Nonempty) (hD : D.Nonempty) :
    1 - (S.card : ℝ) / D.card < 1 := by
  have hD0 : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hD
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hρ : 0 < (S.card : ℝ) / D.card := div_pos hS0 hD0
  linarith

/-- **Corollary 6.1 — drift certainty without σ.** First-drift time geometric
with per-step probability p_drift: E[T_drift] = 1/p_drift exactly (canon's
bound E[T] ≤ 1/p met with equality in the geometric model). Fences: hdrift is
canon's own premise p_drift > 0; hp1 < 1 named. -/
theorem corollary_6_1 (p : ℝ) (hdrift : 0 < p) (hp1 : p < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * ((1 - p) ^ n * p) = 1 / p := by
  have hx0 : (0 : ℝ) ≤ 1 - p := by linarith
  have hx1 : (1 : ℝ) - p < 1 := by linarith
  have hnorm : ‖(1 : ℝ) - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * (1 - p) ^ n)
      ((1 - p) / (1 - (1 - p)) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have h2 : HasSum (fun n : ℕ => (1 - p) ^ n) ((1 - (1 - p))⁻¹) :=
    hasSum_geometric_of_lt_one hx0 hx1
  have h3 := (h1.add h2).mul_right p
  have h4 : (fun n : ℕ => ((n : ℝ) * (1 - p) ^ n + (1 - p) ^ n) * p)
      = fun n : ℕ => ((n : ℝ) + 1) * ((1 - p) ^ n * p) := by
    funext n; ring
  rw [h4] at h3
  rw [h3.tsum_eq]
  have hpne : p ≠ 0 := ne_of_gt hdrift
  have hsimp : (1 : ℝ) - (1 - p) = p := by ring
  rw [hsimp]
  field_simp
  ring

/-- **Case 2 — the frozen σ rejects all growth.** A catalogue frozen at time t
(Ŷ ⊆ Yₜ) flags every genuinely novel structure (anything in Yₜ₊₁ \ Yₜ) as
outside itself: identity rigidity — the system cannot learn. -/
theorem frozen_sigma_rejects_growth {α : Type*} (Ycat Yt Yt1 : Set α)
    (hfrozen : Ycat ⊆ Yt) {o : α} (hnovel : o ∈ Yt1 \ Yt) : o ∉ Ycat :=
  fun h => hnovel.2 (hfrozen h)

/-- **The tempo differential** — canon's "strongest claim in this section."
Catalogue growing at human tempo a, profile at machine tempo b, LINEAR RATES
NAMED (faster-than-linear machine growth only strengthens the conclusion —
results doc). With the catalogue starting above its asymptotic fate (hstart),
the coverage ratio is strictly falling on t ≥ 0, tends to a/b, and a/b < 1:
the ratio must fall. Only a machine-tempo monitor holds it. -/
theorem tempo_differential (a b a0 b0 : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a < b)
    (ha0 : 0 < a0) (hb0 : 0 < b0)
    (hstart : a * b0 < b * a0) :
    (∀ s t : ℝ, 0 ≤ s → s < t →
        (a0 + a * t) / (b0 + b * t) < (a0 + a * s) / (b0 + b * s)) ∧
    Tendsto (fun t : ℝ => (a0 + a * t) / (b0 + b * t)) atTop (nhds (a / b)) ∧
    a / b < 1 := by
  refine ⟨?_, ?_, (div_lt_one hb).mpr hab⟩
  · intro s t hs hst
    have hds : 0 < b0 + b * s := by nlinarith
    have hdt : 0 < b0 + b * t := by nlinarith
    rw [div_lt_div_iff₀ hdt hds]
    nlinarith
  · have hev : (fun t : ℝ => (a0 + a * t) / (b0 + b * t))
        =ᶠ[atTop] fun t : ℝ => (a0 * t⁻¹ + a) / (b0 * t⁻¹ + b) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have htne : t ≠ 0 := ne_of_gt ht
      have hd1 : b0 + b * t ≠ 0 := by positivity
      have hd2 : b0 * t⁻¹ + b ≠ 0 := by positivity
      field_simp
    have hnum : Tendsto (fun t : ℝ => a0 * t⁻¹ + a) atTop (nhds a) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul a0 |>.add
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => a) atTop (nhds a))
      simpa using h
    have hden : Tendsto (fun t : ℝ => b0 * t⁻¹ + b) atTop (nhds b) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul b0 |>.add
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => b) atTop (nhds b))
      simpa using h
    exact Tendsto.congr' hev.symm (hnum.div hden (ne_of_gt hb))

/-- **CAPSTONE — the Theorem 6 skeleton.** Under the named floor (Premises 3+4:
σ cannot be absent) and the named ceiling (Premise 2 + Generative Law: the
catalogue is never the whole profile), with canon's drift premise p > 0: the
coverage ratio is Mu-bounded in (0,1), the uniform escape probability is
exactly 1 − ρ, and the unguarded first-drift time has expectation 1/p.
σ absent, frozen, and adaptive are separated by no_sigma_blind,
frozen_sigma_rejects_growth, and this bound respectively. Conditional
throughout — the PN axioms ride as the premise structure, per canon's
architectural note. -/
theorem theorem_six_skeleton {α : Type*} [DecidableEq α]
    (D S : Finset α) (hS : S ⊆ D)
    (hfloor : S.Nonempty)
    (hceiling : S ≠ D)
    (p : ℝ) (hdrift : 0 < p) (hp1 : p < 1) :
    0 < (S.card : ℝ) / D.card ∧
    (S.card : ℝ) / D.card < 1 ∧
    ((D \ S).card : ℝ) / D.card = 1 - (S.card : ℝ) / D.card ∧
    ∑' n : ℕ, ((n : ℝ) + 1) * ((1 - p) ^ n * p) = 1 / p := by
  have hD : D.Nonempty :=
    Finset.card_pos.mp
      ((Finset.card_pos.mpr hfloor).trans_le (Finset.card_le_card hS))
  have hss : S ⊂ D := lt_of_le_of_ne hS hceiling
  have hlt : S.card < D.card := Finset.card_lt_card hss
  obtain ⟨h1, h2⟩ :=
    mu_bounded_coverage S.card D.card (Finset.card_pos.mpr hfloor) hlt
  exact ⟨h1, h2, escape_bound_uniform D S hS hD, corollary_6_1 p hdrift hp1⟩

/-! ## TIER 2 — the strict-case operational category and the two donors -/

universe u

/-- **CΩ_strict** — canon's operational category in its printed STRICT CASE:
objects are relational contents R(A); a morphism A ⟶ B exists iff
R(A) ⊆ R(B) — "every relational connection present in A is preserved in B",
no relation dissolved. The Category instance is mathlib's
`Preorder.smallCategory` on `Set R` under ⊆. The wider class preserving
R_core only stays canon prose; the name carries the scope. -/
abbrev CΩ_strict (R : Type u) : Type u := Set R

set_option warn.classDefReducibility false in
/-- The category check of canon's Verification paragraph, kernel-discharged:
CΩ_strict is a category (identities, composition, associativity, units). -/
def category_check (R : Type u) : Category (CΩ_strict R) := inferInstance

/-- canon: "id_A exists trivially for every configuration: doing nothing
preserves all existing relations" — the identity morphism, which on this model
IS subset-reflexivity. -/
def identity_exists {R : Type u} (A : CΩ_strict R) : A ⟶ A := 𝟙 A

/-- The defining clause as an iff: a transition A ⟶ B exists precisely when
A's relational structure is preserved into B. -/
theorem morphism_iff_preserves {R : Type u} (A B : CΩ_strict R) :
    Nonempty (A ⟶ B) ↔ A ⊆ B :=
  ⟨fun ⟨f⟩ => leOfHom f, fun h => ⟨homOfLE h⟩⟩

/-- **The Yoneda floor** (Premise 3, consumed from mathlib's fully proved
Yoneda lemma): a configuration of CΩ_strict is determined by its relational
profile — an isomorphism of Yoneda profiles yields an isomorphism of
configurations. σ cannot be absent, because without the self-relation there
is no identity to maintain. -/
def floor_yoneda {R : Type u} {A B : CΩ_strict R}
    (h : yoneda.obj A ≅ yoneda.obj B) : A ≅ B :=
  Yoneda.fullyFaithful.preimageIso h

/-- On the strict case the determination is rigid: mutually related is equal
(antisymmetry). This is the honest size of Yoneda's content at exactly this
model — Axiom 3's categorical face, no larger. -/
theorem strict_case_rigid {R : Type u} {A B : CΩ_strict R} (h : A ≅ B) :
    A = B :=
  le_antisymm (leOfHom h.hom) (leOfHom h.inv)

/-- Profile determines configuration, end to end: isomorphic Yoneda profiles
force equal relational contents on the strict model. -/
theorem profile_determines {R : Type u} {A B : CΩ_strict R}
    (h : yoneda.obj A ≅ yoneda.obj B) : A = B :=
  strict_case_rigid (floor_yoneda h)

/-- Proposition 5.2(b)'s mechanism, consumed: the entire relational profile
unfolds from evaluation at the identity morphism — the Yoneda lemma's
equivalence itself. -/
def profile_evaluation {R : Type u} (A : CΩ_strict R)
    (F : (CΩ_strict R)ᵒᵖ ⥤ Type u) :
    (yoneda.obj A ⟶ F) ≃ F.obj (Opposite.op A) :=
  yonedaEquiv

/-- **The Rice ceiling** (Premise 2's on-ramp, consumed from mathlib's Rice
theorem): no nontrivial semantic class of computed functions is decidable —
given canon's two nontriviality witnesses (some outputs preserve the profile,
some deform it), no effective procedure decides membership from code.
NAMED FENCE, canon's own printed hedge: the identification of "preserves
Y(Ω)" with such a class C is carried by hpreserves/hdeforms and by canon's
prose ("whose qualification as a clean Rice index set is contestable"); the
Kolmogorov leg — the one canon says the conclusion rests on — has no mathlib
donor and remains prose. The ceiling's certified face is the on-ramp. -/
theorem ceiling_rice (C : Set (ℕ →. ℕ)) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g)
    (hpreserves : f ∈ C) (hdeforms : g ∉ C) :
    ¬ComputablePred fun c => Nat.Partrec.Code.eval c ∈ C :=
  fun h => hdeforms (ComputablePred.rice C h hf hg hpreserves)

end PN22

#print axioms PN22.mu_bounded_coverage
#print axioms PN22.escape_bound_uniform
#print axioms PN22.no_sigma_blind
#print axioms PN22.escape_concentrated_strict
#print axioms PN22.corollary_6_1
#print axioms PN22.frozen_sigma_rejects_growth
#print axioms PN22.tempo_differential
#print axioms PN22.theorem_six_skeleton
#print axioms PN22.category_check
#print axioms PN22.identity_exists
#print axioms PN22.morphism_iff_preserves
#print axioms PN22.floor_yoneda
#print axioms PN22.strict_case_rigid
#print axioms PN22.profile_determines
#print axioms PN22.profile_evaluation
#print axioms PN22.ceiling_rice
