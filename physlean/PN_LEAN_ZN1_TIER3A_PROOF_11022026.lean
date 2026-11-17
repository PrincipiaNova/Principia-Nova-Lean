/-
  PRINCIPIA NOVA — Z-N.1 TIER 3a: THE LAPSE LAGRANGIAN IN PHYSLEAN
  11/02/2026 · Lean v4.35.0 + mathlib + PhysLean (PhyslibAlpha.ClassicalFieldTheory.Local)

  GOAL OF TIER 3: derive the Euler–Lagrange equation of
      L(t, q, q̇) = q̇²/(2N(t)) − N(t)·V(q)
  from the action principle δS = 0, using PhysLean's proven
  fundamental theorem of variational calculus
  (isCritical ⟺ SatisfiesEulerLagrange), then chain into Tier 2's
  drift law. Stage 3a (this file): the PN lapse Lagrangian as a
  well-formed PhysLean `Lagrangian 1 1 1` — one base coordinate
  (time), one field (q), first-order jets — with its fiber-derivative
  obligation PROVED, not assumed.
-/
import PhyslibAlpha.ClassicalFieldTheory.Local.EulerLagrangeEquation

open Physlib ClassicalFieldTheory Local

namespace PN

/-! ## The two derivative indices of mechanics: u (position) and u̇ (velocity) -/

/-- The order-0 derivative index on one coordinate: the field value q. -/
def idx0 : DerivativeIndex 1 1 := ⟨⟨fun _ => 0⟩, by decide⟩

/-- The order-1 derivative index on one coordinate: the velocity q̇. -/
def idx1 : DerivativeIndex 1 1 := ⟨⟨fun _ => 1⟩, by decide⟩

lemma idx0_ne_idx1 : idx0 ≠ idx1 := by decide

/-- Summation over the two derivative indices of (d, k) = (1, 1). -/
lemma sum_derivIndex11 (g : DerivativeIndex 1 1 → ℝ) :
    ∑ I : DerivativeIndex 1 1, g I = g idx0 + g idx1 := by
  have huniv : (Finset.univ : Finset (DerivativeIndex 1 1)) = {idx0, idx1} := by
    ext I
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨⟨f⟩, hord⟩ := I
    have hf : f 0 ≤ 1 := by
      simpa [MultiIndex.order, Fin.sum_univ_one] using hord
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hf with h | h
    · left
      apply Subtype.ext
      show MultiIndex.mk f = MultiIndex.mk (fun _ => 0)
      rw [MultiIndex.mk.injEq]
      funext i
      fin_cases i
      exact h
    · right
      apply Subtype.ext
      show MultiIndex.mk f = MultiIndex.mk (fun _ => 1)
      rw [MultiIndex.mk.injEq]
      funext i
      fin_cases i
      exact h
  rw [huniv, Finset.sum_insert (by simpa using idx0_ne_idx1), Finset.sum_singleton]

/-! ## The PN lapse Lagrangian -/

variable (N N' V V' : ℝ → ℝ)

/-- **The Z-N.1 lapse Lagrangian as a PhysLean local Lagrangian** (d = 1, m = 1, k = 1):
    L(t, q, q̇) = q̇²/(2·N(t)) − N(t)·V(q), with N = τ_coh the clock rate.
    The `hasDerivAlongFiber` field is the structure's proof obligation —
    that the declared ∂L/∂q and ∂L/∂q̇ really are the fiber derivatives —
    discharged here with mathlib calculus. -/
noncomputable def lapseLagrangian
    (hNpos : ∀ t, 0 < N t)
    (hV : ∀ x, HasDerivAt V (V' x) x) : Lagrangian 1 1 1 where
  toFun J := (J.coord idx1 0) ^ 2 / (2 * N (J.base.val 0))
    - N (J.base.val 0) * V (J.coord idx0 0)
  coordDeriv I _ J :=
    if I = idx1 then J.coord idx1 0 / N (J.base.val 0)
    else -(N (J.base.val 0) * V' (J.coord idx0 0))
  hasDerivAlongFiber := by
    intro J W
    have hNb : N (J.base.val 0) ≠ 0 := ne_of_gt (hNpos _)
    -- the declared pairing, reduced to its two real terms
    have hsum : (∑ I : DerivativeIndex 1 1, ∑ a : Fin 1,
        (if I = idx1 then J.coord idx1 0 / N (J.base.val 0)
         else -(N (J.base.val 0) * V' (J.coord idx0 0))) * W.coord I a)
        = J.coord idx1 0 / N (J.base.val 0) * W.coord idx1 0
          + -(N (J.base.val 0) * V' (J.coord idx0 0)) * W.coord idx0 0 := by
      rw [sum_derivIndex11]
      simp [idx0_ne_idx1]
      ring
    rw [hsum]
    -- the varied curve, with base fixed and fiber shifted linearly
    simp only [JetPoint.lineMap_base, JetPoint.lineMap_coord]
    -- kinetic piece: s ↦ (u₁ + s·w₁)²/(2N(b))
    have hlin1 : HasDerivAt (fun s : ℝ => J.coord idx1 0 + s * W.coord idx1 0)
        (W.coord idx1 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (W.coord idx1 0)).const_add
        (J.coord idx1 0)
    have hkin := (hlin1.pow 2).div_const (2 * N (J.base.val 0))
    -- potential piece: s ↦ N(b)·V(u₀ + s·w₀)
    have hlin0 : HasDerivAt (fun s : ℝ => J.coord idx0 0 + s * W.coord idx0 0)
        (W.coord idx0 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (W.coord idx0 0)).const_add
        (J.coord idx0 0)
    have hVc := ((hV (J.coord idx0 0 + 0 * W.coord idx0 0)).comp 0 hlin0).const_mul
      (N (J.base.val 0))
    have htot := hkin.sub hVc
    -- normalize the combinator wrappers into the explicit curve and derivative
    have htot' : HasDerivAt
        (fun s : ℝ => (J.coord idx1 0 + s * W.coord idx1 0) ^ 2 / (2 * N (J.base.val 0))
          - N (J.base.val 0) * V (J.coord idx0 0 + s * W.coord idx0 0))
        (2 * J.coord idx1 0 * W.coord idx1 0 / (2 * N (J.base.val 0))
          - N (J.base.val 0) * (V' (J.coord idx0 0) * W.coord idx0 0)) 0 := by
      simpa [Pi.sub_def] using htot
    convert htot' using 1
    field_simp
    ring

end PN

#print axioms PN.lapseLagrangian
#print axioms PN.sum_derivIndex11
