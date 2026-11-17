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

/-! ## TIER 3b — STAGE 1: the time-coordinate bridge
    Space 1 is the time line; `Space.coord 0` reads the clock. These lemmas
    translate PhysLean's Space-calculus into ordinary real calculus. -/

namespace PN

open Space

/-- Chain rule through the time coordinate: the Space-1 partial of g∘(coord 0)
    is g′∘(coord 0). -/
lemma deriv0_comp_coord {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) :
    (∂[(0 : Fin 1)] fun x : Space 1 => g (Space.coord 0 x))
      = fun x => g' (Space.coord 0 x) := by
  funext x
  have hF : HasFDerivAt (fun y : Space 1 => g (Space.coord 0 y))
      ((g' (Space.coord 0 x)) • (Space.coordCLM 0 : Space 1 →L[ℝ] ℝ)) x := by
    have h1 : HasFDerivAt (fun y : Space 1 => Space.coord 0 y)
        (Space.coordCLM 0 : Space 1 →L[ℝ] ℝ) x := (Space.coordCLM 0).hasFDerivAt
    exact (hg (Space.coord 0 x)).comp_hasFDerivAt x h1
  show Space.deriv 0 _ x = _
  unfold Space.deriv
  rw [hF.fderiv]
  simp [Space.coordCLM_apply, Space.coord_apply]

/-- A real trajectory q packaged as a PhysLean field on the time line. -/
noncomputable def mkField (q : ℝ → ℝ) : Space 1 → EuclideanSpace ℝ (Fin 1) :=
  fun x => WithLp.toLp 2 (fun _ => q (Space.coord 0 x))

lemma mkField_apply (q : ℝ → ℝ) (x : Space 1) (b : Fin 1) :
    mkField q x b = q (Space.coord 0 x) := rfl

lemma idx0_fst : idx0.1 = (0 : MultiIndex 1) := by decide

lemma toList_idx1 : idx1.1.toList = [0] := by decide

lemma iteratedDeriv_idx1 (F : Space 1 → ℝ) :
    (∂^[idx1.1] F) = ∂[(0 : Fin 1)] F := by
  show idx1.1.toList.foldr (fun i g => Space.deriv i g) F = _
  rw [toList_idx1]
  rfl

/-- Jet coordinate 0 of a packaged trajectory: the position. -/
lemma jet_coord0 (q : ℝ → ℝ) (x : Space 1) :
    (jetAt 1 (mkField q) x).coord idx0 0 = q (Space.coord 0 x) := by
  show jetCoordinatesAt 1 (mkField q) x idx0 0 = _
  unfold jetCoordinatesAt
  rw [idx0_fst]
  simp [mkField_apply, Space.coord_apply]

/-- Jet coordinate 1 of a packaged trajectory: the velocity. -/
lemma jet_coord1 (q v : ℝ → ℝ) (hq : ∀ t, HasDerivAt q (v t) t) (x : Space 1) :
    (jetAt 1 (mkField q) x).coord idx1 0 = v (Space.coord 0 x) := by
  show jetCoordinatesAt 1 (mkField q) x idx1 0 = _
  unfold jetCoordinatesAt
  rw [show (fun y => (mkField q y) 0) = (fun y : Space 1 => q (Space.coord 0 y)) from rfl]
  rw [iteratedDeriv_idx1, deriv0_comp_coord hq]

end PN

/-! ## TIER 3b — STAGE 2: the Euler–Lagrange bridge
    PhysLean's EL operator, evaluated on the lapse Lagrangian along a packaged
    trajectory, reduces to the cleared EL equation of Tiers 1–2. -/

namespace PN

open Space

lemma idx0_order : idx0.1.order = 0 := by decide
lemma idx1_order : idx1.1.order = 1 := by decide

/-- The point of the time line at clock reading t. -/
def atTime (t : ℝ) : Space 1 := ⟨fun _ => t⟩

lemma coord_atTime (t : ℝ) : Space.coord 0 (atTime t) = t := by
  simp [Space.coord_apply, atTime]

variable (q v a N N' V V' : ℝ → ℝ)

lemma lapse_coordDeriv (hNpos : ∀ t, 0 < N t) (hV : ∀ x, HasDerivAt V (V' x) x)
    (I : DerivativeIndex 1 1) (b : Fin 1) (J : JetPoint 1 1 1) :
    (lapseLagrangian N V V' hNpos hV).coordDeriv I b J
      = if I = idx1 then J.coord idx1 0 / N (J.base.val 0)
        else -(N (J.base.val 0) * V' (J.coord idx0 0)) := rfl

lemma base_val_eq_coord (x : Space 1) : x.val 0 = Space.coord 0 x := by
  rw [Space.coord_apply]

/-- **The bridge: PhysLean's EL component of the lapse Lagrangian, in closed form.** -/
lemma elComponent_eq
    (hNpos : ∀ t, 0 < N t)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hN : ∀ t, HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x) (x : Space 1) :
    eulerLagrangeComponent (lapseLagrangian N V V' hNpos hV) 0 (mkField q) x
      = -(N (Space.coord 0 x) * V' (q (Space.coord 0 x)))
        - (a (Space.coord 0 x) * N (Space.coord 0 x)
            - v (Space.coord 0 x) * N' (Space.coord 0 x)) / (N (Space.coord 0 x)) ^ 2 := by
  rw [eulerLagrangeComponent_apply, sum_derivIndex11]
  have h0 : eulerLagrangeTerm (lapseLagrangian N V V' hNpos hV) idx0 0 (mkField q) x
      = -(N (Space.coord 0 x) * V' (q (Space.coord 0 x))) := by
    rw [eulerLagrangeTerm_apply, idx0_order]
    unfold iteratedTotalDerivative
    rw [idx0_fst]
    simp only [Space.iteratedDeriv_zero, evalOnJet_apply]
    rw [lapse_coordDeriv, if_neg idx0_ne_idx1, jetAt_base, base_val_eq_coord, jet_coord0]
    simp
  have h1 : eulerLagrangeTerm (lapseLagrangian N V V' hNpos hV) idx1 0 (mkField q) x
      = -((a (Space.coord 0 x) * N (Space.coord 0 x)
          - v (Space.coord 0 x) * N' (Space.coord 0 x)) / (N (Space.coord 0 x)) ^ 2) := by
    rw [eulerLagrangeTerm_apply, idx1_order]
    unfold iteratedTotalDerivative
    have hfun : evalOnJet 1 ((lapseLagrangian N V V' hNpos hV).coordDeriv idx1 0) (mkField q)
        = fun y : Space 1 => v (Space.coord 0 y) / N (Space.coord 0 y) := by
      funext y
      rw [evalOnJet_apply, lapse_coordDeriv, if_pos rfl, jetAt_base, base_val_eq_coord,
        jet_coord1 q v hq]
    rw [hfun, iteratedDeriv_idx1,
      deriv0_comp_coord (g := fun s => v s / N s)
        (g' := fun s => (a s * N s - v s * N' s) / N s ^ 2)
        (fun s => (hv s).div (hN s) (ne_of_gt (hNpos s)))]
    simp
  rw [h0, h1]
  ring

/-- **SatisfiesEulerLagrange ⟺ the cleared EL equation of Tiers 1–2.**
    This is the statement-fidelity theorem: PhysLean's variational EL condition
    for the lapse Lagrangian IS the equation N·a = v·Ṅ − N³·V′(q). -/
theorem satisfiesEL_iff_cleared
    (hNpos : ∀ t, 0 < N t)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hN : ∀ t, HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x) :
    SatisfiesEulerLagrange (lapseLagrangian N V V' hNpos hV) (mkField q)
      ↔ ∀ t, N t * a t = v t * N' t - (N t) ^ 3 * V' (q t) := by
  unfold SatisfiesEulerLagrange
  constructor
  · intro h t
    have hx : eulerLagrangeOp (lapseLagrangian N V V' hNpos hV) (mkField q) (atTime t) 0
        = 0 := by
      rw [h]; simp
    rw [eulerLagrangeOp_apply,
      elComponent_eq q v a N N' V V' hNpos hq hv hN hV (atTime t), coord_atTime] at hx
    have hNt : N t ≠ 0 := ne_of_gt (hNpos t)
    field_simp at hx
    linarith [hx]
  · intro h
    funext x
    have ht := h (Space.coord 0 x)
    have hNt : N (Space.coord 0 x) ≠ 0 := ne_of_gt (hNpos _)
    show WithLp.toLp 2
        (fun b => eulerLagrangeComponent (lapseLagrangian N V V' hNpos hV) b (mkField q) x) = _
    have hzero : (fun b : Fin 1 =>
        eulerLagrangeComponent (lapseLagrangian N V V' hNpos hV) b (mkField q) x)
        = fun _ => (0 : ℝ) := by
      funext b
      have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
      subst hb
      rw [elComponent_eq q v a N N' V V' hNpos hq hv hN hV x]
      have hdiv : (a (Space.coord 0 x) * N (Space.coord 0 x)
          - v (Space.coord 0 x) * N' (Space.coord 0 x)) / (N (Space.coord 0 x)) ^ 2
          = -(N (Space.coord 0 x) * V' (q (Space.coord 0 x))) := by
        rw [div_eq_iff (by positivity)]
        linear_combination ht
      rw [hdiv]
      ring
    rw [hzero]
    simp
    rfl

end PN

#print axioms PN.satisfiesEL_iff_cleared

/-! ## TIER 3b — STAGE 3: the capstone
    Tier 2's drift law, ported into this workspace, then chained through
    PhysLean's fundamental theorem of variational calculus:
    δS = 0  ⟹  Euler–Lagrange  ⟹  dE/dt = (Ṅ/N)·E.  No hypothesis but the action. -/

namespace PN

open scoped ContDiff

variable (q v a N N' V V' : ℝ → ℝ)

/-- Tier 2's drift law (ported): from the cleared EL equation, the energy
    E = v²/(2N) + N·V(q) drifts as E′ = (Ṅ/N)·E. -/
theorem drift_law_at (t : ℝ)
    (hNpos : ∀ s, 0 < N s)
    (hq : ∀ s, HasDerivAt q (v s) s)
    (hv : HasDerivAt v (a t) t)
    (hN : HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hEL : N t * a t = v t * N' t - (N t)^3 * V' (q t)) :
    HasDerivAt (fun s => (v s)^2 / (2 * N s) + N s * V (q s))
      ((N' t / N t) * ((v t)^2 / (2 * N t) + N t * V (q t))) t := by
  have hNt : N t ≠ 0 := ne_of_gt (hNpos t)
  have h2Nt : 2 * N t ≠ 0 := by positivity
  have hnum := hv.pow 2
  have hden : HasDerivAt (fun s => 2 * N s) (2 * N' t) t := hN.const_mul 2
  have hkin := hnum.div hden h2Nt
  have hVq : HasDerivAt (fun s => V (q s)) (V' (q t) * v t) t :=
    (hV (q t)).comp t (hq t)
  have hpot := hN.mul hVq
  have htot := hkin.add hpot
  convert htot using 1
  have hELa : a t = (v t * N' t - (N t)^3 * V' (q t)) / N t := by
    rw [eq_div_iff hNt]
    linear_combination hEL
  rw [hELa]
  push_cast
  field_simp
  simp only [Pi.pow_apply]
  ring

/-- **The action principle delivers the EL equation** — PhysLean's proven
    fundamental theorem of variational calculus, instantiated for the lapse
    Lagrangian: criticality of the action ⟺ the cleared EL equation. -/
theorem action_critical_iff_el
    (hNpos : ∀ t, 0 < N t)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hN : ∀ t, HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hf : ContDiff ℝ ∞ (mkField q))
    (hLs : (lapseLagrangian N V V' hNpos hV).SmoothInCoordinates)
    (hfin : HasFiniteAction (lapseLagrangian N V V' hNpos hV) (mkField q)) :
    IsCritical (lapseLagrangian N V V' hNpos hV) (mkField q)
      ↔ ∀ t, N t * a t = v t * N' t - (N t) ^ 3 * V' (q t) :=
  (isCritical_iff_satisfiesEulerLagrange_of_contDiff_and_smoothInCoordinates
      (lapseLagrangian N V V' hNpos hV) (mkField q) hf hLs hfin).trans
    (satisfiesEL_iff_cleared q v a N N' V V' hNpos hq hv hN hV)

/-- **THE CAPSTONE — Z-N.1 end to end: δS = 0 ⟹ the drift law.**
    If the trajectory q is a critical point of the lapse action, then its
    energy E = v²/(2N) + N·V(q) drifts at the logarithmic clock rate:
    dE/dt = (Ṅ/N)·E — the Generative Law's form, demanded by the variational
    principle, with no physics hypothesis remaining but the action itself. -/
theorem action_critical_drift_law
    (hNpos : ∀ t, 0 < N t)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hN : ∀ t, HasDerivAt N (N' t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hf : ContDiff ℝ ∞ (mkField q))
    (hLs : (lapseLagrangian N V V' hNpos hV).SmoothInCoordinates)
    (hfin : HasFiniteAction (lapseLagrangian N V V' hNpos hV) (mkField q))
    (hcrit : IsCritical (lapseLagrangian N V V' hNpos hV) (mkField q)) (t : ℝ) :
    HasDerivAt (fun s => (v s)^2 / (2 * N s) + N s * V (q s))
      ((N' t / N t) * ((v t)^2 / (2 * N t) + N t * V (q t))) t := by
  have hEL := (action_critical_iff_el q v a N N' V V' hNpos hq hv hN hV hf hLs hfin).mp hcrit t
  exact drift_law_at q v a N N' V V' t hNpos hq (hv t) (hN t) hV hEL

end PN

#print axioms PN.action_critical_drift_law

/-! ## TIER 3c — discharging the regularity debt, and the canon corollary -/

namespace PN

open scoped ContDiff
open Space

/-- Reading the clock off the base factor is smooth. -/
lemma contDiff_baseval :
    ContDiff ℝ ∞ (fun p : Space 1 × JetCoordinates 1 1 1 => p.1.val 0) := by
  have h : (fun p : Space 1 × JetCoordinates 1 1 1 => p.1.val 0)
      = fun p => Space.coordCLM 0 p.1 := by
    funext p
    rw [Space.coordCLM_apply, Space.coord_apply]
  rw [h]
  exact (Space.coordCLM 0).contDiff.comp contDiff_fst

/-- Reading a jet coordinate off the fiber factor is smooth. -/
lemma contDiff_fiberval (I : DerivativeIndex 1 1) (b : Fin 1) :
    ContDiff ℝ ∞ (fun p : Space 1 × JetCoordinates 1 1 1 => p.2 I b) := by
  fun_prop

variable (q v a N N' V V' : ℝ → ℝ)

/-- **The regularity debt, discharged**: for smooth N and V′ (and V differentiable),
    the lapse Lagrangian is smooth in PhysLean's jet coordinates. -/
theorem lapse_smoothInCoordinates
    (hNpos : ∀ t, 0 < N t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hNs : ContDiff ℝ ∞ N)
    (hV's : ContDiff ℝ ∞ V') :
    (lapseLagrangian N V V' hNpos hV).SmoothInCoordinates := by
  constructor
  · -- continuity of L itself in coordinates
    have hVc : Continuous V := by
      rw [continuous_iff_continuousAt]
      exact fun x => (hV x).continuousAt
    have hb := contDiff_baseval.continuous
    have hf1 := (contDiff_fiberval idx1 0).continuous
    have hf0 := (contDiff_fiberval idx0 0).continuous
    show Continuous fun p : Space 1 × JetCoordinates 1 1 1 =>
      (p.2 idx1 0) ^ 2 / (2 * N (p.1.val 0)) - N (p.1.val 0) * V (p.2 idx0 0)
    apply Continuous.sub
    · apply Continuous.div (hf1.pow 2) (continuous_const.mul ((hNs.continuous).comp hb))
      intro p
      exact ne_of_gt (mul_pos two_pos (hNpos _))
    · exact ((hNs.continuous).comp hb).mul (hVc.comp hf0)
  · -- smoothness of the coordinate derivatives in coordinates
    intro I b
    by_cases hI : I = idx1
    · subst hI
      have hfun : (fun p : Space 1 × JetCoordinates 1 1 1 =>
          (lapseLagrangian N V V' hNpos hV).coordDeriv idx1 b
            (JetPoint.ofBaseCoordinates p.1 p.2))
          = fun p => p.2 idx1 0 / N (p.1.val 0) := by
        funext p
        rw [lapse_coordDeriv, if_pos rfl]
        rfl
      rw [hfun]
      exact (contDiff_fiberval idx1 0).div (hNs.comp contDiff_baseval)
        (fun p => ne_of_gt (hNpos _))
    · have hfun : (fun p : Space 1 × JetCoordinates 1 1 1 =>
          (lapseLagrangian N V V' hNpos hV).coordDeriv I b
            (JetPoint.ofBaseCoordinates p.1 p.2))
          = fun p => -(N (p.1.val 0) * V' (p.2 idx0 0)) := by
        funext p
        rw [lapse_coordDeriv, if_neg hI]
        rfl
      rw [hfun]
      exact ((hNs.comp contDiff_baseval).mul (hV's.comp (contDiff_fiberval idx0 0))).neg

/-- **THE CANON COROLLARY — Z-N.1 in the book's own symbols.**
    Wire in the arena law N = C_floor/C and the Generative Law Ċ = G − D_loss:
    if the trajectory is a critical point of the lapse action, then
    dE/dt = ((D_loss − G)/C) · E — canon's N-1 drift law, demanded by δS = 0. -/
theorem action_critical_drift_law_canon
    (C Gg Dl : ℝ → ℝ) (C_floor : ℝ) (hCf : 0 < C_floor)
    (hCpos : ∀ t, 0 < C t)
    (hC : ∀ t, HasDerivAt C (Gg t - Dl t) t)
    (hNdef : N = fun t => C_floor / C t)
    (hN'def : N' = fun t => -(C_floor * (Gg t - Dl t)) / (C t) ^ 2)
    (hNpos : ∀ t, 0 < N t)
    (hq : ∀ t, HasDerivAt q (v t) t)
    (hv : ∀ t, HasDerivAt v (a t) t)
    (hV : ∀ x, HasDerivAt V (V' x) x)
    (hf : ContDiff ℝ ∞ (mkField q))
    (hLs : (lapseLagrangian N V V' hNpos hV).SmoothInCoordinates)
    (hfin : HasFiniteAction (lapseLagrangian N V V' hNpos hV) (mkField q))
    (hcrit : IsCritical (lapseLagrangian N V V' hNpos hV) (mkField q)) (t : ℝ) :
    HasDerivAt (fun s => (v s)^2 / (2 * N s) + N s * V (q s))
      (((Dl t - Gg t) / C t) * ((v t)^2 / (2 * N t) + N t * V (q t))) t := by
  have hN : ∀ s, HasDerivAt N (N' s) s := by
    intro s
    rw [hNdef, hN'def]
    have h := (hasDerivAt_const s C_floor).div (hC s) (ne_of_gt (hCpos s))
    simpa [Pi.div_def] using h
  have h := action_critical_drift_law q v a N N' V V' hNpos hq hv hN hV hf hLs hfin hcrit t
  convert h using 2
  rw [hNdef, hN'def]
  have hCt : C t ≠ 0 := ne_of_gt (hCpos t)
  have hCft : C_floor ≠ 0 := ne_of_gt hCf
  field_simp
  ring

end PN

#print axioms PN.lapse_smoothInCoordinates
#print axioms PN.action_critical_drift_law_canon
