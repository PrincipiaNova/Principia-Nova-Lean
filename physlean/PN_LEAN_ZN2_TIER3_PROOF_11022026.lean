/-
  PRINCIPIA NOVA — Z-N.2 TIER 3, CAMP A: THE FIELD LAGRANGIAN IN PHYSLEAN
  11/02/2026 · Lean v4.35.0 + mathlib + PhysLean.

  GOAL OF N-2 TIER 3: derive the field Euler–Lagrange equation of
      L = u_t²/(2N) − N·u_x²/2 − N·V(u),   N = N(t, x) the lapse field,
  from the action principle δS = 0 on the (t, x) plane (d = 2, m = 1,
  k = 1), then chain into Tier 2's sourced continuity and irremovability.

  CAMP A (this stage): the three derivative indices of 1+1 field theory
  (value u, time-velocity u_t, space-gradient u_x), the 2D sum lemma,
  and the lapse field Lagrangian admitted with its fiber-derivative
  obligation PROVED.
-/
import PhyslibAlpha.ClassicalFieldTheory.Local.EulerLagrangeEquation

open Physlib ClassicalFieldTheory Local

namespace PN2

/-! ## The three derivative indices of (d, k) = (2, 1) -/

/-- Order-0: the field value u. -/
def j00 : DerivativeIndex 2 1 := ⟨⟨fun _ => 0⟩, by decide⟩

/-- Order-1 in coordinate 0 (time): u_t. -/
def j10 : DerivativeIndex 2 1 := ⟨⟨fun i => if i = 0 then 1 else 0⟩, by decide⟩

/-- Order-1 in coordinate 1 (space): u_x. -/
def j01 : DerivativeIndex 2 1 := ⟨⟨fun i => if i = 0 then 0 else 1⟩, by decide⟩

lemma j00_ne_j10 : j00 ≠ j10 := by decide
lemma j00_ne_j01 : j00 ≠ j01 := by decide
lemma j10_ne_j01 : j10 ≠ j01 := by decide
lemma j10_ne_j00 : j10 ≠ j00 := by decide
lemma j01_ne_j00 : j01 ≠ j00 := by decide
lemma j01_ne_j10 : j01 ≠ j10 := by decide

/-- Summation over the three derivative indices of (d, k) = (2, 1). -/
lemma sum_derivIndex21 (g : DerivativeIndex 2 1 → ℝ) :
    ∑ I : DerivativeIndex 2 1, g I = g j00 + g j10 + g j01 := by
  have huniv : (Finset.univ : Finset (DerivativeIndex 2 1)) = {j00, j10, j01} := by
    ext I
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨⟨f⟩, hord⟩ := I
    have hf : f 0 + f 1 ≤ 1 := by
      simpa [MultiIndex.order, Fin.sum_univ_two] using hord
    have h0 : f 0 = 0 ∨ (f 0 = 1 ∧ f 1 = 0) := by omega
    rcases h0 with h0 | ⟨h0, h1⟩
    · have h1 : f 1 = 0 ∨ f 1 = 1 := by omega
      rcases h1 with h1 | h1
      · left
        apply Subtype.ext
        show MultiIndex.mk f = MultiIndex.mk (fun _ => 0)
        rw [MultiIndex.mk.injEq]
        funext i
        fin_cases i <;> simpa [h0, h1]
      · right; right
        apply Subtype.ext
        show MultiIndex.mk f = MultiIndex.mk (fun i => if i = 0 then 0 else 1)
        rw [MultiIndex.mk.injEq]
        funext i
        fin_cases i <;> simp [h0, h1]
    · right; left
      apply Subtype.ext
      show MultiIndex.mk f = MultiIndex.mk (fun i => if i = 0 then 1 else 0)
      rw [MultiIndex.mk.injEq]
      funext i
      fin_cases i <;> simp [h0, h1]
  rw [huniv]
  rw [Finset.sum_insert (by simp [j00_ne_j10, j00_ne_j01]),
      Finset.sum_insert (by simpa using j10_ne_j01),
      Finset.sum_singleton]
  ring

/-! ## The lapse field Lagrangian -/

variable (N : ℝ → ℝ → ℝ) (V V' : ℝ → ℝ)

/-- **The Z-N.2 lapse field Lagrangian as a PhysLean local Lagrangian**
    (d = 2, m = 1, k = 1): L = u_t²/(2N) − N·u_x²/2 − N·V(u), with the
    lapse N(t, x) depending on BOTH base coordinates — the position- and
    time-dependent clock field of the N-2 stage. The `hasDerivAlongFiber`
    obligation is PROVED. -/
noncomputable def lapseFieldLagrangian
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z) : Lagrangian 2 1 1 where
  toFun J := (J.coord j10 0) ^ 2 / (2 * N (J.base.val 0) (J.base.val 1))
    - N (J.base.val 0) (J.base.val 1) * (J.coord j01 0) ^ 2 / 2
    - N (J.base.val 0) (J.base.val 1) * V (J.coord j00 0)
  coordDeriv I _ J :=
    if I = j10 then J.coord j10 0 / N (J.base.val 0) (J.base.val 1)
    else if I = j01 then -(N (J.base.val 0) (J.base.val 1) * J.coord j01 0)
    else -(N (J.base.val 0) (J.base.val 1) * V' (J.coord j00 0))
  hasDerivAlongFiber := by
    intro J W
    have hNb : N (J.base.val 0) (J.base.val 1) ≠ 0 := ne_of_gt (hNpos _ _)
    have hsum : (∑ I : DerivativeIndex 2 1, ∑ a : Fin 1,
        (if I = j10 then J.coord j10 0 / N (J.base.val 0) (J.base.val 1)
         else if I = j01 then -(N (J.base.val 0) (J.base.val 1) * J.coord j01 0)
         else -(N (J.base.val 0) (J.base.val 1) * V' (J.coord j00 0))) * W.coord I a)
        = J.coord j10 0 / N (J.base.val 0) (J.base.val 1) * W.coord j10 0
          + -(N (J.base.val 0) (J.base.val 1) * J.coord j01 0) * W.coord j01 0
          + -(N (J.base.val 0) (J.base.val 1) * V' (J.coord j00 0)) * W.coord j00 0 := by
      rw [sum_derivIndex21]
      simp [j00_ne_j10, j00_ne_j01, j10_ne_j01, j10_ne_j00, j01_ne_j00, j01_ne_j10]
      ring
    rw [hsum]
    simp only [JetPoint.lineMap_base, JetPoint.lineMap_coord]
    have hlin10 : HasDerivAt (fun s : ℝ => J.coord j10 0 + s * W.coord j10 0)
        (W.coord j10 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (W.coord j10 0)).const_add
        (J.coord j10 0)
    have hlin01 : HasDerivAt (fun s : ℝ => J.coord j01 0 + s * W.coord j01 0)
        (W.coord j01 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (W.coord j01 0)).const_add
        (J.coord j01 0)
    have hlin00 : HasDerivAt (fun s : ℝ => J.coord j00 0 + s * W.coord j00 0)
        (W.coord j00 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (W.coord j00 0)).const_add
        (J.coord j00 0)
    have hkin := (hlin10.pow 2).div_const (2 * N (J.base.val 0) (J.base.val 1))
    have hBx := (((hlin01.pow 2).const_mul
        (N (J.base.val 0) (J.base.val 1))).div_const 2)
    have hVc := ((hV (J.coord j00 0 + 0 * W.coord j00 0)).comp 0 hlin00).const_mul
      (N (J.base.val 0) (J.base.val 1))
    have htot := (hkin.sub hBx).sub hVc
    have htot' : HasDerivAt
        (fun s : ℝ => (J.coord j10 0 + s * W.coord j10 0) ^ 2
            / (2 * N (J.base.val 0) (J.base.val 1))
          - N (J.base.val 0) (J.base.val 1)
            * (J.coord j01 0 + s * W.coord j01 0) ^ 2 / 2
          - N (J.base.val 0) (J.base.val 1)
            * V (J.coord j00 0 + s * W.coord j00 0))
        (2 * J.coord j10 0 * W.coord j10 0 / (2 * N (J.base.val 0) (J.base.val 1))
          - N (J.base.val 0) (J.base.val 1) * (2 * J.coord j01 0 * W.coord j01 0) / 2
          - N (J.base.val 0) (J.base.val 1)
            * (V' (J.coord j00 0) * W.coord j00 0)) 0 := by
      simpa [Pi.sub_def, mul_comm, mul_assoc, mul_left_comm] using htot
    convert htot' using 1
    field_simp
    ring

end PN2

#print axioms PN2.sum_derivIndex21
#print axioms PN2.lapseFieldLagrangian

/-! ## CAMP B — STAGE 1: plane plumbing
    Total derivatives on the (t,x) plane carried as componentwise data:
    a gradient CLM built from two named partials, extraction lemmas for
    the two coordinate directions, and the jet coordinates of a packaged
    two-variable field. -/

namespace PN2

open Space

/-- A two-variable function placed on the plane. -/
def onPlane (g : ℝ → ℝ → ℝ) : Space 2 → ℝ := fun p => g (p.val 0) (p.val 1)

/-- A trajectory field q(t,x) packaged for PhysLean. -/
noncomputable def mkField2 (q : ℝ → ℝ → ℝ) : Space 2 → EuclideanSpace ℝ (Fin 1) :=
  fun p => WithLp.toLp 2 (fun _ => q (p.val 0) (p.val 1))

lemma mkField2_apply (q : ℝ → ℝ → ℝ) (p : Space 2) (b : Fin 1) :
    mkField2 q p b = q (p.val 0) (p.val 1) := rfl

/-- The gradient of a plane function, as a CLM with two named components. -/
noncomputable def gradCLM (a b : ℝ) : Space 2 →L[ℝ] ℝ :=
  a • (Space.coordCLM 0 : Space 2 →L[ℝ] ℝ) + b • (Space.coordCLM 1 : Space 2 →L[ℝ] ℝ)

lemma gradCLM_basis0 (a b : ℝ) : gradCLM a b (Space.basis 0) = a := by
  simp [gradCLM, Space.coordCLM_apply, Space.coord_apply, Space.basis_apply]

lemma gradCLM_basis1 (a b : ℝ) : gradCLM a b (Space.basis 1) = b := by
  simp [gradCLM, Space.coordCLM_apply, Space.coord_apply, Space.basis_apply]

/-- Extract the time-direction partial from componentwise derivative data. -/
lemma deriv0_of_fd {F : Space 2 → ℝ} {a b : ℝ} {p : Space 2}
    (h : HasFDerivAt F (gradCLM a b) p) :
    (∂[(0 : Fin 2)] F) p = a := by
  show Space.deriv 0 F p = a
  unfold Space.deriv
  rw [h.fderiv]
  exact gradCLM_basis0 a b

/-- Extract the space-direction partial from componentwise derivative data. -/
lemma deriv1_of_fd {F : Space 2 → ℝ} {a b : ℝ} {p : Space 2}
    (h : HasFDerivAt F (gradCLM a b) p) :
    (∂[(1 : Fin 2)] F) p = b := by
  show Space.deriv 1 F p = b
  unfold Space.deriv
  rw [h.fderiv]
  exact gradCLM_basis1 a b

/-! Jet coordinates of the packaged field. -/

lemma j00_fst : j00.1 = (0 : MultiIndex 2) := by decide
lemma toList_j10 : j10.1.toList = [0] := by decide
lemma toList_j01 : j01.1.toList = [1] := by decide
lemma j00_order : j00.1.order = 0 := by decide
lemma j10_order : j10.1.order = 1 := by decide
lemma j01_order : j01.1.order = 1 := by decide

lemma iteratedDeriv_j10 (F : Space 2 → ℝ) : (∂^[j10.1] F) = ∂[(0 : Fin 2)] F := by
  show j10.1.toList.foldr (fun i g => Space.deriv i g) F = _
  rw [toList_j10]
  rfl

lemma iteratedDeriv_j01 (F : Space 2 → ℝ) : (∂^[j01.1] F) = ∂[(1 : Fin 2)] F := by
  show j01.1.toList.foldr (fun i g => Space.deriv i g) F = _
  rw [toList_j01]
  rfl

variable (q qt qx : ℝ → ℝ → ℝ)

/-- Jet coordinate (0,0): the field value. -/
lemma jet2_coord00 (p : Space 2) :
    (jetAt 1 (mkField2 q) p).coord j00 0 = q (p.val 0) (p.val 1) := by
  show jetCoordinatesAt 1 (mkField2 q) p j00 0 = _
  unfold jetCoordinatesAt
  rw [j00_fst]
  simp [mkField2_apply]

/-- Jet coordinate (1,0): the time-velocity u_t. -/
lemma jet2_coord10
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (p : Space 2) :
    (jetAt 1 (mkField2 q) p).coord j10 0 = qt (p.val 0) (p.val 1) := by
  show jetCoordinatesAt 1 (mkField2 q) p j10 0 = _
  unfold jetCoordinatesAt
  rw [show (fun y => (mkField2 q y) 0) = onPlane q from rfl]
  rw [iteratedDeriv_j10]
  exact deriv0_of_fd (hq p)

/-- Jet coordinate (0,1): the space-gradient u_x. -/
lemma jet2_coord01
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (p : Space 2) :
    (jetAt 1 (mkField2 q) p).coord j01 0 = qx (p.val 0) (p.val 1) := by
  show jetCoordinatesAt 1 (mkField2 q) p j01 0 = _
  unfold jetCoordinatesAt
  rw [show (fun y => (mkField2 q y) 0) = onPlane q from rfl]
  rw [iteratedDeriv_j01]
  exact deriv1_of_fd (hq p)

end PN2

#print axioms PN2.jet2_coord10

/-! ## CAMP B — STAGE 2: the bridge
    PhysLean's d = 2 Euler–Lagrange component of the lapse field
    Lagrangian, unfolded in closed form, and the statement-fidelity
    theorem: SatisfiesEulerLagrange ⟺ the cleared field equation of
    Z-N.2 Tiers 1–2. -/

namespace PN2

open Space

/-! FD calculus: quotient and product rules carried through gradCLM. -/

lemma gradCLM_apply (a b : ℝ) (y : Space 2) :
    gradCLM a b y = a * Space.coord 0 y + b * Space.coord 1 y := by
  simp [gradCLM, Space.coordCLM_apply]

/-- Quotient rule, componentwise. -/
lemma fd_div {F G : Space 2 → ℝ} {a b c d : ℝ} {p : Space 2}
    (hF : HasFDerivAt F (gradCLM a b) p) (hG : HasFDerivAt G (gradCLM c d) p)
    (hG0 : G p ≠ 0) :
    HasFDerivAt (fun y => F y / G y)
      (gradCLM ((a * G p - F p * c) / G p ^ 2) ((b * G p - F p * d) / G p ^ 2)) p := by
  have hinv : HasFDerivAt (fun y => (G y)⁻¹)
      ((-(G p ^ 2)⁻¹) • gradCLM c d) p :=
    (hasDerivAt_inv hG0).comp_hasFDerivAt p hG
  have hprod := HasFDerivAt.mul hF hinv
  simp only [div_eq_mul_inv]
  convert hprod using 1
  ext y
  simp only [gradCLM_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Negated product rule, componentwise. -/
lemma fd_neg_mul {F G : Space 2 → ℝ} {a b c d : ℝ} {p : Space 2}
    (hF : HasFDerivAt F (gradCLM a b) p) (hG : HasFDerivAt G (gradCLM c d) p) :
    HasFDerivAt (fun y => -(F y * G y))
      (gradCLM (-(F p * c + G p * a)) (-(F p * d + G p * b))) p := by
  have h := (HasFDerivAt.mul hF hG).neg
  convert h using 1
  ext y
  simp only [gradCLM_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

/-! The bridge proper. -/

variable (q qt qx qtt m qxx N nt nx : ℝ → ℝ → ℝ) (V V' : ℝ → ℝ)

lemma lapseField_coordDeriv (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (I : DerivativeIndex 2 1) (b : Fin 1) (J : JetPoint 2 1 1) :
    (lapseFieldLagrangian N V V' hNpos hV).coordDeriv I b J
      = if I = j10 then J.coord j10 0 / N (J.base.val 0) (J.base.val 1)
        else if I = j01 then -(N (J.base.val 0) (J.base.val 1) * J.coord j01 0)
        else -(N (J.base.val 0) (J.base.val 1) * V' (J.coord j00 0)) := rfl

/-- **The bridge: PhysLean's d = 2 EL component of the lapse field
    Lagrangian, in closed form.** All total derivatives are honest
    Fréchet data on the plane (hq, hqt, hqx, hN); one mixed partial m
    serves both slots — the Schwarz polish derives exactly that package
    from C² smoothness. -/
lemma elComponent_eq2
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (hqt : ∀ p : Space 2, HasFDerivAt (onPlane qt)
      (gradCLM (qtt (p.val 0) (p.val 1)) (m (p.val 0) (p.val 1))) p)
    (hqx : ∀ p : Space 2, HasFDerivAt (onPlane qx)
      (gradCLM (m (p.val 0) (p.val 1)) (qxx (p.val 0) (p.val 1))) p)
    (hN : ∀ p : Space 2, HasFDerivAt (onPlane N)
      (gradCLM (nt (p.val 0) (p.val 1)) (nx (p.val 0) (p.val 1))) p)
    (p : Space 2) :
    eulerLagrangeComponent (lapseFieldLagrangian N V V' hNpos hV) 0 (mkField2 q) p
      = -(N (p.val 0) (p.val 1) * V' (q (p.val 0) (p.val 1)))
        - (qtt (p.val 0) (p.val 1) * N (p.val 0) (p.val 1)
            - qt (p.val 0) (p.val 1) * nt (p.val 0) (p.val 1))
          / (N (p.val 0) (p.val 1)) ^ 2
        + (nx (p.val 0) (p.val 1) * qx (p.val 0) (p.val 1)
            + N (p.val 0) (p.val 1) * qxx (p.val 0) (p.val 1)) := by
  have hne : onPlane N p ≠ 0 := ne_of_gt (hNpos _ _)
  have h00 : eulerLagrangeTerm (lapseFieldLagrangian N V V' hNpos hV) j00 0 (mkField2 q) p
      = -(N (p.val 0) (p.val 1) * V' (q (p.val 0) (p.val 1))) := by
    rw [eulerLagrangeTerm_apply, j00_order]
    unfold iteratedTotalDerivative
    rw [j00_fst]
    simp only [Space.iteratedDeriv_zero, evalOnJet_apply]
    rw [lapseField_coordDeriv, if_neg j00_ne_j10, if_neg j00_ne_j01, jetAt_base,
      jet2_coord00]
    simp
  have h10 : eulerLagrangeTerm (lapseFieldLagrangian N V V' hNpos hV) j10 0 (mkField2 q) p
      = -((qtt (p.val 0) (p.val 1) * N (p.val 0) (p.val 1)
          - qt (p.val 0) (p.val 1) * nt (p.val 0) (p.val 1))
         / (N (p.val 0) (p.val 1)) ^ 2) := by
    rw [eulerLagrangeTerm_apply, j10_order]
    unfold iteratedTotalDerivative
    have hfun : evalOnJet 1 ((lapseFieldLagrangian N V V' hNpos hV).coordDeriv j10 0)
        (mkField2 q) = fun y => onPlane qt y / onPlane N y := by
      funext y
      rw [evalOnJet_apply, lapseField_coordDeriv, if_pos rfl, jetAt_base,
        jet2_coord10 q qt qx hq y]
      rfl
    rw [hfun, iteratedDeriv_j10, deriv0_of_fd (fd_div (hqt p) (hN p) hne)]
    simp [onPlane]
  have h01 : eulerLagrangeTerm (lapseFieldLagrangian N V V' hNpos hV) j01 0 (mkField2 q) p
      = nx (p.val 0) (p.val 1) * qx (p.val 0) (p.val 1)
        + N (p.val 0) (p.val 1) * qxx (p.val 0) (p.val 1) := by
    rw [eulerLagrangeTerm_apply, j01_order]
    unfold iteratedTotalDerivative
    have hfun : evalOnJet 1 ((lapseFieldLagrangian N V V' hNpos hV).coordDeriv j01 0)
        (mkField2 q) = fun y => -(onPlane N y * onPlane qx y) := by
      funext y
      rw [evalOnJet_apply, lapseField_coordDeriv, if_neg j01_ne_j10, if_pos rfl, jetAt_base,
        jet2_coord01 q qt qx hq y]
      rfl
    rw [hfun, iteratedDeriv_j01, deriv1_of_fd (fd_neg_mul (hN p) (hqx p))]
    simp [onPlane]
    ring
  rw [eulerLagrangeComponent_apply, sum_derivIndex21, h00, h10, h01]
  ring

/-- The point (t, x) of the plane. -/
def atPoint (t x : ℝ) : Space 2 := ⟨fun i => if i = 0 then t else x⟩

lemma atPoint_val0 (t x : ℝ) : (atPoint t x).val 0 = t := by simp [atPoint]
lemma atPoint_val1 (t x : ℝ) : (atPoint t x).val 1 = x := by simp [atPoint]

/-- **STATEMENT FIDELITY, d = 2: SatisfiesEulerLagrange ⟺ the cleared
    field equation of Z-N.2 Tiers 1–2.** PhysLean's variational EL
    condition for the lapse field Lagrangian IS the equation
    N·u_tt + N³·V′(u) = u_t·N_t + N²·N_x·u_x + N³·u_xx. -/
theorem satisfiesEL_iff_cleared2
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (hqt : ∀ p : Space 2, HasFDerivAt (onPlane qt)
      (gradCLM (qtt (p.val 0) (p.val 1)) (m (p.val 0) (p.val 1))) p)
    (hqx : ∀ p : Space 2, HasFDerivAt (onPlane qx)
      (gradCLM (m (p.val 0) (p.val 1)) (qxx (p.val 0) (p.val 1))) p)
    (hN : ∀ p : Space 2, HasFDerivAt (onPlane N)
      (gradCLM (nt (p.val 0) (p.val 1)) (nx (p.val 0) (p.val 1))) p) :
    SatisfiesEulerLagrange (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q)
      ↔ ∀ t x, N t x * qtt t x + (N t x) ^ 3 * V' (q t x)
          = qt t x * nt t x + (N t x) ^ 2 * nx t x * qx t x
            + (N t x) ^ 3 * qxx t x := by
  unfold SatisfiesEulerLagrange
  constructor
  · intro h t x
    have hx0 : eulerLagrangeOp (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q)
        (atPoint t x) 0 = 0 := by
      rw [h]; simp
    rw [eulerLagrangeOp_apply,
      elComponent_eq2 q qt qx qtt m qxx N nt nx V V' hNpos hV hq hqt hqx hN (atPoint t x),
      atPoint_val0, atPoint_val1] at hx0
    have hNt : N t x ≠ 0 := ne_of_gt (hNpos t x)
    field_simp at hx0
    linarith [hx0]
  · intro h
    funext p
    have ht := h (p.val 0) (p.val 1)
    have hNt : N (p.val 0) (p.val 1) ≠ 0 := ne_of_gt (hNpos _ _)
    show WithLp.toLp 2 (fun b => eulerLagrangeComponent
      (lapseFieldLagrangian N V V' hNpos hV) b (mkField2 q) p) = _
    have hzero : (fun b : Fin 1 => eulerLagrangeComponent
        (lapseFieldLagrangian N V V' hNpos hV) b (mkField2 q) p) = fun _ => (0 : ℝ) := by
      funext b
      have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
      subst hb
      rw [elComponent_eq2 q qt qx qtt m qxx N nt nx V V' hNpos hV hq hqt hqx hN p]
      have hdiv : (qtt (p.val 0) (p.val 1) * N (p.val 0) (p.val 1)
          - qt (p.val 0) (p.val 1) * nt (p.val 0) (p.val 1))
            / (N (p.val 0) (p.val 1)) ^ 2
          = -(N (p.val 0) (p.val 1) * V' (q (p.val 0) (p.val 1)))
            + (nx (p.val 0) (p.val 1) * qx (p.val 0) (p.val 1)
               + N (p.val 0) (p.val 1) * qxx (p.val 0) (p.val 1)) := by
        rw [div_eq_iff (by positivity)]
        linear_combination ht
      rw [hdiv]
      ring
    rw [hzero]
    simp
    rfl

end PN2

#print axioms PN2.satisfiesEL_iff_cleared2

/-! ## CAMP C — STAGE 1: the regularity discharge (Tier 3c at d = 2)
    For smooth N(t,x) and V′ (and V differentiable), the lapse field
    Lagrangian is smooth in PhysLean's jet coordinates: the regularity
    the fundamental theorem of variational calculus requires, PROVED. -/

namespace PN2

open scoped ContDiff
open Space

lemma contDiff_baseval2 (i : Fin 2) :
    ContDiff ℝ ∞ (fun p : Space 2 × JetCoordinates 2 1 1 => p.1.val i) := by
  have h : (fun p : Space 2 × JetCoordinates 2 1 1 => p.1.val i)
      = fun p => Space.coordCLM i p.1 := by
    funext p
    rw [Space.coordCLM_apply, Space.coord_apply]
  rw [h]
  exact (Space.coordCLM i).contDiff.comp contDiff_fst

lemma contDiff_fiberval2 (I : DerivativeIndex 2 1) (b : Fin 1) :
    ContDiff ℝ ∞ (fun p : Space 2 × JetCoordinates 2 1 1 => p.2 I b) := by
  fun_prop

variable (N : ℝ → ℝ → ℝ) (V V' : ℝ → ℝ)

/-- **The d = 2 regularity debt, discharged.** -/
theorem lapseField_smoothInCoordinates
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hNs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => N p.1 p.2))
    (hV's : ContDiff ℝ ∞ V') :
    (lapseFieldLagrangian N V V' hNpos hV).SmoothInCoordinates := by
  have hbase : ContDiff ℝ ∞ (fun p : Space 2 × JetCoordinates 2 1 1 =>
      ((p.1.val 0, p.1.val 1) : ℝ × ℝ)) :=
    (contDiff_baseval2 0).prodMk (contDiff_baseval2 1)
  have hNcd : ContDiff ℝ ∞ (fun p : Space 2 × JetCoordinates 2 1 1 =>
      N (p.1.val 0) (p.1.val 1)) := hNs.comp hbase
  constructor
  · -- continuity of L itself in coordinates
    have hVc : Continuous V := by
      rw [continuous_iff_continuousAt]
      exact fun z => (hV z).continuousAt
    have hNc := hNcd.continuous
    have hf10 := (contDiff_fiberval2 j10 0).continuous
    have hf01 := (contDiff_fiberval2 j01 0).continuous
    have hf00 := (contDiff_fiberval2 j00 0).continuous
    show Continuous fun p : Space 2 × JetCoordinates 2 1 1 =>
      (p.2 j10 0) ^ 2 / (2 * N (p.1.val 0) (p.1.val 1))
        - N (p.1.val 0) (p.1.val 1) * (p.2 j01 0) ^ 2 / 2
        - N (p.1.val 0) (p.1.val 1) * V (p.2 j00 0)
    apply Continuous.sub
    · apply Continuous.sub
      · apply Continuous.div (hf10.pow 2) (continuous_const.mul hNc)
        intro p
        exact ne_of_gt (mul_pos two_pos (hNpos _ _))
      · exact (hNc.mul (hf01.pow 2)).div_const 2
    · exact hNc.mul (hVc.comp hf00)
  · -- smoothness of the coordinate derivatives in coordinates
    intro I b
    by_cases h10 : I = j10
    · subst h10
      have hfun : (fun p : Space 2 × JetCoordinates 2 1 1 =>
          (lapseFieldLagrangian N V V' hNpos hV).coordDeriv j10 b
            (JetPoint.ofBaseCoordinates p.1 p.2))
          = fun p => p.2 j10 0 / N (p.1.val 0) (p.1.val 1) := by
        funext p
        rw [lapseField_coordDeriv, if_pos rfl]
        rfl
      rw [hfun]
      exact (contDiff_fiberval2 j10 0).div hNcd (fun p => ne_of_gt (hNpos _ _))
    · by_cases h01 : I = j01
      · subst h01
        have hfun : (fun p : Space 2 × JetCoordinates 2 1 1 =>
            (lapseFieldLagrangian N V V' hNpos hV).coordDeriv j01 b
              (JetPoint.ofBaseCoordinates p.1 p.2))
            = fun p => -(N (p.1.val 0) (p.1.val 1) * p.2 j01 0) := by
          funext p
          rw [lapseField_coordDeriv, if_neg j01_ne_j10, if_pos rfl]
          rfl
        rw [hfun]
        exact (hNcd.mul (contDiff_fiberval2 j01 0)).neg
      · have hfun : (fun p : Space 2 × JetCoordinates 2 1 1 =>
            (lapseFieldLagrangian N V V' hNpos hV).coordDeriv I b
              (JetPoint.ofBaseCoordinates p.1 p.2))
            = fun p => -(N (p.1.val 0) (p.1.val 1) * V' (p.2 j00 0)) := by
          funext p
          rw [lapseField_coordDeriv, if_neg h10, if_neg h01]
          rfl
        rw [hfun]
        exact (hNcd.mul (hV's.comp (contDiff_fiberval2 j00 0))).neg

end PN2

#print axioms PN2.lapseField_smoothInCoordinates

/-! ## CAMP C — STAGE 2: the ported Z-N.2 Tier 2 ledger
    (same statements, same proofs, this workspace) -/

namespace PN2

variable (φ pt px ptt mm bx n ntt nxx : ℝ → ℝ → ℝ) (V V' : ℝ → ℝ) (t x : ℝ)

theorem energy_time_deriv
    (hNpos : ∀ s y, 0 < n s y)
    (hφt : HasDerivAt (fun s => φ s x) (pt t x) t)
    (hptt : HasDerivAt (fun s => pt s x) (ptt t x) t)
    (hpxt : HasDerivAt (fun s => px s x) (mm t x) t)
    (hnt : HasDerivAt (fun s => n s x) (ntt t x) t)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hEL : n t x * ptt t x + (n t x)^3 * V' (φ t x)
         = pt t x * ntt t x + (n t x)^2 * nxx t x * px t x + (n t x)^3 * bx t x) :
    HasDerivAt (fun s => (pt s x)^2 / (2 * n s x) + n s x * ((px s x)^2 / 2 + V (φ s x)))
      (ntt t x / n t x * ((pt t x)^2 / (2 * n t x) + n t x * ((px t x)^2 / 2 + V (φ t x)))
        + (nxx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
           + n t x * (px t x * mm t x))) t := by
  have hn : n t x ≠ 0 := ne_of_gt (hNpos t x)
  have h2n : 2 * n t x ≠ 0 := by positivity
  have hkin := (hptt.pow 2).div (hnt.const_mul 2) h2n
  have hVc : HasDerivAt (fun s => V (φ s x)) (V' (φ t x) * pt t x) t :=
    (hV (φ t x)).comp t hφt
  have hin := ((hpxt.pow 2).div_const 2).add hVc
  have hpot := hnt.mul hin
  have htot := hkin.add hpot
  convert htot using 1
  have hELa : ptt t x = (pt t x * ntt t x + (n t x)^2 * nxx t x * px t x
      + (n t x)^3 * bx t x - (n t x)^3 * V' (φ t x)) / n t x := by
    rw [eq_div_iff hn]
    linear_combination hEL
  rw [hELa]
  push_cast
  field_simp
  simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply]
  ring

theorem flux_space_deriv
    (hptx : HasDerivAt (fun y => pt t y) (mm t x) x)
    (hpxx : HasDerivAt (fun y => px t y) (bx t x) x)
    (hnx : HasDerivAt (fun y => n t y) (nxx t x) x) :
    HasDerivAt (fun y => -(n t y * (px t y * pt t y)))
      (-(nxx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
         + n t x * (px t x * mm t x))) x := by
  have hinner := hpxx.mul hptx
  have hprod := hnx.mul hinner
  have h := hprod.neg
  convert h using 1
  simp only [Pi.mul_apply]
  ring

/-- **Z-N.2 SOURCED CONTINUITY (ported):** ∂t ρE + ∂x f = (∂tN/N)·ρE. -/
theorem sourced_continuity
    (hNpos : ∀ s y, 0 < n s y)
    (hφt : HasDerivAt (fun s => φ s x) (pt t x) t)
    (hptt : HasDerivAt (fun s => pt s x) (ptt t x) t)
    (hpxt : HasDerivAt (fun s => px s x) (mm t x) t)
    (hptx : HasDerivAt (fun y => pt t y) (mm t x) x)
    (hpxx : HasDerivAt (fun y => px t y) (bx t x) x)
    (hnt : HasDerivAt (fun s => n s x) (ntt t x) t)
    (hnx : HasDerivAt (fun y => n t y) (nxx t x) x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hEL : n t x * ptt t x + (n t x)^3 * V' (φ t x)
         = pt t x * ntt t x + (n t x)^2 * nxx t x * px t x + (n t x)^3 * bx t x)
    (Et Fx : ℝ)
    (hEt : HasDerivAt (fun s => (pt s x)^2 / (2 * n s x)
        + n s x * ((px s x)^2 / 2 + V (φ s x))) Et t)
    (hFx : HasDerivAt (fun y => -(n t y * (px t y * pt t y))) Fx x) :
    Et + Fx = ntt t x / n t x
      * ((pt t x)^2 / (2 * n t x) + n t x * ((px t x)^2 / 2 + V (φ t x))) := by
  have h1 := energy_time_deriv φ pt px ptt mm bx n ntt nxx V V' t x
    hNpos hφt hptt hpxt hnt hV hEL
  have h2 := flux_space_deriv pt px mm bx n nxx t x hptx hpxx hnx
  have e1 : Et = ntt t x / n t x * ((pt t x)^2 / (2 * n t x)
      + n t x * ((px t x)^2 / 2 + V (φ t x)))
      + (nxx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
         + n t x * (px t x * mm t x)) := hEt.unique h1
  have e2 : Fx = -(nxx t x * (px t x * pt t x) + n t x * (bx t x * pt t x)
      + n t x * (px t x * mm t x)) := hFx.unique h2
  rw [e1, e2]
  ring

variable (c cx : ℝ → ℝ → ℝ)

theorem arena_obstruction_x (k : ℝ)
    (hk : ∀ y, n t y * c t y = k)
    (hnx : HasDerivAt (fun y => n t y) (nxx t x) x)
    (hcx : HasDerivAt (fun y => c t y) (cx t x) x) :
    nxx t x * c t x + n t x * cx t x = 0 := by
  have hprod := hnx.mul hcx
  have hconst : HasDerivAt (fun y => n t y * c t y) 0 x := by
    have : (fun y => n t y * c t y) = fun _ => k := funext hk
    rw [this]
    exact hasDerivAt_const x k
  exact hprod.unique hconst

/-- **Z-N.2 IRREMOVABILITY CORE (ported):** ∂xN = 0 ⟺ ∂xC = 0. -/
theorem obstruction_iff (k : ℝ)
    (hNpos : ∀ s y, 0 < n s y) (hCpos : ∀ s y, 0 < c s y)
    (hk : ∀ y, n t y * c t y = k)
    (hnx : HasDerivAt (fun y => n t y) (nxx t x) x)
    (hcx : HasDerivAt (fun y => c t y) (cx t x) x) :
    nxx t x = 0 ↔ cx t x = 0 := by
  have hobs := arena_obstruction_x n nxx t x c cx k hk hnx hcx
  have hn : n t x ≠ 0 := ne_of_gt (hNpos t x)
  have hc : c t x ≠ 0 := ne_of_gt (hCpos t x)
  constructor
  · intro h
    rw [h, zero_mul, zero_add] at hobs
    exact (mul_eq_zero.mp hobs).resolve_left hn
  · intro h
    rw [h, mul_zero, add_zero] at hobs
    exact (mul_eq_zero.mp hobs).resolve_right hc

end PN2

#print axioms PN2.sourced_continuity
#print axioms PN2.obstruction_iff

/-! ## CAMP C — STAGE 3: THE CAPSTONE
    δS = 0 ⟹ the field Euler–Lagrange equation ⟹ sourced continuity:
    the N-2 ledger, demanded end to end by the action principle. -/

namespace PN2

open scoped ContDiff

variable (q qt qx qtt m qxx N nt nx : ℝ → ℝ → ℝ) (V V' : ℝ → ℝ)

/-- **The action principle delivers the field EL equation** — PhysLean's
    fundamental theorem of variational calculus at d = 2, instantiated. -/
theorem action_critical_iff_el2
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (hqt : ∀ p : Space 2, HasFDerivAt (onPlane qt)
      (gradCLM (qtt (p.val 0) (p.val 1)) (m (p.val 0) (p.val 1))) p)
    (hqx : ∀ p : Space 2, HasFDerivAt (onPlane qx)
      (gradCLM (m (p.val 0) (p.val 1)) (qxx (p.val 0) (p.val 1))) p)
    (hN : ∀ p : Space 2, HasFDerivAt (onPlane N)
      (gradCLM (nt (p.val 0) (p.val 1)) (nx (p.val 0) (p.val 1))) p)
    (hf : ContDiff ℝ ∞ (mkField2 q))
    (hLs : (lapseFieldLagrangian N V V' hNpos hV).SmoothInCoordinates)
    (hfin : HasFiniteAction (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q)) :
    IsCritical (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q)
      ↔ ∀ t x, N t x * qtt t x + (N t x) ^ 3 * V' (q t x)
          = qt t x * nt t x + (N t x) ^ 2 * nx t x * qx t x
            + (N t x) ^ 3 * qxx t x :=
  (isCritical_iff_satisfiesEulerLagrange_of_contDiff_and_smoothInCoordinates
      (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q) hf hLs hfin).trans
    (satisfiesEL_iff_cleared2 q qt qx qtt m qxx N nt nx V V' hNpos hV hq hqt hqx hN)

/-- **THE CAPSTONE — Z-N.2 end to end: δS = 0 ⟹ sourced continuity.**
    If the field is a critical point of the lapse action on the (t,x)
    plane, then the energy ledger holds: ∂t ρE + ∂x f = (∂tN/N)·ρE —
    the flux intact, the source purely the time variation of the clock,
    demanded by the variational principle. -/
theorem action_critical_sourced_continuity
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (hqt : ∀ p : Space 2, HasFDerivAt (onPlane qt)
      (gradCLM (qtt (p.val 0) (p.val 1)) (m (p.val 0) (p.val 1))) p)
    (hqx : ∀ p : Space 2, HasFDerivAt (onPlane qx)
      (gradCLM (m (p.val 0) (p.val 1)) (qxx (p.val 0) (p.val 1))) p)
    (hN : ∀ p : Space 2, HasFDerivAt (onPlane N)
      (gradCLM (nt (p.val 0) (p.val 1)) (nx (p.val 0) (p.val 1))) p)
    (hf : ContDiff ℝ ∞ (mkField2 q))
    (hLs : (lapseFieldLagrangian N V V' hNpos hV).SmoothInCoordinates)
    (hfin : HasFiniteAction (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q))
    (hcrit : IsCritical (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q))
    (t x : ℝ)
    (hφt : HasDerivAt (fun s => q s x) (qt t x) t)
    (hptt : HasDerivAt (fun s => qt s x) (qtt t x) t)
    (hpxt : HasDerivAt (fun s => qx s x) (m t x) t)
    (hptx : HasDerivAt (fun y => qt t y) (m t x) x)
    (hpxx : HasDerivAt (fun y => qx t y) (qxx t x) x)
    (hnt : HasDerivAt (fun s => N s x) (nt t x) t)
    (hnx : HasDerivAt (fun y => N t y) (nx t x) x)
    (Et Fx : ℝ)
    (hEt : HasDerivAt (fun s => (qt s x)^2 / (2 * N s x)
        + N s x * ((qx s x)^2 / 2 + V (q s x))) Et t)
    (hFx : HasDerivAt (fun y => -(N t y * (qx t y * qt t y))) Fx x) :
    Et + Fx = nt t x / N t x
      * ((qt t x)^2 / (2 * N t x) + N t x * ((qx t x)^2 / 2 + V (q t x))) := by
  have hEL := (action_critical_iff_el2 q qt qx qtt m qxx N nt nx V V'
    hNpos hV hq hqt hqx hN hf hLs hfin).mp hcrit t x
  exact sourced_continuity q qt qx qtt m qxx N nt nx V V' t x
    hNpos hφt hptt hpxt hptx hpxx hnt hnx hV hEL Et Fx hEt hFx

/-- **THE CANON COROLLARY — Z-N.2 in the book's own symbols.**
    Wire in the arena law N = C_floor/C and the Generative Law
    ∂tC = G − D_loss: if the field is a critical point of the lapse
    action, then ∂t ρE + ∂x f = ((D_loss − G)/C)·ρE — canon's N-2
    sourced continuity, demanded by δS = 0. -/
theorem action_critical_sourced_continuity_canon
    (C Gg Dl : ℝ → ℝ → ℝ) (C_floor : ℝ) (hCf : 0 < C_floor)
    (hCpos : ∀ t x, 0 < C t x)
    (hNdef : N = fun t x => C_floor / C t x)
    (hntdef : nt = fun t x => -(C_floor * (Gg t x - Dl t x)) / (C t x) ^ 2)
    (hNpos : ∀ t x, 0 < N t x)
    (hV : ∀ z, HasDerivAt V (V' z) z)
    (hq : ∀ p : Space 2, HasFDerivAt (onPlane q)
      (gradCLM (qt (p.val 0) (p.val 1)) (qx (p.val 0) (p.val 1))) p)
    (hqt : ∀ p : Space 2, HasFDerivAt (onPlane qt)
      (gradCLM (qtt (p.val 0) (p.val 1)) (m (p.val 0) (p.val 1))) p)
    (hqx : ∀ p : Space 2, HasFDerivAt (onPlane qx)
      (gradCLM (m (p.val 0) (p.val 1)) (qxx (p.val 0) (p.val 1))) p)
    (hN : ∀ p : Space 2, HasFDerivAt (onPlane N)
      (gradCLM (nt (p.val 0) (p.val 1)) (nx (p.val 0) (p.val 1))) p)
    (hf : ContDiff ℝ ∞ (mkField2 q))
    (hLs : (lapseFieldLagrangian N V V' hNpos hV).SmoothInCoordinates)
    (hfin : HasFiniteAction (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q))
    (hcrit : IsCritical (lapseFieldLagrangian N V V' hNpos hV) (mkField2 q))
    (t x : ℝ)
    (hCt : HasDerivAt (fun s => C s x) (Gg t x - Dl t x) t)
    (hφt : HasDerivAt (fun s => q s x) (qt t x) t)
    (hptt : HasDerivAt (fun s => qt s x) (qtt t x) t)
    (hpxt : HasDerivAt (fun s => qx s x) (m t x) t)
    (hptx : HasDerivAt (fun y => qt t y) (m t x) x)
    (hpxx : HasDerivAt (fun y => qx t y) (qxx t x) x)
    (hnx : HasDerivAt (fun y => N t y) (nx t x) x)
    (Et Fx : ℝ)
    (hEt : HasDerivAt (fun s => (qt s x)^2 / (2 * N s x)
        + N s x * ((qx s x)^2 / 2 + V (q s x))) Et t)
    (hFx : HasDerivAt (fun y => -(N t y * (qx t y * qt t y))) Fx x) :
    Et + Fx = ((Dl t x - Gg t x) / C t x)
      * ((qt t x)^2 / (2 * N t x) + N t x * ((qx t x)^2 / 2 + V (q t x))) := by
  have hnt : HasDerivAt (fun s => N s x) (nt t x) t := by
    rw [hNdef, hntdef]
    have h := (hasDerivAt_const t C_floor).div hCt (ne_of_gt (hCpos t x))
    simpa [Pi.div_def] using h
  have h := action_critical_sourced_continuity q qt qx qtt m qxx N nt nx V V'
    hNpos hV hq hqt hqx hN hf hLs hfin hcrit t x
    hφt hptt hpxt hptx hpxx hnt hnx Et Fx hEt hFx
  rw [h]
  rw [hNdef, hntdef]
  have hCt0 : C t x ≠ 0 := ne_of_gt (hCpos t x)
  have hCft : C_floor ≠ 0 := ne_of_gt hCf
  field_simp
  ring

end PN2

#print axioms PN2.action_critical_iff_el2
#print axioms PN2.action_critical_sourced_continuity
#print axioms PN2.action_critical_sourced_continuity_canon
