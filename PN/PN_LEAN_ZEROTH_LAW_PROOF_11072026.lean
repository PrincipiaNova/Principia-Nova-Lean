/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE ZEROTH PN LAW PAIR, KERNEL-CERTIFIED · 11/07/2026 · Lean 4 + mathlib

Authority (canon Ch7, verbatim): "∇⋅Cv = 0 ... The divergence measures whether
coherence is accumulating or depleting. Equilibrium is the absence of net
coherence accumulation in an open system." And the reason clause: "The
classical Zeroth Law assumed transitivity — that balance could be inferred
through a chain of intermediaries. The PN Zeroth Law replaces transitivity
with independent assessment. There are no middlemen. Every balance stands on
its own." (The same clause P3 feeds into the §20 Bell/λ lemma.)

MOVEMENT 1 — the equation, 1D: the printed object is the PRODUCT C·v; zero
divergence ⟺ the flux is identical across all stations — "absence of net
accumulation" as a theorem. Deriv-zero constancy engine (warm from the FRW
anchor and the Ledger tower).

MOVEMENT 2 — the reason clause, finite witness model (discriminating_case
species, WITNESS-GRADE, named): systems with an antisymmetric pairwise
net-flow J; Balance(X,Y) := J(X,Y) = 0 — the pairwise restatement of
Movement 1's two-station flux balance. The model deliberately assumes NO
potential form J(X,Y) = T(X) − T(Y): that absence is the content, because a
scalar-induced flow is exactly what forces transitivity back in. The matched
pair (ruled in, with sharpening): the scalar-induced flow IS transitive, the
witness flow is NOT — transitivity tracks the primitive scalar exactly,
which is canon's diagnosis ("relies on temperature as a primitive")
certified from both sides as a controlled experiment on one relation shape.

AXIOM NOTE: this is Axiom 3's thermodynamic face — the second no-middlemen
clause in the kernel column, beside the CRVL groupoid's kinematic locality
clause, with the topological face (winding/homotopy invariance) queued.

FENCES: 1D scoping for the divergence movement (higher-d stays prose);
differentiability of the flux named; the flow model is witness-grade — it
certifies that the classical inference CAN fail (all that "replaces
transitivity" claims), asserting nothing about any particular physical
triple. No hidden hypotheses: self-balance is free (J(X,X) = −J(X,X) over ℝ).
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

namespace PNZeroth

/-! ## MOVEMENT 1 — the equation (1D) -/

/-- **The printed object, unpacked.** ∇·(Cv) in one dimension is the
derivative of the product: d(C·v)/dx = C′v + Cv′. The law is about the
product C·v — the coherence flux — and this bridge keeps it so. -/
theorem divergence_of_product (C v : ℝ → ℝ) (x dC dv : ℝ)
    (hC : HasDerivAt C dC x) (hv : HasDerivAt v dv x) :
    HasDerivAt (fun y => C y * v y) (dC * v x + C x * dv) x :=
  hC.mul hv

/-- **Flux balance.** Zero divergence everywhere ⟹ the flux J = C·v is equal
at any two stations: what flows in flows out — canon's "absence of net
coherence accumulation" as a theorem. -/
theorem flux_balance (C v : ℝ → ℝ)
    (hdiff : Differentiable ℝ (fun y => C y * v y))
    (hdiv : ∀ x, deriv (fun y => C y * v y) x = 0)
    (x₁ x₂ : ℝ) :
    C x₂ * v x₂ = C x₁ * v x₁ :=
  is_const_of_deriv_eq_zero hdiff hdiv x₂ x₁

/-- **Equilibrium ⟺ flow balance**, both directions (differentiability of the
flux named): the divergence vanishes everywhere precisely when the flux is
identical across all stations. -/
theorem equilibrium_iff_flux_balance (C v : ℝ → ℝ)
    (hdiff : Differentiable ℝ (fun y => C y * v y)) :
    (∀ x, deriv (fun y => C y * v y) x = 0) ↔
      (∀ x₁ x₂, C x₂ * v x₂ = C x₁ * v x₁) := by
  constructor
  · intro h x₁ x₂
    exact is_const_of_deriv_eq_zero hdiff h x₂ x₁
  · intro h x
    have hconst : (fun y => C y * v y) = fun _ => C x * v x := by
      funext y
      exact h x y
    rw [hconst]
    exact deriv_const x _

/-! ## MOVEMENT 2 — the reason clause (finite witness model, witness-grade) -/

/-- The three systems of the witness model. -/
inductive Sys : Type
  | A | B | C
deriving DecidableEq

/-- **Balance** between two systems, in any flow model: zero net pairwise
flow — the pairwise restatement of Movement 1's two-station flux balance. -/
def Balance {S : Type*} (J : S → S → ℝ) (X Y : S) : Prop := J X Y = 0

/-- **The witness net-flow** (WITNESS-GRADE MODEL): A–B balanced, B–C
balanced, A–C not. Deliberately NOT of potential form T(X) − T(Y). -/
def Jw : Sys → Sys → ℝ
  | Sys.A, Sys.C => 1
  | Sys.C, Sys.A => -1
  | _, _ => 0

/-- The witness flow is a legitimate flow: antisymmetric in its arguments. -/
theorem Jw_antisymm : ∀ X Y, Jw X Y = -Jw Y X := by
  intro X Y
  cases X <;> cases Y <;> simp [Jw]

/-- **Self-balance is free**: antisymmetry alone forces J(X,X) = 0 — every
system balances itself, with no hidden hypothesis. -/
theorem balance_reflexive {S : Type*} (J : S → S → ℝ)
    (hanti : ∀ X Y, J X Y = -J Y X) (X : S) :
    Balance J X X := by
  have h := hanti X X
  unfold Balance
  linarith

/-- **Balance is mutual**: antisymmetry makes the relation symmetric. -/
theorem balance_symmetric {S : Type*} (J : S → S → ℝ)
    (hanti : ∀ X Y, J X Y = -J Y X) (X Y : S)
    (h : Balance J X Y) : Balance J Y X := by
  unfold Balance at h ⊢
  have := hanti Y X
  linarith

/-- **The scalar-induced flow**: a primitive temperature-like scalar T
induces J(X,Y) := T(X) − T(Y) — the classical picture. -/
def scalarFlow {S : Type*} (T : S → ℝ) (X Y : S) : ℝ := T X - T Y

/-- The scalar-induced flow is also a legitimate (antisymmetric) flow. -/
theorem scalarFlow_antisymm {S : Type*} (T : S → ℝ) :
    ∀ X Y, scalarFlow T X Y = -scalarFlow T Y X := by
  intro X Y
  unfold scalarFlow
  ring

/-- **The contrast shot (matched pair, side 1).** Balance through a primitive
scalar IS transitive — because equality of the scalar is. Transitivity was
always the scalar's property, never equilibrium's: canon's diagnosis
("relies on temperature as a primitive") certified from the classical side. -/
theorem classical_transitivity {S : Type*} (T : S → ℝ) (X Y Z : S)
    (hxy : Balance (scalarFlow T) X Y) (hyz : Balance (scalarFlow T) Y Z) :
    Balance (scalarFlow T) X Z := by
  unfold Balance scalarFlow at hxy hyz ⊢
  linarith

/-- **THE WITNESS (matched pair, side 2) — no middlemen.** In the witness
flow model: A balances B, B balances C, and A does NOT balance C. The
classical Zeroth inference — balance through a chain of intermediaries —
fails in a PN-shaped flow model. Independent assessment is necessary, not
stylistic. -/
theorem no_middlemen :
    (∀ X Y, Jw X Y = -Jw Y X) ∧
    Balance Jw Sys.A Sys.B ∧
    Balance Jw Sys.B Sys.C ∧
    ¬Balance Jw Sys.A Sys.C := by
  refine ⟨Jw_antisymm, ?_, ?_, ?_⟩
  · simp [Balance, Jw]
  · simp [Balance, Jw]
  · simp [Balance, Jw]

/-- **CAPSTONE — equilibrium is a relation, not an equivalence.** Over the
same relation shape: balance is reflexive (free, by antisymmetry) and
symmetric, the witness flow refutes transitivity, and the scalar-induced
flow restores it. Transitivity tracks the primitive scalar exactly — which
is what the classical Zeroth Law existed to manufacture (temperature as the
equivalence-class label), and exactly what the PN Zeroth Law declines to
assume. Every balance stands on its own. -/
theorem balance_not_equivalence :
    (∀ X, Balance Jw X X) ∧
    (∀ X Y, Balance Jw X Y → Balance Jw Y X) ∧
    ¬(∀ X Y Z, Balance Jw X Y → Balance Jw Y Z → Balance Jw X Z) ∧
    (∀ (S : Type) (T : S → ℝ) (X Y Z : S),
        Balance (scalarFlow T) X Y → Balance (scalarFlow T) Y Z →
        Balance (scalarFlow T) X Z) := by
  refine ⟨fun X => balance_reflexive Jw Jw_antisymm X,
          fun X Y h => balance_symmetric Jw Jw_antisymm X Y h,
          ?_,
          fun S T X Y Z hxy hyz => classical_transitivity T X Y Z hxy hyz⟩
  intro h
  have hAB : Balance Jw Sys.A Sys.B := by simp [Balance, Jw]
  have hBC : Balance Jw Sys.B Sys.C := by simp [Balance, Jw]
  have hAC := h Sys.A Sys.B Sys.C hAB hBC
  simp [Balance, Jw] at hAC

end PNZeroth

#print axioms PNZeroth.divergence_of_product
#print axioms PNZeroth.flux_balance
#print axioms PNZeroth.equilibrium_iff_flux_balance
#print axioms PNZeroth.Jw_antisymm
#print axioms PNZeroth.balance_reflexive
#print axioms PNZeroth.balance_symmetric
#print axioms PNZeroth.scalarFlow_antisymm
#print axioms PNZeroth.classical_transitivity
#print axioms PNZeroth.no_middlemen
#print axioms PNZeroth.balance_not_equivalence
