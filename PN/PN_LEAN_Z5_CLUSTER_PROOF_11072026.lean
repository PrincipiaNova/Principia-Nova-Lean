/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE §5 MINIMAL-MODEL CLUSTER · 11/07/2026 · Lean 4 + mathlib
THE ROSTER'S QUANTUM CORNER OPENS · purest Coherence-Axiom climb in the program

Flight plan PN_Z5_CLUSTER_FLIGHT_PLAN_11072026 — approved, all
four rulings, with the Ruling-1 UPGRADE: the certified face of Theorem 1
is not a workaround for the missing Uhlmann donor; it is CANON'S OWN
PRINTED PROOF, certified. Canon's "why it holds": "the fidelity of two
density matrices vanishes only when their supports are orthogonal
subspaces. Every state strictly inside the Bloch ball is full-rank...
Exclude the boundary and perfect distinguishability does not become
rare. It becomes impossible."

Authorities (verbatim, character-checked):
· Definition 1: "C(ρ) = Tr(ρ²)... For a qubit, C(ρ) = ½(1 + |r|²), which
  lies in [½, 1] automatically."
· The trace identity: "Not approximately. Identically: Tr(ρ[H,ρ]) = 0,
  always. Structured coherence transfer writes nothing to the ledger."
· Theorem 1 (No perfect distinguishability): "Any two states in the Mu
  region have strictly positive fidelity: F(ρ,σ) > 0." — FIDELITY, not
  Fisher (scoping-shorthand error corrected at source, 11/07).
· §5.7, canon's own scope: "The room has a roof. The cathedral does not."

THE LOUD SENTENCE: Theorem 1's certified face is the operational overlap
form — canon's own support-overlap argument; the Uhlmann-fidelity
statement itself remains prose, because NO fidelity donor exists in
mathlib. Logged, not hidden. HEDGE INHERITANCE (§22/Rice species): any
future claim that Theorem 1 is kernel-certified — including through
Ch13's printed citation of it — must carry this note.

Grain, per Ruling 3: Movement 1 DIMENSION-FREE (canon's "always" honored
at full strength — any square matrices, any dimension, any commutative
ring of entries); Movements 2–3 at qubit/Bloch grain, canon's own
minimal model, where "strictly inside" is ‖r‖ < 1 (canon's full-rank
gloss — Ruling 2's hypothesis is the book's own sentence). The Bloch
overlap (1 + ⟪r,s⟫)/2 is the model's trace form, Definition-1 species
(canon's C is its diagonal). The general-n PosDef version is cathedral
(§5.7), not roof.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

open scoped InnerProductSpace

namespace PNZ5

/-! ## MOVEMENT 1 — only the drain writes (dimension-free) -/

/-- **The trace identity — "Not approximately. Identically... always."**
Tr(ρ[H,ρ]) = 0 for ALL square matrices over ANY commutative ring, any
dimension: pure trace cyclicity. The reversible, work-like part of the
dynamics writes nothing to the coherence ledger — the modes can turn
forever and nothing is ever decided. -/
theorem hamiltonian_writes_nothing {n : Type*} [Fintype n] {R : Type*}
    [CommRing R] (ρ H : Matrix n n R) :
    (ρ * (H * ρ - ρ * H)).trace = 0 := by
  have h := Matrix.trace_mul_comm (ρ * H) ρ
  calc (ρ * (H * ρ - ρ * H)).trace
      = (ρ * (H * ρ)).trace - (ρ * (ρ * H)).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub]
    _ = ((ρ * H) * ρ).trace - (ρ * (ρ * H)).trace := by
        rw [Matrix.mul_assoc]
    _ = 0 := by rw [h]; ring

/-- **The glue (Ruling 4, IN): only the channels write.** In any rate
split L = (reversible commutator) + (channels), the commutator drops out
of Tr(ρ·L) identically — what reaches dC/dt is the channel part alone.
The formal backbone under "tracing never picks the braid; locking does." -/
theorem only_channels_write {n : Type*} [Fintype n] {R : Type*}
    [CommRing R] (ρ H K : Matrix n n R) :
    (ρ * ((H * ρ - ρ * H) + K)).trace = (ρ * K).trace := by
  rw [Matrix.mul_add, Matrix.trace_add, hamiltonian_writes_nothing ρ H,
    zero_add]

/-! ## MOVEMENT 2 — Definition 1's automatic bounds (qubit Bloch grain) -/

/-- Canon's qubit coherence norm: C(ρ) = ½(1 + |r|²) on the Bloch ball. -/
noncomputable def Cbloch (r : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 + ‖r‖ ^ 2) / 2

/-- **"Which lies in [½, 1] automatically."** The bounds are inherited
from the state space, not imposed: ½ at the dead center exactly, 1
exactly on the shell — strictly below 1 everywhere inside. The
first-axiom-to-fall promotion (Axiom 3's Mu-Bounded Norm as definition),
certified as algebra. -/
theorem definition_one_bounds (r : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r‖ ≤ 1) :
    1 / 2 ≤ Cbloch r ∧ Cbloch r ≤ 1 ∧
    (Cbloch r = 1 / 2 ↔ r = 0) ∧ (Cbloch r < 1 ↔ ‖r‖ < 1) := by
  unfold Cbloch
  have h0 : 0 ≤ ‖r‖ := norm_nonneg r
  have hsq : ‖r‖ ^ 2 ≤ 1 := by nlinarith
  refine ⟨by nlinarith [sq_nonneg ‖r‖], by nlinarith, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have h2 : ‖r‖ ^ 2 = 0 := by linarith
    have hr0 : ‖r‖ = 0 := (pow_eq_zero_iff (two_ne_zero)).mp h2
    exact norm_eq_zero.mp hr0
  · intro h
    subst h
    simp
  · intro h
    by_contra hge
    rw [not_lt] at hge
    have heq : ‖r‖ = 1 := le_antisymm hr hge
    rw [heq] at h
    norm_num at h
  · intro h
    nlinarith

/-- **The Mu interior** — strictly inside the ball, the ceiling is
strictly unattained: C < 1 everywhere a physical state lives. -/
theorem mu_interior (r : EuclideanSpace ℝ (Fin 3)) (hr : ‖r‖ < 1) :
    Cbloch r < 1 := by
  unfold Cbloch
  have h0 : 0 ≤ ‖r‖ := norm_nonneg r
  nlinarith

/-! ## MOVEMENT 3 — no perfect distinguishability (Theorem 1's certified
face = canon's own printed proof) -/

/-- The qubit overlap in Bloch form: Tr(ρσ) = ½(1 + r·s) — the model's
trace rule (Definition-1 species; canon's C(ρ) is its diagonal). -/
noncomputable def overlap (r s : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 + ⟪r, s⟫_ℝ) / 2

/-- **THEOREM 1's CERTIFIED FACE — no perfect distinguishability.** A
state strictly inside the Bloch ball (‖r‖ < 1 — canon's full-rank gloss,
Ruling 2's NAMED nondegeneracy) has strictly positive overlap with EVERY
state: no outcome, no test distinguishes it from anything with
certainty. Cauchy–Schwarz pins the inner product above −1. "Exclude the
boundary and perfect distinguishability does not become rare. It becomes
impossible." (The Uhlmann-fidelity name on the conclusion stays prose —
no mathlib donor; see the loud sentence in the header.) -/
theorem overlap_positive (r s : EuclideanSpace ℝ (Fin 3))
    (hr : ‖r‖ < 1) (hs : ‖s‖ ≤ 1) :
    0 < overlap r s := by
  unfold overlap
  have hcs : |⟪r, s⟫_ℝ| ≤ ‖r‖ * ‖s‖ := abs_real_inner_le_norm r s
  have h0r : 0 ≤ ‖r‖ := norm_nonneg r
  have h0s : 0 ≤ ‖s‖ := norm_nonneg s
  have habs := abs_le.mp hcs
  have hprod : ‖r‖ * ‖s‖ < 1 := by nlinarith
  linarith [habs.1]

/-- **The shell door (matched pair, house style).** On the boundary,
perfect distinguishability EXISTS: antipodal pure states have overlap
zero. The interior hypothesis of Theorem 1 is sharp — "perfect
distinguishability exists only where Theorem 1 does not apply, which is
only on the shell." -/
theorem shell_orthogonality_witness :
    ∃ r s : EuclideanSpace ℝ (Fin 3),
      ‖r‖ = 1 ∧ ‖s‖ = 1 ∧ overlap r s = 0 := by
  have ho := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)
  have hn : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := ho.1 0
  refine ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ),
    -(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)), hn, ?_, ?_⟩
  · rw [norm_neg]; exact hn
  · unfold overlap
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hn]
    norm_num

end PNZ5

#print axioms PNZ5.hamiltonian_writes_nothing
#print axioms PNZ5.only_channels_write
#print axioms PNZ5.definition_one_bounds
#print axioms PNZ5.mu_interior
#print axioms PNZ5.overlap_positive
#print axioms PNZ5.shell_orthogonality_witness
