/-
═══════════════════════════════════════════════════════════════════════════════
PN — THE §15 WITNESS TOWER · 11/07/2026 · Lean 4 + mathlib
Four columns of the PN Incompleteness Principle, bolted down.

FRAMEWORK-FREE FILE (the program's second, after the FRW anchor): zero PN
premises in any signature. The witnesses are the mainstream's own theorems;
the kernel holds four of §15's columns directly, with the diagonal core
displayed rather than cited.

Authorities (canon Z §15, verbatim, verified at source):
· The unifier: "Lawvere (1969) proved a single fixed-point theorem whose
  instances are the diagonal cores of Cantor's argument, Russell's paradox,
  Gödel's first theorem, and Tarski's undefinability... Where the columns
  could be unified, they have been — by theorem." (The gem theorem's target
  sentence.) Turing's halting problem "is the same diagonal run on machines
  ... it rides with that core."
· 15.1–15.2: "The theorem forbids a summit"; "the completed ladder of
  ordinals would itself be an ordinal standing above the completed ladder";
  "The totality can be spoken of; it cannot be a member of anything."
· The metric witness: the Mu-open manifold "contains sequences whose limits
  exist only in a completion no trajectory enters."
· The care-sentence, kept: "nothing here extends Gödel's theorem beyond its
  hypotheses... the wider principle is this framework's own claim...
  answerable to this book's falsifiers, not to Gödel's authority."

Found object, logged: mathlib's own docstring on the fixed-point donor reads
"an instance of Lawvere's fixed-point theorem... the diagonal argument
underlying cantor_surjective" — the community wrote canon's footnote without
knowing it.

COVERAGE (the file's spine): kernel-certified — the Totality column (Cantor
+ Burali-Forti + Russell), the Lawvere core with in-file unification, the
Turing rider, the Mu-open metric witness. DONOR-ABSENT, STAYS PROSE, LOUD —
Provability (Gödel), Truth (Tarski), Describability (Montague–Lévy), the
entire index family (no Poincaré–Hopf / hairy ball / Gauss–Bonnet / Morse /
Atiyah–Singer index theory in mathlib), Page–Wootters (physics). §15 is NOT
certified "as a whole"; the nine-fold recurrence claim remains the book's
own. Hedge-inheritance applies to any downstream "§15 certified" phrasing.
═══════════════════════════════════════════════════════════════════════════════
-/
import Mathlib

open scoped ZFClass

namespace PNZ15

/-! ## MOVEMENT 1 — the diagonal core and its certified columns -/

/-- **The Lawvere core, consumed.** A surjection of α onto its own function
space α → β forces every endofunction of β to have a fixed point — the
single categorical mechanism canon names under four of the nine columns. -/
theorem lawvere_core {α β : Type*} (f : α → α → β)
    (hf : Function.Surjective f) (g : β → β) : ∃ x, g x = x :=
  Function.exists_fixed_point_of_surjective f hf g

/-- **THE GEM — "Where the columns could be unified, they have been — by
theorem."** Cantor's conclusion derived FROM the Lawvere core, inside this
file: a surjection onto the power set would hand negation a fixed point —
a proposition equal to its own negation — which is absurd. The mechanism
displayed, not cited. -/
theorem diagonal_unification {α : Type*} (f : α → Set α) :
    ¬Function.Surjective f := by
  intro hf
  have hF : Function.Surjective fun a b => b ∈ f a := by
    intro g
    obtain ⟨a, ha⟩ := hf {b | g b}
    refine ⟨a, ?_⟩
    funext b
    simp only [ha, Set.mem_ofPred_eq]
  obtain ⟨p, hp⟩ := lawvere_core _ hF Not
  exact iff_not_self (iff_of_eq hp).symm

/-- **The summit forbidden** (Cantor 1891, consumed): no set surveys its own
power set. "The theorem forbids a summit — and in the same stroke it
generates the entire transfinite hierarchy." -/
theorem no_summit {α : Type*} (f : α → Set α) : ¬Function.Surjective f :=
  Function.cantor_surjective f

/-- **The totality is not an object, I** (Russell 1903, consumed): the
universe of sets is not a member of itself — the set of all sets fails;
the totality is a proper class. "It can be spoken of; it cannot be a
member of anything." -/
theorem totality_not_object_russell :
    (Set.univ : ZFClass.{0}) ᶜ∉ (Set.univ : ZFClass.{0}) :=
  ZFClass.univ_notCMem_univ

/-- **The totality is not an object, II** (Burali-Forti 1897, consumed —
mathlib carries the paradox by name): the ordinals form a proper class;
the completed ladder cannot stand on its own top rung. -/
theorem totality_not_object_burali_forti :
    ({x | x.IsOrdinal} : ZFClass.{0}) ᶜ∉ (Set.univ : ZFClass.{0}) :=
  ZFSet.isOrdinal_notCMem_univ

/-- **The diagonal on machines** (Turing 1936, consumed — the rider, seated
exactly where canon seats it): no procedure decides halting, and the
complement is not even semi-decidable. Computation's own self-verification
ceiling, the same wall §22's identity block builds on. -/
theorem halting_wall (n : ℕ) :
    (¬ComputablePred fun c => (Nat.Partrec.Code.eval c n).Dom) ∧
    (¬REPred fun c => ¬(Nat.Partrec.Code.eval c n).Dom) :=
  ⟨ComputablePred.halting_problem n, ComputablePred.halting_problem_not_re n⟩

/-! ## MOVEMENT 2 — the Mu-open metric witness (witness 9, constructive) -/

/-- **The completion no trajectory enters.** An explicit trajectory living
strictly inside the open coherence interval whose limit exists — and is
not in the space. The Mu-open manifold's signature, exhibited at interval
grain (model species: CΩ_strict / discriminating_case). Third appearance
of asymptote-not-arrival, in its purest form. -/
theorem mu_open_witness :
    ∃ x : ℕ → ℝ, (∀ n, x n ∈ Set.Ioo (-1 : ℝ) 1) ∧
      Filter.Tendsto x Filter.atTop (nhds 1) ∧
      (1 : ℝ) ∉ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨fun n => 1 - 1 / (n + 1), fun n => ?_, ?_, by simp⟩
  · have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpos : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr h1
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one h1]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    constructor
    · linarith
    · linarith
  · have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h.const_sub 1
    simpa using h2

end PNZ15

#print axioms PNZ15.lawvere_core
#print axioms PNZ15.diagonal_unification
#print axioms PNZ15.no_summit
#print axioms PNZ15.totality_not_object_russell
#print axioms PNZ15.totality_not_object_burali_forti
#print axioms PNZ15.halting_wall
#print axioms PNZ15.mu_open_witness
