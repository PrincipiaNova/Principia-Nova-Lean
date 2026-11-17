/-
  PRINCIPIA NOVA — THE LEIBNIZ PANEL: THE COMPOSITION INHERITANCE,
  KERNEL-CERTIFIED · 11/04/2026 · Lean 4 + mathlib.

  §24's second triptych panel ("Composition — the Chain-Rule
  Inheritance"), certified at exactly its printed size. Canon's claim:

    "Wherever arenas nest — each level a reparametrization dT = τ dt of
     the level beneath it — the composed tempo factor is the product of
     the local factors. No alternative composition is expressible: rates
     compose by the chain rule, and tempo is a rate. Multiplicativity is
     therefore inherited, not chosen."

  Statement contract maps the printed sentences one to one. The
  tautology objection is OWNED exactly as canon owns it: the product
  form is the free part, and the free part is all this file claims —
  the locality clause (each factor depends only on its own arena's
  coherence) is canon's NAMED assumption and never enters these
  signatures. The fence holds at its printed size: SERIAL composition
  only; the parallel knitting of overlapping arenas is Chapter 6 §2's
  open debt and no theorem below touches it.

  THEOREMS
    nested_rates_multiply    : two nested reparametrizations compose at
                               the PRODUCT of their rates (chain rule,
                               consumed from mathlib, instantiated on
                               clocks)
    composition_rate_unique  : "no alternative composition is
                               expressible" — any certified rate for the
                               composite IS the product (derivative
                               uniqueness)
    three_level_stack        : a clock inside a well inside an epoch:
                               triple nesting composes at τ₃·τ₂·τ₁
    uniform_factors          : the integrated uniform case — linear
                               clocks T = k·t stack to k₂·k₁
    forcings_meet_in_log     : "the two forcings meet in the logarithm"
                               — a forced product, taken under ln, is a
                               sum: the Σ ln(C_i/C_floor,i) shape is the
                               only form the left-hand side could have
-/
import Mathlib

namespace PNComp

/-- **THE COMPOSITION INHERITANCE (chain rule on nested clocks):**
    if arena B's clock runs as f against A's parameter (rate τ₁ at t),
    and arena C's clock runs as g against B's (rate τ₂ at f t), the
    composed clock runs at the PRODUCT τ₂·τ₁ — multiplicativity
    inherited, not chosen. -/
theorem nested_rates_multiply (f g : ℝ → ℝ) (τ1 τ2 t : ℝ)
    (hf : HasDerivAt f τ1 t) (hg : HasDerivAt g τ2 (f t)) :
    HasDerivAt (fun s => g (f s)) (τ2 * τ1) t :=
  hg.comp t hf

/-- **"No alternative composition is expressible":** any rate the
    composite clock can be certified to run at IS τ₂·τ₁ — the product
    is forced by what a rate is, not selected among options. -/
theorem composition_rate_unique (f g : ℝ → ℝ) (τ1 τ2 r t : ℝ)
    (hf : HasDerivAt f τ1 t) (hg : HasDerivAt g τ2 (f t))
    (hr : HasDerivAt (fun s => g (f s)) r t) :
    r = τ2 * τ1 :=
  hr.unique (nested_rates_multiply f g τ1 τ2 t hf hg)

/-- **The stack:** a clock inside a well inside an epoch — three nested
    reparametrizations compose at τ₃·τ₂·τ₁. Each level contributes its
    factor; the order of the product is the order of the nesting. -/
theorem three_level_stack (f g h : ℝ → ℝ) (τ1 τ2 τ3 t : ℝ)
    (hf : HasDerivAt f τ1 t) (hg : HasDerivAt g τ2 (f t))
    (hh : HasDerivAt h τ3 (g (f t))) :
    HasDerivAt (fun s => h (g (f s))) (τ3 * (τ2 * τ1)) t :=
  (hh.comp t (hg.comp t hf) : _)

/-- The integrated uniform case: linear clocks T = k·t stack to k₂·k₁ —
    the arithmetic face of the inheritance. -/
theorem uniform_factors (k1 k2 t : ℝ) :
    HasDerivAt (fun s => k2 * (k1 * s)) (k2 * k1) t := by
  have h := ((hasDerivAt_id t).const_mul k1).const_mul k2
  simpa [mul_assoc] using h

/-- **"The two forcings meet in the logarithm":** a forced product,
    taken under ln, is a sum — the Σ ln shape of the arena sum is the
    only form the composed tempo's logarithm could have. (Consumed from
    mathlib; instantiated on positive tempo factors, as Mu guarantees.) -/
theorem forcings_meet_in_log (τ1 τ2 : ℝ) (h1 : 0 < τ1) (h2 : 0 < τ2) :
    Real.log (τ2 * τ1) = Real.log τ2 + Real.log τ1 :=
  Real.log_mul (ne_of_gt h2) (ne_of_gt h1)

end PNComp

#print axioms PNComp.nested_rates_multiply
#print axioms PNComp.composition_rate_unique
#print axioms PNComp.three_level_stack
#print axioms PNComp.uniform_factors
#print axioms PNComp.forcings_meet_in_log
