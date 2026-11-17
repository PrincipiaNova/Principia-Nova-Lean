/-
  PRINCIPIA NOVA — Z-N.2 TIER 1: FIELD STAGE, KERNEL-CHECKED ALGEBRA
  11/02/2026 · Lean 4.21.0 core, NO mathlib — every axiom stated below.

  THE MODEL (N-2, canon): 1+1 field theory with position-dependent lapse,
  L = φ_t²/(2N) − N·φ_x²/2 − N·V(φ). Two abstract derivations Dt, Dx
  (∂_t and ∂_x), each additive + Leibniz; mixed partials agree on φ
  (hmix). Elements: pt = ∂_t φ, px = ∂_x φ, n = N, V = V(φ), V' = V′(φ).

  Cleared quantities (no division; ring, not field):
    R = pt² + n²·px² + 2n²·V      ( = 2N·ρ_E, cleared energy density )
    g = n·px·pt                   ( = −f, the energy flux, sign moved )

  Hypotheses, named in the statements:
    hVt  : Dt V = V'·pt           (chain rule, time; the spatial chain rule
                                   turned out to be UNNECESSARY — removed)
    hmix : Dt px = Dx pt          (mixed partials of φ agree)
    hEL  : n·Dt pt + n³·V' = pt·Dt n + n²·Dx n·px + n³·Dx px
           (Euler–Lagrange equation of L, denominators cleared, moved form)

  THEOREM sourced_continuity :  n·Dt R = 2·(Dt n)·R + 2n²·Dx g
    — the cleared form of  ∂_t ρ_E + ∂_x f = (∂_t N)·ρ_s  with ρ_s = ρ_E/N:
    the flux term intact (the First PN Law, certified), the source purely
    local and proportional to the TIME variation of the clock.

  THEOREM arena_obstruction :  N·C constant in x  ⟹  (Dx n)·c + n·(Dx c) = 0

  THEOREM obstruction_iff (THE IRREMOVABILITY CORE) :
      Dx n = 0  ⟺  Dx c = 0
    — the clock can be flattened exactly where the spatial coherence
    gradient vanishes. The obstruction to any global re-clocking IS ∇C —
    what Chapter 5 names gravity. (Stage-three usage: the theorem itself
    never needs the word.)

  COROLLARY flat_patch : Dt n = 0 ⟹ n·Dt R = 2n²·Dx g
    — where the clock is steady in time, the ledger is pure flux exchange.
-/

namespace PN

/-- A commutative algebra with TWO derivations: the minimal arena for the
    1+1 field stage. Eleven axioms, nothing else. -/
structure FieldAlgebra (R : Type) : Type where
  add  : R → R → R
  mul  : R → R → R
  zero : R
  add_assoc    : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm     : ∀ a b : R, add a b = add b a
  add_zero     : ∀ a : R, add a zero = a
  mul_assoc    : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm     : ∀ a b : R, mul a b = mul b a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  zero_mul     : ∀ a : R, mul zero a = zero
  /-- Time derivation: abstract ∂_t. -/
  Dt     : R → R
  Dt_add : ∀ a b : R, Dt (add a b) = add (Dt a) (Dt b)
  Dt_mul : ∀ a b : R, Dt (mul a b) = add (mul (Dt a) b) (mul a (Dt b))
  /-- Space derivation: abstract ∂_x. -/
  Dx     : R → R
  Dx_add : ∀ a b : R, Dx (add a b) = add (Dx a) (Dx b)
  Dx_mul : ∀ a b : R, Dx (mul a b) = add (mul (Dx a) b) (mul a (Dx b))

namespace FieldAlgebra

variable {R : Type} (A : FieldAlgebra R)

local infixl:65 " ⊹ " => A.add
local infixl:70 " ⬝ " => A.mul
local prefix:100 "∂t" => A.Dt
local prefix:100 "∂x" => A.Dx

theorem add_left_comm (a b c : R) : a ⊹ (b ⊹ c) = b ⊹ (a ⊹ c) := by
  rw [← A.add_assoc, A.add_comm a b, A.add_assoc]

theorem mul_left_comm (a b c : R) : a ⬝ (b ⬝ c) = b ⬝ (a ⬝ c) := by
  rw [← A.mul_assoc, A.mul_comm a b, A.mul_assoc]

theorem right_distrib (a b c : R) : (a ⊹ b) ⬝ c = a ⬝ c ⊹ b ⬝ c := by
  rw [A.mul_comm, A.left_distrib, A.mul_comm c a, A.mul_comm c b]

theorem mul_zero (a : R) : a ⬝ A.zero = A.zero := by
  rw [A.mul_comm, A.zero_mul]

theorem zero_add (a : R) : A.zero ⊹ a = a := by
  rw [A.add_comm, A.add_zero]

set_option maxHeartbeats 16000000 in
/-- **Z-N.2 SOURCED CONTINUITY (kernel-checked, cleared form).**
    From the field EL equation, both chain rules, and the symmetry of
    mixed partials alone:  n·∂tR = 2·(∂tn)·R + 2n²·∂xg.
    The flux is intact; the source is the time variation of the clock. -/
theorem sourced_continuity
    (pt px n V V' : R)
    (hVt : ∂t V = V' ⬝ pt)
    (hmix : ∂t px = ∂x pt)
    (hEL : n ⬝ ∂t pt ⊹ n ⬝ n ⬝ n ⬝ V'
         = pt ⬝ ∂t n ⊹ (n ⬝ n ⬝ (∂x n ⬝ px) ⊹ n ⬝ n ⬝ n ⬝ ∂x px))
    (Rr g : R)
    (hR : Rr = pt ⬝ pt ⊹ (n ⬝ n ⬝ (px ⬝ px) ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V)))
    (hg : g = n ⬝ (px ⬝ pt)) :
    n ⬝ ∂t Rr = (∂t n ⬝ Rr ⊹ ∂t n ⬝ Rr) ⊹ (n ⬝ n ⬝ ∂x g ⊹ n ⬝ n ⬝ ∂x g) := by
  subst hR hg
  calc
    n ⬝ ∂t (pt ⬝ pt ⊹ (n ⬝ n ⬝ (px ⬝ px) ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V)))
        = pt ⬝ (n ⬝ ∂t pt ⊹ n ⬝ n ⬝ n ⬝ V') ⊹ pt ⬝ (n ⬝ ∂t pt ⊹ n ⬝ n ⬝ n ⬝ V')
          ⊹ (n ⬝ n ⬝ ∂t n ⬝ (px ⬝ px) ⊹ n ⬝ n ⬝ ∂t n ⬝ (px ⬝ px))
          ⊹ (n ⬝ n ⬝ ∂t n ⬝ V ⊹ n ⬝ n ⬝ ∂t n ⬝ V
             ⊹ (n ⬝ n ⬝ ∂t n ⬝ V ⊹ n ⬝ n ⬝ ∂t n ⬝ V))
          ⊹ (n ⬝ n ⬝ n ⬝ (px ⬝ ∂t px) ⊹ n ⬝ n ⬝ n ⬝ (px ⬝ ∂t px)) := by
      simp [A.Dt_add, A.Dt_mul, hVt, A.left_distrib, A.right_distrib,
            A.add_assoc, A.add_comm, A.add_left_comm,
            A.mul_assoc, A.mul_comm, A.mul_left_comm]
    _ = pt ⬝ (pt ⬝ ∂t n ⊹ (n ⬝ n ⬝ (∂x n ⬝ px) ⊹ n ⬝ n ⬝ n ⬝ ∂x px))
          ⊹ pt ⬝ (pt ⬝ ∂t n ⊹ (n ⬝ n ⬝ (∂x n ⬝ px) ⊹ n ⬝ n ⬝ n ⬝ ∂x px))
          ⊹ (n ⬝ n ⬝ ∂t n ⬝ (px ⬝ px) ⊹ n ⬝ n ⬝ ∂t n ⬝ (px ⬝ px))
          ⊹ (n ⬝ n ⬝ ∂t n ⬝ V ⊹ n ⬝ n ⬝ ∂t n ⬝ V
             ⊹ (n ⬝ n ⬝ ∂t n ⬝ V ⊹ n ⬝ n ⬝ ∂t n ⬝ V))
          ⊹ (n ⬝ n ⬝ n ⬝ (px ⬝ ∂x pt) ⊹ n ⬝ n ⬝ n ⬝ (px ⬝ ∂x pt)) := by
      rw [hEL, hmix]
    _ = (∂t n ⬝ (pt ⬝ pt ⊹ (n ⬝ n ⬝ (px ⬝ px) ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V)))
          ⊹ ∂t n ⬝ (pt ⬝ pt ⊹ (n ⬝ n ⬝ (px ⬝ px) ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V))))
          ⊹ (n ⬝ n ⬝ ∂x (n ⬝ (px ⬝ pt)) ⊹ n ⬝ n ⬝ ∂x (n ⬝ (px ⬝ pt))) := by
      have hDxg : ∂x (n ⬝ (px ⬝ pt))
          = ∂x n ⬝ (px ⬝ pt) ⊹ n ⬝ (∂x px ⬝ pt ⊹ px ⬝ ∂x pt) := by
        rw [A.Dx_mul, A.Dx_mul]
      rw [hDxg]
      simp [A.left_distrib, A.right_distrib,
            A.add_assoc, A.add_comm, A.add_left_comm,
            A.mul_assoc, A.mul_comm, A.mul_left_comm]

/-- **The arena law kills the x-freedom of the clock:** N·C constant in x
    forces (∂x n)·c + n·(∂x c) = 0. -/
theorem arena_obstruction
    (n c k : R) (hk : n ⬝ c = k) (hkx : ∂x k = A.zero) :
    ∂x n ⬝ c ⊹ n ⬝ ∂x c = A.zero := by
  rw [← A.Dx_mul, hk, hkx]

/-- **Z-N.2 IRREMOVABILITY CORE (kernel-checked).**
    Under the arena law, the clock's spatial variation vanishes exactly
    where the coherence gradient does:  ∂x n = 0  ⟺  ∂x c = 0.
    The obstruction to flattening the clock IS the spatial coherence
    gradient — the object Chapter 5 names gravity. -/
theorem obstruction_iff
    (n c k : R) (hk : n ⬝ c = k) (hkx : ∂x k = A.zero)
    (hcancN : ∀ a : R, n ⬝ a = A.zero → a = A.zero)
    (hcancC : ∀ a : R, c ⬝ a = A.zero → a = A.zero) :
    ∂x n = A.zero ↔ ∂x c = A.zero := by
  have hobs := A.arena_obstruction n c k hk hkx
  constructor
  · intro h
    rw [h, A.zero_mul, A.zero_add] at hobs
    exact hcancN _ hobs
  · intro h
    rw [h, A.mul_zero, A.add_zero] at hobs
    rw [A.mul_comm] at hobs
    exact hcancC _ hobs

set_option maxHeartbeats 1000000 in
/-- **Corollary: the flat-in-time patch.** Where ∂t n = 0, the continuity
    law is pure flux — local exchange balances exactly (First PN Law). -/
theorem flat_patch
    (pt px n V V' : R)
    (hVt : ∂t V = V' ⬝ pt)
    (hmix : ∂t px = ∂x pt)
    (hEL : n ⬝ ∂t pt ⊹ n ⬝ n ⬝ n ⬝ V'
         = pt ⬝ ∂t n ⊹ (n ⬝ n ⬝ (∂x n ⬝ px) ⊹ n ⬝ n ⬝ n ⬝ ∂x px))
    (Rr g : R)
    (hR : Rr = pt ⬝ pt ⊹ (n ⬝ n ⬝ (px ⬝ px) ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V)))
    (hg : g = n ⬝ (px ⬝ pt))
    (hflat : ∂t n = A.zero) :
    n ⬝ ∂t Rr = n ⬝ n ⬝ ∂x g ⊹ n ⬝ n ⬝ ∂x g := by
  have h := A.sourced_continuity pt px n V V' hVt hmix hEL Rr g hR hg
  rw [hflat, A.zero_mul, A.add_zero, A.zero_add] at h
  exact h

end FieldAlgebra

end PN

#print axioms PN.FieldAlgebra.sourced_continuity
#print axioms PN.FieldAlgebra.arena_obstruction
#print axioms PN.FieldAlgebra.obstruction_iff
#print axioms PN.FieldAlgebra.flat_patch
