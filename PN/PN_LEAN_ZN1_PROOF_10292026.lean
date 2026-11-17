/-
  PRINCIPIA NOVA — Z-N.1 DRIFT LAW: KERNEL-CHECKED ALGEBRAIC SKELETON
  10/29/2026 · Lean 4.21.0 core, NO mathlib — every axiom used is stated
  in the structure below, visible to the kernel.

  WHAT IS PROVED
  --------------
  Setting: an arbitrary commutative algebra R with a derivation ∂
  (additivity + Leibniz rule) — the abstract skeleton of "functions of
  time, with d/dt". Elements:
    v  = q̇ (velocity),  n = N (the lapse / clock rate τ_coh),
    V  = V(q) (potential along the trajectory),  V' = V'(q).
  To avoid division (we work in a ring, not a field), the energy is
  carried in denominator-cleared form:
    F := v² + 2n²V   ( = 2N·E_t , twice-lapse-times-energy ).

  Hypotheses, each named in the theorem statement:
    hChain : ∂V = V'·v                     (chain rule along the trajectory)
    hEL    : n·∂v + n³·V' = v·∂n            (Euler–Lagrange eq. of
             L = q̇²/(2N) − N·V, cleared of denominators, moved form)

  THEOREM drift_law :  n·∂F = 2·(∂n)·F
    — the denominator-cleared form of  dE_t/dt = (Ṅ/N)·E_t.
    (Divide by 2n² to recover it:  the same identity is ALSO the
     statement ∂(F/n²) = 0, i.e. substrate-time energy E_s = E_t/N
     is exactly conserved — one identity, both ledgers.)

  COROLLARY flat_clock :  ∂n = 0  →  n·∂F = 0
    — conservation is exact where the clock is flat.

  COROLLARY arena_law :  given  (∂n)·C + n·Ċ = 0   (the arena law
    N·C = C_floor, differentiated), it follows that
      n·( C·∂F + 2·Ċ·F ) = 0
    — the N-1 canon form  dE/dt = [(D_loss − G)/C]·E  cleared of
    fractions, with Ċ ↦ G − D_loss by the Generative Law.

  SCOPE, STATED PLAINLY
  ---------------------
  This certifies the ALGEBRA of Z-N.1: that the drift law follows from
  the Leibniz/chain rules and the EL equation by pure symbol pushing,
  with no sign error and no hidden step. It does not certify the
  analysis (that d/dt on smooth functions IS a derivation — textbook),
  nor the variational derivation of the EL equation itself (taken as
  hypothesis, exactly as the sympy scripts take it on-shell). Those
  layers belong to the mathlib-grade formalization (Tier 2).
-/

namespace PN

/-- A commutative algebra with derivation: the minimal arena in which
    the drift law can be stated. Nine axioms, nothing else. -/
structure ClockAlgebra (R : Type) : Type where
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
  /-- The derivation: abstract d/dt. -/
  D     : R → R
  D_add : ∀ a b : R, D (add a b) = add (D a) (D b)
  D_mul : ∀ a b : R, D (mul a b) = add (mul (D a) b) (mul a (D b))

namespace ClockAlgebra

variable {R : Type} (A : ClockAlgebra R)

local infixl:65 " ⊹ " => A.add
local infixl:70 " ⬝ " => A.mul
local prefix:100 "∂" => A.D

/- Derived helpers (proved, not assumed). -/

theorem add_left_comm (a b c : R) : a ⊹ (b ⊹ c) = b ⊹ (a ⊹ c) := by
  rw [← A.add_assoc, A.add_comm a b, A.add_assoc]

theorem mul_left_comm (a b c : R) : a ⬝ (b ⬝ c) = b ⬝ (a ⬝ c) := by
  rw [← A.mul_assoc, A.mul_comm a b, A.mul_assoc]

theorem right_distrib (a b c : R) : (a ⊹ b) ⬝ c = a ⬝ c ⊹ b ⬝ c := by
  rw [A.mul_comm, A.left_distrib, A.mul_comm c a, A.mul_comm c b]

theorem mul_zero (a : R) : a ⬝ A.zero = A.zero := by
  rw [A.mul_comm, A.zero_mul]

/-- **Z-N.1 DRIFT LAW (kernel-checked).**
    From the chain rule and the Euler–Lagrange equation of
    L = q̇²/(2N) − N·V alone:  n·∂F = 2·(∂n)·F,
    the cleared form of dE_t/dt = (Ṅ/N)·E_t. -/
theorem drift_law
    (v n V V' : R)
    (hChain : ∂V = V' ⬝ v)
    (hEL : n ⬝ ∂v ⊹ n ⬝ n ⬝ n ⬝ V' = v ⬝ ∂n)
    (F : R) (hF : F = v ⬝ v ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V)) :
    n ⬝ ∂F = ∂n ⬝ F ⊹ ∂n ⬝ F := by
  subst hF
  calc
    n ⬝ ∂(v ⬝ v ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V))
        = v ⬝ (n ⬝ ∂v ⊹ n ⬝ n ⬝ n ⬝ V') ⊹ v ⬝ (n ⬝ ∂v ⊹ n ⬝ n ⬝ n ⬝ V')
          ⊹ (∂n ⬝ (n ⬝ n ⬝ V) ⊹ ∂n ⬝ (n ⬝ n ⬝ V)
             ⊹ (∂n ⬝ (n ⬝ n ⬝ V) ⊹ ∂n ⬝ (n ⬝ n ⬝ V))) := by
      simp [A.D_add, A.D_mul, hChain, A.left_distrib, A.right_distrib,
            A.add_assoc, A.add_comm, A.add_left_comm,
            A.mul_assoc, A.mul_comm, A.mul_left_comm]
    _ = v ⬝ (v ⬝ ∂n) ⊹ v ⬝ (v ⬝ ∂n)
          ⊹ (∂n ⬝ (n ⬝ n ⬝ V) ⊹ ∂n ⬝ (n ⬝ n ⬝ V)
             ⊹ (∂n ⬝ (n ⬝ n ⬝ V) ⊹ ∂n ⬝ (n ⬝ n ⬝ V))) := by
      rw [hEL]
    _ = ∂n ⬝ (v ⬝ v ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V))
          ⊹ ∂n ⬝ (v ⬝ v ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V)) := by
      simp [A.left_distrib, A.right_distrib,
            A.add_assoc, A.add_comm, A.add_left_comm,
            A.mul_assoc, A.mul_comm, A.mul_left_comm]

/-- **Corollary: flat clock ⇒ exact conservation.**
    Where the clock does not vary, the ledger closes exactly. -/
theorem flat_clock
    (v n V V' : R)
    (hChain : ∂V = V' ⬝ v)
    (hEL : n ⬝ ∂v ⊹ n ⬝ n ⬝ n ⬝ V' = v ⬝ ∂n)
    (F : R) (hF : F = v ⬝ v ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V))
    (hflat : ∂n = A.zero) :
    n ⬝ ∂F = A.zero := by
  rw [A.drift_law v n V V' hChain hEL F hF, hflat, A.zero_mul, A.add_zero]

/-- **Corollary: the arena-law form.**
    With the arena law N·C = C_floor differentiated — (∂n)·C + n·Ċ = 0 —
    the drift law becomes  n·(C·∂F + 2·Ċ·F) = 0 :
    the cleared form of  dE/dt = [(D_loss − G)/C]·E,  with Ċ ↦ G − D_loss. -/
theorem arena_law
    (v n V V' : R)
    (hChain : ∂V = V' ⬝ v)
    (hEL : n ⬝ ∂v ⊹ n ⬝ n ⬝ n ⬝ V' = v ⬝ ∂n)
    (F : R) (hF : F = v ⬝ v ⊹ (n ⬝ n ⬝ V ⊹ n ⬝ n ⬝ V))
    (C Cdot : R)
    (hclock : ∂n ⬝ C ⊹ n ⬝ Cdot = A.zero) :
    n ⬝ (C ⬝ ∂F ⊹ (Cdot ⬝ F ⊹ Cdot ⬝ F)) = A.zero := by
  have h := A.drift_law v n V V' hChain hEL F hF
  calc
    n ⬝ (C ⬝ ∂F ⊹ (Cdot ⬝ F ⊹ Cdot ⬝ F))
        = C ⬝ (n ⬝ ∂F) ⊹ (n ⬝ Cdot ⬝ F ⊹ n ⬝ Cdot ⬝ F) := by
      simp [A.left_distrib, A.right_distrib,
            A.add_assoc, A.add_comm, A.add_left_comm,
            A.mul_assoc, A.mul_comm, A.mul_left_comm]
    _ = C ⬝ (∂n ⬝ F ⊹ ∂n ⬝ F) ⊹ (n ⬝ Cdot ⬝ F ⊹ n ⬝ Cdot ⬝ F) := by
      rw [h]
    _ = (∂n ⬝ C ⊹ n ⬝ Cdot) ⬝ F ⊹ (∂n ⬝ C ⊹ n ⬝ Cdot) ⬝ F := by
      simp [A.left_distrib, A.right_distrib,
            A.add_assoc, A.add_comm, A.add_left_comm,
            A.mul_assoc, A.mul_comm, A.mul_left_comm]
    _ = A.zero ⬝ F ⊹ A.zero ⬝ F := by rw [hclock]
    _ = A.zero := by rw [A.zero_mul, A.add_zero]

end ClockAlgebra

/-- Consistency witness: the axioms are satisfiable (ℤ with the zero
    derivation), so the theorems above are not vacuously true. -/
def intClock : ClockAlgebra Int where
  add := (· + ·)
  mul := (· * ·)
  zero := 0
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_zero := Int.add_zero
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add
  zero_mul := Int.zero_mul
  D := fun _ => 0
  D_add := by intro a b; simp
  D_mul := by intro a b; simp

end PN

-- Axiom audit: what does the proof ultimately rest on?
#print axioms PN.ClockAlgebra.drift_law
#print axioms PN.ClockAlgebra.flat_clock
#print axioms PN.ClockAlgebra.arena_law
