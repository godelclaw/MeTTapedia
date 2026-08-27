import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Kernel-flip involution for the PNP steelman

This file contains the finite linear-algebra core of the repaired calibration
step.  If `w` is a kernel vector of the Valiant-Vazirani matrix `A` and
`w i = 1`, then adding `w` to the witness preserves the right-hand side `b`,
is an involution on the `A x = b` fiber, and pairs the states with bit `i = 0`
with the states with bit `i = 1`.

No probability space is used here; exact neutrality is recorded as equality of
finite fiber cardinalities.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- Vectors over `F_2`, represented as `ZMod 2` coordinate functions. -/
abbrev F2Vec (n : Nat) :=
  Fin n -> ZMod 2

/-- The zero vector over `F_2`. -/
def f2ZeroVec (n : Nat) : F2Vec n :=
  fun _ => 0

/-- Pointwise vector addition over `F_2`. -/
def f2AddVec {n : Nat} (x y : F2Vec n) : F2Vec n :=
  fun i => x i + y i

/-- Matrix-vector multiplication over `F_2`, written explicitly to keep the
finite counting argument independent of any later analytic formalization. -/
def f2MatVec {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (x : F2Vec m) : F2Vec k :=
  fun r => Finset.univ.sum (fun c => A r c * x c)

/-- A vector lies in the kernel of `A`. -/
def IsKernelVector {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (w : F2Vec m) : Prop :=
  f2MatVec A w = f2ZeroVec k

/-- The affine fiber `A x = b`. -/
abbrev KernelFiber {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (b : F2Vec k) :=
  {x : F2Vec m // f2MatVec A x = b}

lemma f2_add_self (a : ZMod 2) : a + a = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by
    exact (ZMod.natCast_eq_zero_iff_even).2 ⟨1, by norm_num⟩
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 * a := by rw [htwo]
    _ = 0 := by simp

lemma f2_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  simpa using f2_add_self (1 : ZMod 2)

lemma f2_add_right_self (a b : ZMod 2) : a + b + b = a := by
  calc
    a + b + b = a + (b + b) := by ac_rfl
    _ = a := by simp [f2_add_self]

lemma f2MatVec_add {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (x w : F2Vec m) :
    f2MatVec A (f2AddVec x w) =
      f2AddVec (f2MatVec A x) (f2MatVec A w) := by
  funext r
  simp [f2MatVec, f2AddVec, Finset.sum_add_distrib, mul_add]

lemma f2AddVec_zero {n : Nat} (x : F2Vec n) :
    f2AddVec x (f2ZeroVec n) = x := by
  funext i
  simp [f2AddVec, f2ZeroVec]

/-- Add a kernel vector to a witness in the fixed `A x = b` fiber. -/
def kernelFlip {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) :
    KernelFiber A b -> KernelFiber A b :=
  fun s =>
    ⟨f2AddVec s.val w, by
      calc
        f2MatVec A (f2AddVec s.val w) =
            f2AddVec (f2MatVec A s.val) (f2MatVec A w) :=
          f2MatVec_add A s.val w
        _ = f2AddVec b (f2ZeroVec k) := by rw [s.property, hw]
        _ = b := f2AddVec_zero b⟩

@[simp] theorem kernelFlip_val {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) (s : KernelFiber A b) :
    (kernelFlip hw s).val = f2AddVec s.val w := rfl

/-- The kernel flip is an involution on the fixed `A x = b` fiber. -/
theorem kernelFlip_involutive {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) :
    Function.Involutive (kernelFlip (A := A) (b := b) hw) := by
  intro s
  apply Subtype.ext
  funext j
  exact f2_add_right_self (s.val j) (w j)

/-- The kernel flip as an explicit bijection of the affine fiber. -/
def kernelFlipEquiv {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) :
    KernelFiber A b ≃ KernelFiber A b where
  toFun := kernelFlip hw
  invFun := kernelFlip hw
  left_inv := kernelFlip_involutive hw
  right_inv := kernelFlip_involutive hw

/-- The right-hand side is fixed because the image stays in the same affine
fiber. -/
theorem kernelFlip_fixes_rhs {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w)
    (s : KernelFiber A b) :
    f2MatVec A (kernelFlip hw s).val = b :=
  (kernelFlip hw s).property

/-- Coordinate `i` is translated by `1` when `w i = 1`. -/
theorem kernelFlip_coord {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) {i : Fin m}
    (hwi : w i = 1) (s : KernelFiber A b) :
    (kernelFlip hw s).val i = s.val i + 1 := by
  simp [kernelFlip, f2AddVec, hwi]

/-- States in the affine fiber with a fixed value of witness bit `i`. -/
abbrev KernelBitFiber {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (b : F2Vec k)
    (i : Fin m) (bit : ZMod 2) :=
  {s : KernelFiber A b // s.val i = bit}

/-- The kernel flip pairs the zero and one slices of coordinate `i`. -/
def kernelFlipZeroOneEquiv {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) {i : Fin m}
    (hwi : w i = 1) :
    KernelBitFiber A b i 0 ≃ KernelBitFiber A b i 1 where
  toFun s :=
    ⟨kernelFlip hw s.val, by
      rw [kernelFlip_coord hw hwi s.val, s.property]
      norm_num⟩
  invFun s :=
    ⟨kernelFlip hw s.val, by
      rw [kernelFlip_coord hw hwi s.val, s.property]
      exact f2_one_add_one⟩
  left_inv s := by
    apply Subtype.ext
    exact kernelFlip_involutive hw s.val
  right_inv s := by
    apply Subtype.ext
    exact kernelFlip_involutive hw s.val

/-- Exact neutrality as a finite counting statement: the kernel flip gives a
cardinality-preserving pairing of the two witness-bit fibers. -/
theorem kernelFlip_exactNeutrality_card {k m : Nat}
    {A : Matrix (Fin k) (Fin m) (ZMod 2)} {b : F2Vec k}
    {w : F2Vec m} (hw : IsKernelVector A w) {i : Fin m}
    (hwi : w i = 1) :
    Fintype.card (KernelBitFiber A b i 0) =
      Fintype.card (KernelBitFiber A b i 1) :=
  Fintype.card_congr (kernelFlipZeroOneEquiv hw hwi)

/-! ## A tiny inhabited kernel-flip model -/

def toyKernelA : Matrix (Fin 1) (Fin 2) (ZMod 2) :=
  fun _ _ => 1

def toyKernelW : F2Vec 2 :=
  fun _ => 1

def toyKernelB : F2Vec 1 :=
  fun _ => 0

theorem toyKernelW_isKernel : IsKernelVector toyKernelA toyKernelW := by
  funext r
  fin_cases r
  change ((2 : Nat) : ZMod 2) = 0
  exact (ZMod.natCast_eq_zero_iff_even).2 ⟨1, by norm_num⟩

theorem toyKernelW_hits_zero : toyKernelW 0 = 1 := rfl

theorem toyKernelFlip_exactNeutrality_card :
    Fintype.card (KernelBitFiber toyKernelA toyKernelB 0 0) =
      Fintype.card (KernelBitFiber toyKernelA toyKernelB 0 1) :=
  kernelFlip_exactNeutrality_card toyKernelW_isKernel toyKernelW_hits_zero

end Mettapedia.Computability.PNP
