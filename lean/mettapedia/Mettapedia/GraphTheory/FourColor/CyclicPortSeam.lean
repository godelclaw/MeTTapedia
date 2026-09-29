import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Abel

/-!
# Cyclic alignment forced by six-step seam faces

Two oriented rows have three-step face arcs in opposite directions. If
their ports are paired and every seam face returns after six steps, the
pairing is a cyclic translation. No bound on the number of ports is used.
-/

namespace Mettapedia.GraphTheory.FourColor.CyclicPortSeam

open Fin.NatCast

variable {D : Type*} {k : ℕ} [NeZero k]
variable (face mate : Equiv.Perm D) (left right : Fin k → D)
  (seam : Fin k ≃ Fin k)
  (hinv : Function.Involutive mate)
  (hmatch : ∀ i, mate (left i) = right (seam i))
  (hout : ∀ i, (face ^ 3) (mate (left i)) = left (i - 1))
  (hin : ∀ i, (face ^ 3) (mate (right i)) = right (i + 1))

include hinv hmatch hin in
theorem three_steps_left (i : Fin k) :
    (face ^ 3) (left i) = right (seam i + 1) := by
  have hm : mate (right (seam i)) = left i := by rw [← hmatch, hinv]
  rw [← hm]
  exact hin (seam i)

include hinv hmatch hout hin in
/-- Six face steps recover the cyclic successor relation on the two rows. -/
theorem successor_of_six_steps (hright : Function.Injective right)
    (hsix : ∀ i, (face ^ 6) (left i) = left i) (i : Fin k) :
    seam (i + 1) = seam i + 1 := by
  have hfirst := three_steps_left face mate left right seam hinv hmatch hin i
  have hreturn : (face ^ 3) (right (seam i + 1)) = left i := by
    rw [← hfirst, ← Equiv.Perm.mul_apply, ← pow_add]
    exact hsix i
  have hnext : (face ^ 3) (right (seam (i + 1))) = left i := by
    rw [← hmatch, hout, add_sub_cancel_right]
  exact hright ((face ^ 3).injective (hnext.trans hreturn.symm))

/-- Commuting with the cyclic successor determines the whole permutation
from its value at one port. -/
theorem translation_of_successor (s : Fin k → Fin k)
    (hs : ∀ i, s (i + 1) = s i + 1) (i : Fin k) : s i = i + s 0 := by
  have hnat : ∀ n : ℕ, s (n : Fin k) = (n : Fin k) + s 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, hs, ih]
      abel
  simpa only [Fin.cast_val_eq_self] using hnat i.val

include hinv hmatch hout hin in
theorem translation_of_six_steps (hright : Function.Injective right)
    (hsix : ∀ i, (face ^ 6) (left i) = left i) (i : Fin k) :
    seam i = i + seam 0 :=
  translation_of_successor seam
    (successor_of_six_steps face mate left right seam hinv hmatch hout hin hright hsix) i

include hinv hmatch hout hin in
/-- Conversely, a cyclic seam gives a six-step return. Minimal face length
is a separate property of the actual embedded rows. -/
theorem six_steps_of_successor (hs : ∀ i, seam (i + 1) = seam i + 1) (i : Fin k) :
    (face ^ 6) (left i) = left i := by
  rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, Equiv.Perm.mul_apply,
    three_steps_left face mate left right seam hinv hmatch hin,
    ← hs, ← hmatch, hout, add_sub_cancel_right]

end Mettapedia.GraphTheory.FourColor.CyclicPortSeam
