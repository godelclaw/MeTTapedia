import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Order.SuccPred.CompleteLinearOrder

/-!
# The natural sum of ordinals

Ordinal addition is strictly monotone in its right argument and **not** in its
left: `0 + ω = 1 + ω`. That is fatal for any recursion whose measure must fall
when *either* of two arguments is replaced by something smaller — which is the
situation in every simultaneous induction over several ordinals at once.

The natural (Hessenberg) sum repairs exactly that. It is defined by the
recursion

```
a ⊕ b = max ( sup_{a' < a} (a' ⊕ b) + 1 , sup_{b' < b} (a ⊕ b') + 1 )
```

and strict monotonicity in each argument is immediate from the definition:
replacing an argument by a smaller one produces a term that the supremum
already dominates, with a successor to spare.

Symmetry derives the mirrored order laws. On a finite argument the operation
agrees with right ordinal addition, giving exact finite values rather than
only upper bounds. These are bounds for fixed-arity recursion: replacing one
argument by several younger arguments instead requires a multiset measure.

The suprema are legitimate because `Set.Iio a` is small, so upstream's
`Ordinal.le_iSup` and `Ordinal.iSup_le` apply.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OrdinalArithmetic

open Ordinal

universe u

/-- The natural (Hessenberg) sum: the least ordinal strictly above every
natural sum obtained by lowering one argument. -/
noncomputable def naturalAdd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | a, b =>
      max (⨆ x : Set.Iio a, naturalAdd x.1 b + 1)
        (⨆ y : Set.Iio b, naturalAdd a y.1 + 1)
termination_by a b => (a, b)
decreasing_by
  · exact Prod.Lex.left _ _ x.2
  · exact Prod.Lex.right _ y.2

theorem naturalAdd_def (a b : Ordinal.{u}) :
    naturalAdd a b =
      max (⨆ x : Set.Iio a, naturalAdd x.1 b + 1)
        (⨆ y : Set.Iio b, naturalAdd a y.1 + 1) := by
  rw [naturalAdd]

/-- Interchanging arguments interchanges the two recursive families. -/
theorem naturalAdd_comm (a b : Ordinal.{u}) : naturalAdd a b = naturalAdd b a := by
  induction a using WellFoundedLT.induction generalizing b with
  | ind a ih =>
    induction b using WellFoundedLT.induction with
    | ind b jh =>
      rw [naturalAdd_def a b, naturalAdd_def b a, max_comm]
      exact congrArg₂ max
        (congrArg iSup (funext fun x => congrArg (fun z : Ordinal => z + 1) (jh x.val x.property)))
        (congrArg iSup (funext fun y => congrArg (fun z : Ordinal => z + 1) (ih y.val y.property b)))

/-! ## Strict monotonicity, the property the recursions need -/

/-- **Lowering the left argument strictly lowers the sum.** -/
theorem naturalAdd_lt_naturalAdd_left {a a' b : Ordinal.{u}} (h : a' < a) :
    naturalAdd a' b < naturalAdd a b := by
  have hmem : naturalAdd a' b + 1 ≤ ⨆ x : Set.Iio a, naturalAdd x.1 b + 1 :=
    Ordinal.le_iSup (fun x : Set.Iio a => naturalAdd x.1 b + 1) ⟨a', h⟩
  calc naturalAdd a' b
      < naturalAdd a' b + 1 := lt_add_one _
    _ ≤ ⨆ x : Set.Iio a, naturalAdd x.1 b + 1 := hmem
    _ ≤ naturalAdd a b := by rw [naturalAdd_def a b]; exact le_max_left _ _

/-- **And lowering the right argument.** -/
theorem naturalAdd_lt_naturalAdd_right {a b b' : Ordinal.{u}} (h : b' < b) :
    naturalAdd a b' < naturalAdd a b := by
  simpa only [naturalAdd_comm a] using naturalAdd_lt_naturalAdd_left (b := a) h

theorem naturalAdd_le_naturalAdd_left {a a' b : Ordinal.{u}} (h : a' ≤ a) :
    naturalAdd a' b ≤ naturalAdd a b :=
  (show StrictMono (fun x => naturalAdd x b) from
    fun _ _ => naturalAdd_lt_naturalAdd_left).monotone h

theorem naturalAdd_le_naturalAdd_right {a b b' : Ordinal.{u}} (h : b' ≤ b) :
    naturalAdd a b' ≤ naturalAdd a b :=
  (show StrictMono (naturalAdd a) from
    fun _ _ => naturalAdd_lt_naturalAdd_right).monotone h

/-- Both at once: lowering either argument, or both, strictly lowers the sum
unless nothing moved. -/
theorem naturalAdd_lt_naturalAdd {a a' b b' : Ordinal.{u}} (ha : a' ≤ a) (hb : b' ≤ b)
    (hne : a' < a ∨ b' < b) : naturalAdd a' b' < naturalAdd a b := by
  rcases hne with h | h
  · exact (naturalAdd_lt_naturalAdd_left h).trans_le (naturalAdd_le_naturalAdd_right hb)
  · exact (naturalAdd_le_naturalAdd_left ha).trans_lt (naturalAdd_lt_naturalAdd_right h)

/-! ## The unit, and the comparison a mixed-arity measure needs -/

/-- **`0 ⊕ b = b`.**  The left supremum is over an empty family and the right
one is the supremum of successors below `b`. -/
theorem naturalAdd_zero_left (b : Ordinal.{u}) : naturalAdd 0 b = b := by
  induction b using WellFoundedLT.induction with
  | _ b ih =>
    rw [naturalAdd_def, ciSup_of_empty, max_eq_right bot_le]
    calc
      _ = ⨆ y : Set.Iio b, Order.succ y.val := by
        congr 1
        funext y
        rw [ih y.val y.property, Order.succ_eq_add_one]
      _ = b := iSup_succ b

/-- `a ⊕ 0 = a`, the mirror of `naturalAdd_zero_left`. -/
theorem naturalAdd_zero_right (a : Ordinal.{u}) : naturalAdd a 0 = a := by
  rw [naturalAdd_comm, naturalAdd_zero_left]

/-- **A summand never exceeds the natural sum.**  This is what lets a measure
over two arguments be compared with one over three. -/
theorem le_naturalAdd_left (a b : Ordinal.{u}) : b ≤ naturalAdd a b := by
  have h := naturalAdd_le_naturalAdd_left (a := a) (a' := 0) (b := b) zero_le
  rwa [naturalAdd_zero_left] at h

/-- **A positive first summand strictly increases the sum.** -/
theorem lt_naturalAdd_right {a : Ordinal.{u}} (b : Ordinal.{u}) (ha : 0 < a) :
    b < naturalAdd a b := by
  have h := naturalAdd_lt_naturalAdd_left (a := a) (a' := 0) (b := b) ha
  rwa [naturalAdd_zero_left] at h

/-- **A positive second summand strictly increases the sum.** -/
theorem lt_naturalAdd_left {b : Ordinal.{u}} (a : Ordinal.{u}) (hb : 0 < b) :
    a < naturalAdd a b := by
  have h := naturalAdd_lt_naturalAdd_right (a := a) (b := b) (b' := 0) hb
  rwa [naturalAdd_zero_right] at h

theorem le_naturalAdd_right (a b : Ordinal.{u}) : a ≤ naturalAdd a b := by
  exact (show StrictMono (fun x => naturalAdd x b) from
    fun _ _ => naturalAdd_lt_naturalAdd_left).le_apply

/-! ## Finite arguments -/

/-- A finite argument agrees with ordinary addition on the right. -/
theorem naturalAdd_natCast_right (a : Ordinal.{u}) (n : ℕ) :
    naturalAdd a (n : Ordinal) = a + n := by
  induction a using WellFoundedLT.induction generalizing n with
  | ind a ih =>
    induction n with
    | zero => simp only [Nat.cast_zero, naturalAdd_zero_right, add_zero]
    | succ n jh =>
      apply le_antisymm
      · rw [naturalAdd_def]
        refine max_le (Ordinal.iSup_le ?_) (Ordinal.iSup_le ?_)
        · rintro ⟨x, hx⟩
          rw [ih x hx]
          have hs := Order.add_one_le_of_lt
            (naturalAdd_lt_naturalAdd_left (b := (n : Ordinal)) hx)
          rw [ih x hx n, jh] at hs
          simpa only [Nat.cast_succ, add_assoc] using add_le_add hs (le_refl 1)
        · rintro ⟨y, hy⟩
          have hle : y ≤ (n : Ordinal) := by
            apply Order.lt_add_one_iff.mp
            simpa only [Nat.cast_succ] using Set.mem_Iio.mp hy
          have hs := add_le_add (naturalAdd_le_naturalAdd_right (a := a) hle) (le_refl 1)
          simpa only [jh, Nat.cast_succ, add_assoc] using hs
      · have hs := Order.add_one_le_of_lt
          (naturalAdd_lt_naturalAdd_right (a := a)
            (show (n : Ordinal) < ((n + 1 : ℕ) : Ordinal) by exact_mod_cast Nat.lt_succ_self n))
        simpa only [jh, Nat.cast_succ, add_assoc] using hs

theorem naturalAdd_natCast_left (n : ℕ) (a : Ordinal.{u}) :
    naturalAdd (n : Ordinal) a = a + n := by
  rw [naturalAdd_comm, naturalAdd_natCast_right]

/-- Exact agreement on finite ordinals. -/
theorem naturalAdd_natCast (m n : ℕ) :
    naturalAdd (m : Ordinal.{u}) (n : Ordinal) = ((m + n : ℕ) : Ordinal) := by
  rw [naturalAdd_natCast_right, Nat.cast_add]

theorem naturalAdd_one_right (a : Ordinal.{u}) : naturalAdd a 1 = a + 1 := by
  simpa using naturalAdd_natCast_right a 1

/-- **The natural sum of naturals is bounded by their sum.** -/
theorem naturalAdd_natCast_le (m n : ℕ) :
    naturalAdd ((m : ℕ) : Ordinal.{u}) ((n : ℕ) : Ordinal.{u})
      ≤ (((m + n : ℕ)) : Ordinal.{u}) :=
  (naturalAdd_natCast m n).le

/-- **So finiteness is preserved**, which is what the birthday of a dyadic
needs: a finite birthday plus a finite birthday stays below `ω`. -/
theorem naturalAdd_lt_omega0 {a b : Ordinal.{u}} (ha : a < Ordinal.omega0)
    (hb : b < Ordinal.omega0) : naturalAdd a b < Ordinal.omega0 := by
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp ha
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
  exact lt_of_le_of_lt (naturalAdd_natCast_le m n) (Ordinal.natCast_lt_omega0 _)

namespace NaturalSumControls

/-- `0 ⊕ 0 = 0`: both suprema are over empty families. -/
theorem naturalAdd_zero_zero : naturalAdd 0 0 = 0 := by
  exact naturalAdd_zero_left 0

/-- **This is exactly what ordinary ordinal addition fails to do.**  Ordinal
addition is constant in its left argument here, so it could never serve as the
measure. -/
theorem ordinal_add_not_strict_left : (0 : Ordinal) + Ordinal.omega0 = 1 + Ordinal.omega0 := by
  rw [zero_add, Ordinal.one_add_omega0]

/-- Whereas the natural sum does separate them. -/
theorem naturalAdd_strict_left_here :
    naturalAdd 0 Ordinal.omega0 < naturalAdd 1 Ordinal.omega0 :=
  naturalAdd_lt_naturalAdd_left zero_lt_one

/-- **And the natural sum of two ordinals is not enough on its own** as a
recursion measure over options: two options born on day `1` already reach the
parent's day `2`, because `1 ⊕ 1 = 2`. Branching recursion instead uses
the multiset replacement order. -/
theorem nadd_measure_fails : ¬ (naturalAdd (1 : Ordinal.{u}) 1 < 1 + 1) := by
  rw [naturalAdd_one_right]
  exact lt_irrefl _

end NaturalSumControls

end Mettapedia.SetTheory.OrdinalArithmetic

#print axioms Mettapedia.SetTheory.OrdinalArithmetic.naturalAdd_lt_naturalAdd_left
#print axioms Mettapedia.SetTheory.OrdinalArithmetic.naturalAdd_lt_naturalAdd_right
#print axioms Mettapedia.SetTheory.OrdinalArithmetic.naturalAdd_lt_naturalAdd
#print axioms Mettapedia.SetTheory.OrdinalArithmetic.NaturalSumControls.naturalAdd_strict_left_here
