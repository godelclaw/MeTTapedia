import Mettapedia.SetTheory.Surreal.Addition
import Mettapedia.SetTheory.Ordinal.NaturalSum
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Tactic.Abel

/-!
# Branching recursion over surreal birthdays

Surreal addition proves monotonicity and separation by mutual induction:
`Mono a b c` compares `a + c` and `b + c`, while `Sep x y` separates the
option families defining `x + y`. Their dependency measures are

```
tripleMeasure a b c = {birthday a, birthday b, birthday c}
pairMeasure  x y   = {birthday x, birthday y}
```

Each call replaces a nonempty collection of birthdays by younger birthdays.
In particular, `Sep x y → Mono l r y` replaces one birthday by two smaller
ones. Mathlib's Dershowitz–Manna order covers replacement, deletion, and this
split, and inherits well-foundedness from the ordinal order.

The measures certify termination rather than work counts. Maximum can stay
fixed when one component decreases; a sum of birthdays can stay fixed when
one component splits; cardinality can increase under a valid decrease.
The controls retain all three boundaries, ordinary ordinal addition's lost
strictness, and rejection of the reversed larger replacement. An encoding by
ordinal powers would require its own correspondence; none is needed here.

One context-preserving replacement lemma supplies the concrete decreases
consumed by `AdditionOrder`, `Associativity`, and `AdditionBirthday`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

open Multiset

/-- Keep the shared obligations and replace one parent by younger children. -/
private theorem replace_lt {α : Type*} [Preorder α]
    (shared children : Multiset α) (parent : α)
    (younger : ∀ child ∈ children, child < parent) :
    IsDershowitzMannaLT (shared + children) (shared + {parent}) :=
  ⟨shared, children, {parent}, by simp, rfl, rfl,
    fun child member => ⟨parent, by simp, younger child member⟩⟩

/-! ## The two measures -/

/-- The birthdays of three numbers, as a multiset. This is the measure of the
monotonicity obligation `Mono a b c`, and later of the associativity obligation
at `(x, y, z)` — both recurse by replacing one of three numbers with younger
ones, so they take the same order. -/
noncomputable def tripleMeasure (a b c : Surreal) : Multiset Ordinal.{0} :=
  {birthday a} + {birthday b} + {birthday c}

/-- The birthdays of two numbers: the measure of a separation obligation
`Sep x y`. -/
noncomputable def pairMeasure (x y : Surreal) : Multiset Ordinal.{0} :=
  {birthday x} + {birthday y}

/-! ## The five decreases -/

/-- **`Mono a b c → Mono a l c`** for `l` an option of `b`: one birthday is
replaced by a smaller one. -/
theorem tripleMeasure_lt_of_second {a b c l : Surreal}
    (h : birthday l < birthday b) :
    IsDershowitzMannaLT (tripleMeasure a l c) (tripleMeasure a b c) := by
  simpa [tripleMeasure, add_assoc, add_comm, add_left_comm] using
    replace_lt ({birthday a} + {birthday c}) {birthday l} (birthday b)
      (by simpa using h)

/-- **`Mono a b c → Mono r b c`** for `r` an option of `a`. -/
theorem tripleMeasure_lt_of_first {a b c r : Surreal}
    (h : birthday r < birthday a) :
    IsDershowitzMannaLT (tripleMeasure r b c) (tripleMeasure a b c) := by
  simpa only [tripleMeasure, add_assoc, add_comm, add_left_comm] using
    replace_lt ({birthday b} + {birthday c}) {birthday r} (birthday a)
      (by simpa using h)

/-- **Replacing the third entry by a younger number.**  Monotonicity never
touches its third argument, but associativity recurses in all three slots, so
it needs this one too. -/
theorem tripleMeasure_lt_of_third {a b c w : Surreal}
    (h : birthday w < birthday c) :
    IsDershowitzMannaLT (tripleMeasure a b w) (tripleMeasure a b c) := by
  simpa [tripleMeasure] using
    replace_lt ({birthday a} + {birthday b}) {birthday w} (birthday c)
      (by simpa using h)

/-- **`Mono a b c → Sep b c`**: a birthday is dropped, which is replacing it by
nothing at all. -/
theorem pairMeasure_lt_tripleMeasure_right (a b c : Surreal) :
    IsDershowitzMannaLT (pairMeasure b c) (tripleMeasure a b c) := by
  simpa only [tripleMeasure, pairMeasure, add_zero, zero_add, add_assoc, add_comm, add_left_comm] using
    replace_lt ({birthday b} + {birthday c}) 0 (birthday a) (by simp)

/-- **`Mono a b c → Sep a c`.** -/
theorem pairMeasure_lt_tripleMeasure_left (a b c : Surreal) :
    IsDershowitzMannaLT (pairMeasure a c) (tripleMeasure a b c) := by
  simpa [tripleMeasure, pairMeasure, add_assoc, add_comm, add_left_comm] using
    replace_lt ({birthday a} + {birthday c}) 0 (birthday b) (by simp)

/-- **`Sep x y → Mono l r y`** for `l` and `r` options of `x`: the single
birthday `bx` is replaced by the two smaller birthdays `bl` and `br`.

This split is not justified by strict monotonicity of a binary birthday sum.
The Dershowitz–Manna order needs nothing about
ordinal arithmetic — only that both options are younger than `x`. -/
theorem tripleMeasure_lt_pairMeasure {x y l r : Surreal}
    (hl : birthday l < birthday x) (hr : birthday r < birthday x) :
    IsDershowitzMannaLT (tripleMeasure l r y) (pairMeasure x y) := by
  simpa [tripleMeasure, pairMeasure, add_assoc, add_comm, add_left_comm] using
    replace_lt {birthday y} ({birthday l} + {birthday r}) (birthday x)
      (by simpa using And.intro hl hr)

/-! ## The order is well founded -/

/-- **So the induction terminates.**  Ordinals are well founded, hence so are
multisets of ordinals under this order. -/
theorem measure_wellFounded :
    WellFounded (IsDershowitzMannaLT (α := Ordinal.{0})) :=
  Multiset.wellFounded_isDershowitzMannaLT

/-! ## Option birthdays are smaller -/

theorem birthday_lt_of_mem_leftOptions {x l : Surreal} (h : l ∈ leftOptions x) :
    birthday l < birthday x := h.2

theorem birthday_lt_of_mem_rightOptions {x r : Surreal} (h : r ∈ rightOptions x) :
    birthday r < birthday x := h.2

/-- The form the induction actually calls: both options of `x`, at once. -/
theorem tripleMeasure_lt_pairMeasure_of_mem {x y l r : Surreal}
    (hl : l ∈ leftOptions x) (hr : r ∈ rightOptions x) :
    IsDershowitzMannaLT (tripleMeasure l r y) (pairMeasure x y) :=
  tripleMeasure_lt_pairMeasure hl.2 hr.2

/-! ## The second summand

A sum is symmetric, so the induction meets each shape twice — once with the
options coming from the left summand, once from the right. These are the
mirrored decreases. -/

theorem pairMeasure_comm (x y : Surreal) : pairMeasure x y = pairMeasure y x := by
  simp only [pairMeasure]; abel

/-- **`Sep x y → Mono l r x`** for `l` and `r` options of the *second*
summand. -/
theorem tripleMeasure_lt_pairMeasure_right {x y l r : Surreal}
    (hl : birthday l < birthday y) (hr : birthday r < birthday y) :
    IsDershowitzMannaLT (tripleMeasure l r x) (pairMeasure x y) := by
  rw [pairMeasure_comm]
  exact tripleMeasure_lt_pairMeasure hl hr

/-- **`Sep x y → Sep u y`** for `u` an option of `x`: the cross cases of the
separation argument recurse into a separation, not a monotonicity. -/
theorem pairMeasure_lt_pairMeasure_left {x y u : Surreal}
    (h : birthday u < birthday x) :
    IsDershowitzMannaLT (pairMeasure u y) (pairMeasure x y) := by
  simpa [pairMeasure, add_comm] using
    replace_lt {birthday y} {birthday u} (birthday x) (by simpa using h)

/-- **`Sep x y → Sep x v`** for `v` an option of `y`. -/
theorem pairMeasure_lt_pairMeasure_right {x y v : Surreal}
    (h : birthday v < birthday y) :
    IsDershowitzMannaLT (pairMeasure x v) (pairMeasure x y) := by
  simpa [pairMeasure] using
    replace_lt {birthday x} {birthday v} (birthday y) (by simpa using h)

/-! ## Controls -/

namespace AdditionMeasureControls

open Mettapedia.SetTheory.OrdinalArithmetic

/-- The maximum measure really does stall where claimed. -/
theorem max_measure_stalls : ((1 : Ordinal) ⊔ 0) = ((1 : Ordinal) ⊔ 1) := by simp

/-- And the plain natural sum of birthdays really does stall: two options born
on day `1` already reach the parent's day `2`. -/
theorem birthday_sum_stalls : ¬ (naturalAdd (1 : Ordinal.{0}) 1 < 1 + 1) :=
  NaturalSumControls.nadd_measure_fails

/-- The `Sep → Mono` step *grows* the multiset while lowering it in the order,
which is why cardinality could never have been the measure — and why an
ordinal-valued measure had to buy the property this order gives away. -/
theorem sep_to_mono_grows (x y l r : Surreal) :
    Multiset.card (tripleMeasure l r y) = Multiset.card (pairMeasure x y) + 1 := by
  simp [tripleMeasure, pairMeasure]

/-- **The order is not vacuous in the direction that matters**: one element
really can be replaced by *two* strictly smaller ones and still go down. This
is the `Sep → Mono` shape in miniature, and it is what no ordinal-valued
measure gave for free. -/
theorem two_below_one :
    IsDershowitzMannaLT ({0, 0} : Multiset Ordinal.{0}) ({1} : Multiset Ordinal.{0}) := by
  simpa using replace_lt (0 : Multiset Ordinal.{0}) {0, 0} 1 (by simp)

/-- **And it is not degenerate**: the reverse replacement, by something
*larger*, is not a decrease. Without this the order could be trivial. -/
theorem not_larger_below :
    ¬ IsDershowitzMannaLT ({1} : Multiset Ordinal.{0}) ({0, 0} : Multiset Ordinal.{0}) :=
  measure_wellFounded.asymmetric _ _ two_below_one

end AdditionMeasureControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.tripleMeasure_lt_of_second
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.tripleMeasure_lt_of_first
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.pairMeasure_lt_tripleMeasure_right
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.pairMeasure_lt_tripleMeasure_left
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.tripleMeasure_lt_pairMeasure
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.measure_wellFounded
