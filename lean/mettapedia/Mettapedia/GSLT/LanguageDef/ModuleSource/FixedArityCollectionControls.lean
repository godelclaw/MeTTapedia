import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtraction
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold

/-! # Fixed-arity set equations do not authorize variadic flattening

This set-valued interpretation satisfies singleton elimination and the
binary-to-ternary flattening equation. Its four-element interpretation is
independent. Thus even set idempotence plus those two source equations does
not justify replacing all nested sums by a flat set.
-/

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.FixedArityCollectionControls

def sum (elements : Finset Nat) : Nat :=
  if elements.card ≤ 3 then elements.sup id else 0

@[simp] theorem singleton (x : Nat) : sum {x} = x := by
  simp [sum]

@[simp] theorem pair (x y : Nat) : sum {x, y} = max x y := by
  have small : ({x, y} : Finset Nat).card ≤ 3 := Finset.card_le_two.trans (by decide)
  simp [sum, small]

@[simp] theorem triple (x y z : Nat) : sum {x, y, z} = max x (max y z) := by
  simp [sum, Finset.card_le_three]

theorem authored_three_element_flattening (x y z : Nat) :
    sum {sum {x, y}, z} = sum {x, y, z} := by
  simp [max_assoc]

theorem repeated_element (x y : Nat) : sum {x, x, y} = sum {x, y} := by simp

theorem variadic_flattening_fails :
    sum {sum {1, 2}, 3, 4} ≠ sum {1, 2, 3, 4} := by decide

end Mettapedia.GSLT.LanguageDef.ModuleSource.FixedArityCollectionControls
