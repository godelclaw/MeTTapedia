import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Logic
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Restriction-sensitive native negation controls

The atom is false at stage zero and true after restriction to stage one.
Failed current membership therefore does not prove its native negation.
An empty atom, in contrast, has a genuine negation at every stage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.LogicControls

open _root_.CategoryTheory Logic

abbrev sections : Nat ⥤ Type := (Functor.const Nat).obj PUnit.{1}

def later : Subfunctor sections where
  obj stage := fun _ => 0 < stage
  map step _ holds := Nat.lt_of_lt_of_le holds (leOfHom step)

def atoms : Unit → Subfunctor sections := fun _ => later

theorem current_atom_absent :
    ¬ Satisfaction atoms (.atom ()) 0 PUnit.unit := by
  exact Nat.lt_irrefl 0

theorem future_atom_present : Satisfaction atoms (.atom ()) 1 PUnit.unit := by
  exact Nat.zero_lt_succ 0

theorem absence_not_native_negation :
    ¬ Satisfaction atoms (Formula.atom ()).negation 0 PUnit.unit := by
  intro alleged
  exact alleged 1 (homOfLE (Nat.zero_le 1)) (Nat.zero_lt_succ 0)

theorem absence_and_negation_separate :
    (¬ Satisfaction atoms (.atom ()) 0 PUnit.unit) ∧
      (¬ Satisfaction atoms (Formula.atom ()).negation 0 PUnit.unit) :=
  ⟨current_atom_absent, absence_not_native_negation⟩

theorem empty_atom_has_negation (stage : Nat) :
    Satisfaction (fun _ : Unit => (⊥ : Subfunctor sections))
      (Formula.atom ()).negation stage PUnit.unit := by
  intro future step impossible
  exact impossible

theorem atom_not_boolean_complement :
    PUnit.unit ∉ (denote atoms (Formula.atom ()).negation).obj 0 := by
  rw [denote_iff_satisfaction]
  exact absence_not_native_negation

theorem excluded_middle_not_global :
    ¬ Satisfaction atoms (.disj (.atom ()) (Formula.atom ()).negation) 0 PUnit.unit := by
  rintro (present | negated)
  · exact current_atom_absent present
  · exact absence_not_native_negation negated

theorem implication_self_global (stage : Nat) :
    Satisfaction atoms (.impl (.atom ()) (.atom ())) stage PUnit.unit := by
  intro future step held
  exact held

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.LogicControls
