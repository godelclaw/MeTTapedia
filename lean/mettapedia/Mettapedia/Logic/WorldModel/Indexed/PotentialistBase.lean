import Mettapedia.SetTheory.OpenTower.Potentialism.Modal
import Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
import Mettapedia.Logic.WorldModel.Indexed.Modalities

/-!
# The potentialist frames as bases of worlds

* The closed sets of one level, ordered by inclusion, are a base of worlds
  (`ClosedWorld`).  Each world is a universe bound, and its questions are its
  members (`memberQuestions`): an extension of the bound keeps every old
  question.
* Extension necessity on this base is the box of the potentialist forcing
  relation (`extBox_iff_forces_box`).  The base is directed and its extensions
  are comparable, so `.2` and `.3` hold (`closed_dot2`, `closed_dot3`), from the
  existing frame facts.
* **No greatest world.** Under cofinally many inaccessibles every world has a
  strict extension (`closed_no_greatest`).
* The admitted theories are a base on which directedness fails at the empty
  theory (`admitted_not_directed_at_empty`).
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.PotentialistBase

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.Potentialism
open Mettapedia.SetTheory.OpenTower.InternalTower
open Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Mettapedia.Logic.WorldModel.Indexed.Modalities
open scoped ZFSet

universe u

/-- The closed sets of one level, as worlds. -/
def ClosedWorld : Type (u + 1) := {U : ZFSet.{u} // Closed U}

/-- Extension of worlds is inclusion. -/
instance : Preorder ClosedWorld.{u} where
  le A B := A.1 ⊆ B.1
  le_refl A := closedFrame_refl A
  le_trans _ _ _ hAB hBC := closedFrame_trans hAB hBC

/-- The questions of a world are its members. -/
def memberQuestions : ClosedWorld.{u} ⥤ Type (u + 1) where
  obj A := {x : ZFSet.{u} // x ∈ A.1}
  map f := ↾(fun x => ⟨x.1, leOfHom f x.2⟩)

/-- An extension keeps every old question. -/
theorem memberQuestions_map_injective {A B : ClosedWorld.{u}} (f : A ⟶ B) :
    Function.Injective (memberQuestions.map f) := by
  intro x y h
  have same := congrArg Subtype.val h
  exact Subtype.ext same

/-- Extension necessity is the potentialist box. -/
theorem extBox_iff_forces_box (V : ℕ → ClosedWorld.{u} → Prop) (A : ClosedWorld.{u})
    (φ : Formula) :
    extBox (fun B => Forces (fun B C : ClosedWorld.{u} => B.1 ⊆ C.1) V B φ) A ↔
      Forces (fun B C : ClosedWorld.{u} => B.1 ⊆ C.1) V A (Formula.box φ) :=
  extBox_preorder_iff _ A

/-- The closed sets are directed. -/
theorem closed_directed : Directed ClosedWorld.{u} := by
  intro _ c d _ _
  obtain ⟨e, hc, hd⟩ := closedFrame_directed c d
  exact ⟨e, ⟨homOfLE hc⟩, ⟨homOfLE hd⟩⟩

/-- Extensions of a closed set are comparable. -/
theorem closed_comparable : ExtensionsComparable ClosedWorld.{u} := by
  intro _ c d _ _
  rcases closedFrame_linear c d with h | h
  · exact Or.inl ⟨homOfLE h⟩
  · exact Or.inr ⟨homOfLE h⟩

theorem closed_dot2 (P : ClosedWorld.{u} → Prop) (A : ClosedWorld.{u}) :
    extDiamond (extBox P) A → extBox (extDiamond P) A :=
  extBox_dot2 closed_directed

theorem closed_dot3 (P R : ClosedWorld.{u} → Prop) (A : ClosedWorld.{u}) :
    extBox (fun c => extBox P c → R c) A ∨ extBox (fun c => extBox R c → P c) A :=
  extBox_dot3 closed_comparable A

/-- **No greatest world.** Under cofinally many inaccessibles every closed set
has a strict closed extension. -/
theorem closed_no_greatest (cofinal : CofinalInaccessibles.{u}) (A : ClosedWorld.{u}) :
    ∃ B : ClosedWorld.{u}, A ≤ B ∧ ¬ B ≤ A := by
  obtain ⟨V, hV, mem⟩ := cofinalInaccessibles_iff_cofinal.mp cofinal A.1
  refine ⟨⟨V, hV⟩, closed_subset_of_mem hV mem, fun back => ?_⟩
  exact ZFSet.mem_irrefl A.1 (back mem)

/-- The admitted theories, as worlds. -/
def AdmittedWorld : Type := {T : Set Principle // Admitted.{u + 1} T}

instance : Preorder AdmittedWorld.{u} where
  le A B := A.1 ⊆ B.1
  le_refl A := admitted_refl A
  le_trans _ _ _ hAB hBC := admitted_trans hAB hBC

/-- The empty theory is admitted. -/
def emptyTheory : AdmittedWorld.{u} := ⟨∅, admitted_wellFounded.mono (Set.empty_subset _)⟩

/-- **The admitted theories are not directed**, already above the empty theory. -/
theorem admitted_not_directed_at_empty : ¬ Directed AdmittedWorld.{u} := by
  intro directed
  obtain ⟨e, ⟨hc⟩, ⟨hd⟩⟩ := directed emptyTheory ⟨wellFounded, admitted_wellFounded⟩
    ⟨antiFounded, admitted_antiFounded⟩ (homOfLE (Set.empty_subset _))
    (homOfLE (Set.empty_subset _))
  exact no_common_admitted_extension (leOfHom hc) (leOfHom hd) e.2

end Mettapedia.Logic.WorldModel.Indexed.PotentialistBase
