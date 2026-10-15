import Mettapedia.GSLT.Poly.BindingLanguage
import Mettapedia.GSLT.Poly.CollectionLanguage
import Mettapedia.GSLT.Poly.RhoCalcControl

/-!
# Controls for multi-binders, ordered collections, bags, and sets

A base-sort multi-binder is inside the binding fragment, and a multi-binder
whose stored type is an arrow of base sorts is outside it. An ordered `vec`
keeps permutations apart. A bag forgets order and keeps a repeated element.
A finite set forgets that repetition. For `rhoCalc`, swapping two closed
processes is one multiset, while nesting a bag and deleting `PZero` are not
permutations of bag elements.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.CollectionLanguageControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Poly.BindingLanguage
open Mettapedia.GSLT.Poly.CollectionLanguage
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

/-- A base-sort multi-binder belongs to the fragment. -/
theorem multi_binder_inside :
    bindingDecl? (.multiAbstractionNamed [] "body" (.base "A")) = some (["A"], "A") := rfl

/-- A multi-binder stored as an arrow of base sorts stays outside the fragment. -/
theorem multi_binder_outside :
    bindingDecl? (.multiAbstractionNamed [] "body" (.arrow (.base "A") (.base "B"))) = none := rfl

/-- A base-sort `vec` parameter is typed by the language's own judgment. -/
theorem vec_parameter_typed :
    HasType collectionLanguage FreeTypeContext.empty [] orderedVec (.base "A") :=
  orderedVec_typed

/-- Two permutations of one `vec` are different patterns. -/
theorem vec_permutation_distinct : orderedVec ≠ swappedVec :=
  vec_patterns_distinct

/-- Swapping the elements of a bag does not change the bag tree. -/
theorem bag_permutation_same :
    bagTree (↑([atomTree .u, atomTree .w] : List _)) =
      bagTree (↑([atomTree .w, atomTree .u] : List _)) :=
  bag_swap_same

/-- A bag keeps a repeated element. Two copies are not one copy. -/
theorem bag_keeps_duplicate :
    bagTree (↑([atomTree .u, atomTree .u] : List _)) ≠
      bagTree (↑([atomTree .u] : List _)) := by
  intro same
  have elements := bagTree_injective same
  have lengths := List.Perm.length_eq (Multiset.coe_eq_coe.mp elements)
  simp only [List.length_cons, List.length_nil] at lengths
  omega

/-- A finite set forgets a repeated element. -/
theorem set_forgets_duplicate {α : Type} (value : α) :
    finsetAbs ⟨2, fun _ => value⟩ = finsetAbs ⟨1, fun _ => value⟩ :=
  finset_forgets_duplicate value

/-- `{procDrop, procOutput}` and `{procOutput, procDrop}` are typed at `Proc`,
and `CanonicalBag` reads them as one multiset. -/
theorem parallel_swap_same :
    HasType rhoCalc FreeTypeContext.empty [] RhoCalcControl.orderedPar (.base "Proc") ∧
      HasType rhoCalc FreeTypeContext.empty [] RhoCalcControl.swappedPar (.base "Proc") ∧
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.fromProcess
            RhoCalcControl.orderedProcess =
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.fromProcess
            RhoCalcControl.swappedProcess :=
  ⟨RhoCalcControl.orderedPar_typed, RhoCalcControl.swappedPar_typed,
    RhoCalcControl.parallel_swap_same⟩

/-- A nested `rhoCalc` bag is not a permutation of the flat bag. -/
theorem nested_not_flat :
    ¬ Relation.EqvGen RhoCalcControl.RhoBagStep RhoCalcControl.nestedPar
        RhoCalcControl.orderedPar :=
  RhoCalcControl.nested_not_flat

/-- `CanonicalBag` flattens that nested bag. The permutation quotient does not. -/
theorem canonical_flattens :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.fromProcess
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.ofList
          [RhoCalcControl.orderedPar] RhoCalcControl.nestedClosed) =
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.fromProcess
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.ofList
          [RhoCalcControl.procDrop, RhoCalcControl.procOutput] RhoCalcControl.flatClosed) :=
  RhoCalcControl.canonical_flattens

/-- Deleting `PZero` from a `rhoCalc` bag is not a permutation of its elements. -/
theorem unit_not_deleted :
    ¬ Relation.EqvGen RhoCalcControl.RhoBagStep RhoCalcControl.withZero
        RhoCalcControl.onlyDrop :=
  RhoCalcControl.unit_not_deleted

/-- `CanonicalBag` deletes that unit. The permutation quotient does not. -/
theorem canonical_drops_unit :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.fromProcess
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.ofList
          [RhoCalcControl.procDrop, RhoCalcControl.procZero] RhoCalcControl.withZeroClosed) =
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.fromProcess
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag.ofList
          [RhoCalcControl.procDrop] RhoCalcControl.onlyDropClosed) :=
  RhoCalcControl.canonical_drops_unit

end Mettapedia.GSLT.Poly.CollectionLanguageControls
