import Mettapedia.GSLT.LanguageDef.IndexedInductiveRecursiveSpaceControls
import Mettapedia.Logic.HOL.IndexedFamilyPredicate
import Mettapedia.TypeTheory.IndexedPolynomialDataPredicate

/-!
# Admitted-family controls for the recursive-space HOL least predicate

The admitted Natural, Vector and registered SearchTree examples instantiate
the actual shape, index and padding guards. Membership is established for
nonempty values. Hidden padding, absent payloads, wrong tags and wrong vector
indices are refused. These are semantic controls of the HOL predicate syntax;
native source definitions and executable representation codecs remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursivePredicateControls

open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.RecursiveSpaceRepresentation
open IndexedInductiveNatVec RecursiveSpaceControls
open Mettapedia.Logic.HOL

theorem natural_member :
    IndexedFamilyPredicate.member naturalPresentation PUnit.unit
      (naturalRepresentation naturalTwo).val :=
  (IndexedFamilyPredicate.member_iff_familyValid _ _ _).mpr ⟨(), natural_image_valid⟩

theorem natural_not_bottom_by_induction :
    (naturalRepresentation naturalTwo).val ≠ RecursiveSpace.bottom :=
  familyValid_induction naturalPresentation PUnit.unit
    (fun tree => tree ≠ RecursiveSpace.bottom)
    (fun _ _ _ _ => RecursiveSpace.construct_ne_bottom _ _ _)
    (naturalRepresentation naturalTwo).val ⟨(), natural_image_valid⟩

theorem vector_member_with_index :
    IndexedFamilyPredicate.member vectorPresentation PUnit.unit
      (vectorRepresentation vectorTwo).val ∧
      HasRootIndex vectorPresentation (vectorRepresentation vectorTwo).val
        (Natural.succ (Natural.succ Natural.zero)) :=
  (IndexedFamilyPredicate.indexed_member_iff _ _ _ _).mpr vector_image_valid

theorem registered_search_member :
    IndexedFamilyPredicate.member Registered.presentation
      PositiveInductiveScenarios.Search.environment
      (Registered.representation Registered.sample).val :=
  (IndexedFamilyPredicate.member_iff_familyValid _ _ _).mpr
    ⟨(), (Registered.representation Registered.sample).property⟩

theorem hidden_tail_not_member :
    ¬ IndexedFamilyPredicate.member naturalPresentation PUnit.unit
      (toRecursiveSpace naturalPresentation HOLFacts.RawPredicateInterpretation.Controls.hiddenTailSuccessor) := by
  intro present
  obtain ⟨index, valid⟩ := (IndexedFamilyPredicate.member_iff_familyValid _ _ _).mp present
  cases index
  exact RecursiveSpaceControls.hidden_tail_refused valid

theorem missing_payload_not_member :
    ¬ IndexedFamilyPredicate.member naturalPresentation PUnit.unit
      (RecursiveSpace.construct 1 (none : naturalPayload) (fun _ => RecursiveSpace.bottom)) := by
  intro present
  obtain ⟨_, encoded, _⟩ := (IndexedFamilyPredicate.member_iff_familyValid _ _ _).mp present
  exact RecursiveSpaceControls.missing_payload_refused encoded

theorem wrong_tag_not_member :
    ¬ IndexedFamilyPredicate.member naturalPresentation PUnit.unit
      (RecursiveSpace.construct 7
        (some ⟨(), HOLFacts.RawPredicateInterpretation.Controls.zeroShape⟩)
        (fun _ => RecursiveSpace.bottom)) := by
  intro present
  obtain ⟨_, encoded, _⟩ := (IndexedFamilyPredicate.member_iff_familyValid _ _ _).mp present
  exact RecursiveSpaceControls.wrong_tag_refused encoded

theorem bottom_not_member :
    ¬ IndexedFamilyPredicate.member naturalPresentation PUnit.unit RecursiveSpace.bottom := by
  intro present
  obtain ⟨index, valid⟩ := (IndexedFamilyPredicate.member_iff_familyValid _ _ _).mp present
  exact recursiveValid_bottom_refused naturalPresentation PUnit.unit index valid

theorem vector_wrong_index_refused :
    ¬ (IndexedFamilyPredicate.member vectorPresentation PUnit.unit
        (vectorRepresentation vectorTwo).val ∧
      HasRootIndex vectorPresentation (vectorRepresentation vectorTwo).val Natural.zero) := by
  intro present
  have wrong := (IndexedFamilyPredicate.indexed_member_iff _ _ _ _).mp present
  have impossible := recursiveValid_index_unique vectorPresentation _ _ _ vector_image_valid wrong
  have counts := congrArg Natural.toNat impossible
  change (2 : Nat) = 0 at counts
  cases counts

namespace DataGuards

open IndexedPolynomial.Description
open DataRepresentation HOLFacts.RawPredicateInterpretation.Controls

theorem natural_tag_agreement :
    shapeGuard naturalPresentation 1 (some ⟨(), succShape⟩) ↔
      dataShapeGuard Natural.constructors 1
        (payloadEquivalence Natural.constructors PUnit.unit (some ⟨(), succShape⟩)) :=
  shapeGuard_data Natural.constructors PUnit.unit 1 _

theorem natural_slot_agreement :
    activeGuard naturalPresentation (some ⟨(), succShape⟩) 0 ↔
      dataActiveGuard Natural.constructors
        (payloadEquivalence Natural.constructors PUnit.unit (some ⟨(), succShape⟩)) 0 :=
  activeGuard_data Natural.constructors PUnit.unit _ 0

theorem natural_child_index :
    dataChildIndex Natural.constructors PUnit.unit
      (payloadEquivalence Natural.constructors PUnit.unit (some ⟨(), succShape⟩)) 0 = some () :=
  dataChildIndex_decoded Natural.constructors PUnit.unit ⟨(), succShape⟩ 0 none rfl

theorem natural_inactive_slot_refused :
    dataChildIndex Natural.constructors PUnit.unit
      (payloadEquivalence Natural.constructors PUnit.unit (some ⟨(), succShape⟩)) 1 = none := rfl

noncomputable def vectorData : InventoryData (Vectors.constructors Bool) := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  exact (Natural.succ Natural.zero, true, PUnit.unit)

noncomputable def vectorPoint :=
  (inventoryDataEquiv (Vectors.constructors Bool) PUnit.unit).symm vectorData

theorem vector_child_index :
    dataChildIndex (Vectors.constructors Bool) PUnit.unit (some vectorData) 0 =
      some (Natural.succ Natural.zero) := rfl

theorem vector_edge_guard_agreement :
    edgeGuard vectorPresentation (some vectorPoint) 0 (vectorRepresentation vectorTwo).val ↔
      ∃ index, dataChildIndex (Vectors.constructors Bool) PUnit.unit
        (payloadEquivalence (Vectors.constructors Bool) PUnit.unit (some vectorPoint)) 0 = some index ∧
        HasRootIndex vectorPresentation (vectorRepresentation vectorTwo).val index :=
  edgeGuard_data (Vectors.constructors Bool) PUnit.unit _ 0 _

theorem vector_wrong_child_index_refused :
    ¬ edgeGuard vectorPresentation (some vectorPoint) 0 (vectorRepresentation vectorTwo).val := by
  intro present
  obtain ⟨index, computed, root⟩ := vector_edge_guard_agreement.mp present
  change some (Natural.succ Natural.zero) = some index at computed
  have same := Option.some.inj computed
  rw [← same] at root
  have wrong := (recursiveValid_iff_family_and_root vectorPresentation _ _).mpr
    ⟨⟨_, vector_image_valid⟩, root⟩
  have impossible := recursiveValid_index_unique vectorPresentation _ _ _ vector_image_valid wrong
  have counts := congrArg Natural.toNat impossible
  change (2 : Nat) = 1 at counts
  cases counts

end DataGuards

#print axioms natural_member
#print axioms vector_member_with_index
#print axioms registered_search_member
#print axioms hidden_tail_not_member
#print axioms wrong_tag_not_member
#print axioms vector_wrong_index_refused
#print axioms DataGuards.natural_child_index
#print axioms DataGuards.vector_wrong_child_index_refused

end Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursivePredicateControls
