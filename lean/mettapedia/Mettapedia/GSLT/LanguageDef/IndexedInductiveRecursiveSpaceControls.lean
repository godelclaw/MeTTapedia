import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpaceRepresentation
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace
import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLoweringControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLPredicate
import Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

/-!
# Recursive-space controls for admitted Natural and Vector families

The original admitted families instantiate the semantic comparison. The controls
retain unknown raw child maps, reject hidden padding and malformed tags, and
round-trip an indexed two-element vector. Native certificate interpretation and
executable adapters retain their separate qualification obligations.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursiveSpaceControls
open Mettapedia.TypeTheory
open IndexedPolynomial
open Description RecursiveSpaceRepresentation
open IndexedInductiveNatVec
open HOLFacts.RawPredicateInterpretation.Controls

abbrev naturalPresentation := recursiveSpacePresentation Natural.constructors
noncomputable abbrev vectorPresentation := recursiveSpacePresentation (Vectors.constructors Bool)
abbrev naturalPayload := RecursivePayload naturalPresentation PUnit.unit
noncomputable def naturalTwo := Natural.succ (Natural.succ Natural.zero)

noncomputable def naturalRepresentation := recursiveSpaceRepresentation naturalPresentation PUnit.unit ()

theorem natural_roundtrip : naturalRepresentation.symm (naturalRepresentation naturalTwo) = naturalTwo :=
  naturalRepresentation.symm_apply_apply naturalTwo

theorem natural_image_valid : RecursiveValid naturalPresentation (naturalRepresentation naturalTwo).val () :=
  (naturalRepresentation naturalTwo).property

theorem hidden_tail_refused :
    ¬ RecursiveValid naturalPresentation (toRecursiveSpace naturalPresentation hiddenTailSuccessor) () := by
  intro present
  exact HOLFacts.RawPredicateInterpretation.Controls.hidden_tail_refused
    ((recursiveValid_toRecursiveSpace_iff naturalPresentation hiddenTailSuccessor ()).mp present)

theorem wrong_tag_refused :
    ¬ RecursiveEncoded naturalPresentation
      (RecursiveSpace.construct 7 (some ⟨(), zeroShape⟩) (fun _ => RecursiveSpace.bottom)) :=
  recursiveEncoded_wrong_tag_refused naturalPresentation ⟨(), zeroShape⟩ 7 (by decide) _

theorem missing_payload_refused :
    ¬ RecursiveEncoded naturalPresentation
      (RecursiveSpace.construct 1 (none : naturalPayload) (fun _ => RecursiveSpace.bottom)) :=
  recursiveEncoded_missing_payload_refused naturalPresentation PUnit.unit 1 _

noncomputable def naturalModel := RecursiveSpace.treeModel naturalPayload
noncomputable def interpretedNaturalRepresentation := interpretedRepresentation naturalPresentation PUnit.unit naturalModel ()

theorem interpreted_natural_roundtrip :
    interpretedNaturalRepresentation.symm (interpretedNaturalRepresentation naturalTwo) = naturalTwo :=
  interpretedNaturalRepresentation.symm_apply_apply naturalTwo

noncomputable def vectorTwo := Vectors.cons true (Vectors.cons false Vectors.nil)
noncomputable def vectorRepresentation :=
  recursiveSpaceRepresentation vectorPresentation PUnit.unit (Natural.succ (Natural.succ Natural.zero))

theorem vector_roundtrip : vectorRepresentation.symm (vectorRepresentation vectorTwo) = vectorTwo :=
  vectorRepresentation.symm_apply_apply vectorTwo

theorem vector_image_valid :
    RecursiveValid vectorPresentation (vectorRepresentation vectorTwo).val (Natural.succ (Natural.succ Natural.zero)) :=
  (vectorRepresentation vectorTwo).property

theorem vector_order_retained :
    vectorRepresentation vectorTwo ≠ vectorRepresentation (Vectors.cons false (Vectors.cons true Vectors.nil)) := by
  intro same
  have sources := vectorRepresentation.injective same
  have lists := congrArg (fun value => (Vectors.toList value).val) sources
  change [true, false] = [false, true] at lists
  cases List.cons.inj lists |>.1

#print axioms natural_roundtrip
#print axioms hidden_tail_refused
#print axioms interpreted_natural_roundtrip
#print axioms vector_roundtrip
#print axioms vector_order_retained
namespace Relations
open Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics

noncomputable def filler : Relation naturalPayload := fun _ _ => True
noncomputable def naturalRelationalModel := model filler
noncomputable def naturalRelationalRepresentation :=
  interpretedRepresentation naturalPresentation PUnit.unit naturalRelationalModel ()

theorem natural_roundtrip :
    naturalRelationalRepresentation.symm (naturalRelationalRepresentation naturalTwo) = naturalTwo :=
  naturalRelationalRepresentation.symm_apply_apply naturalTwo

theorem valid_natural :
    RecursiveValid naturalPresentation
      ((RecursiveSpace.equivalence naturalRelationalModel).symm (naturalRelationalRepresentation naturalTwo).val) () :=
  (naturalRelationalRepresentation naturalTwo).property

noncomputable def vectorFiller : Relation (RecursivePayload vectorPresentation PUnit.unit) := fun _ _ => False
noncomputable def vectorRelationalModel := model vectorFiller
noncomputable def vectorRelationalRepresentation :=
  interpretedRepresentation vectorPresentation PUnit.unit vectorRelationalModel
    (Natural.succ (Natural.succ Natural.zero))

theorem vector_roundtrip :
    vectorRelationalRepresentation.symm (vectorRelationalRepresentation vectorTwo) = vectorTwo :=
  vectorRelationalRepresentation.symm_apply_apply vectorTwo

theorem vector_order_retained :
    vectorRelationalRepresentation vectorTwo ≠
      vectorRelationalRepresentation (Vectors.cons false (Vectors.cons true Vectors.nil)) := by
  intro same
  have source := vectorRelationalRepresentation.injective same
  have lists := congrArg (fun value => (Vectors.toList value).val) source
  change [true, false] = [false, true] at lists
  cases List.cons.inj lists |>.1

end Relations
#print axioms Relations.natural_roundtrip
#print axioms Relations.vector_roundtrip
#print axioms Relations.vector_order_retained
end Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursiveSpaceControls

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursiveSpaceControls.Registered
open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.RecursiveSpaceRepresentation
open PositiveInductiveScenarios.Search

abbrev sourceOrder := ModuleSource.PositiveInductiveLoweringControls.Search.sourceOrder
abbrev registered := ModuleSource.PositiveInductiveLoweringControls.WholeFamily.source_registered
noncomputable def presentation := IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder admitted registered
noncomputable def representation := IndexedPositiveContainer.RecursiveSpaceRepresentation.blockRepresentation sourceOrder admitted registered environment ()
noncomputable def sample : SearchTree := branch [solved true, solved false]

theorem sample_roundtrip : representation.symm (representation sample) = sample :=
  representation.symm_apply_apply sample

theorem order_retained : representation sample ≠ representation (branch [solved false, solved true]) := by
  intro same
  have source := representation.injective same
  have outputs := congrArg answers source
  change [true, false] = [false, true] at outputs
  cases List.cons.inj outputs |>.1

open Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics
noncomputable def filler : Relation (RecursivePayload presentation environment) := fun _ _ => False
noncomputable def relationalModel := model filler
noncomputable def relationalRepresentation :=
  IndexedPositiveContainer.RecursiveSpaceRepresentation.interpretedBlockRepresentation sourceOrder admitted registered environment relationalModel ()

theorem relational_roundtrip : relationalRepresentation.symm (relationalRepresentation sample) = sample :=
  relationalRepresentation.symm_apply_apply sample

theorem relational_order_retained :
    relationalRepresentation sample ≠ relationalRepresentation (branch [solved false, solved true]) := by
  intro same
  have source := relationalRepresentation.injective same
  have outputs := congrArg answers source
  change [true, false] = [false, true] at outputs
  cases List.cons.inj outputs |>.1

noncomputable def vectorCode := IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation
  IndexedPositiveContainer.VectorControl.orderedFinitary IndexedPositiveContainer.VectorControl.code

theorem vector_two_outside_refused :
    (vectorCode.coding (IndexedPositiveContainer.VectorControl.shapeAt 2)).decode (2 : Nat) = none := by
  apply (IndexedPositiveContainer.RecursiveSpaceRepresentation.code_padding_iff _ _ _ _).mpr
  change (2 : Nat) ≤ 2
  exact Nat.le_refl 2

theorem vector_three_third_present :
    (vectorCode.coding (IndexedPositiveContainer.VectorControl.shapeAt 3)).decode (2 : Nat) ≠ none := by
  intro absent
  have impossible := (IndexedPositiveContainer.RecursiveSpaceRepresentation.code_padding_iff _ _ _ _).mp absent
  change (3 : Nat) ≤ 2 at impossible
  omega

theorem vector_third_order :
    (vectorCode.coding (IndexedPositiveContainer.VectorControl.shapeAt 3)).encode
      (IndexedPositiveContainer.Code.orderedPositionEquiv
        IndexedPositiveContainer.VectorControl.orderedFinitary IndexedPositiveContainer.VectorControl.code
        (IndexedPositiveContainer.VectorControl.shapeAt 3) ⟨2, by change 2 < 3; decide⟩) = (2 : Nat) :=
  IndexedPositiveContainer.RecursiveSpaceRepresentation.code_position_order _ _ _ _

#print axioms sample_roundtrip
#print axioms order_retained
#print axioms relational_roundtrip
#print axioms relational_order_retained
#print axioms vector_two_outside_refused
#print axioms vector_three_third_present
end Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursiveSpaceControls.Registered

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursiveSpaceControls.Relations
open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.RecursiveSpaceRepresentation
open IndexedInductiveNatVec
open HOLFacts.RawPredicateInterpretation.Controls

theorem constructor_clause :
    interpretedEncode naturalPresentation naturalRelationalModel (Fix.roll succShape (fun _ => Natural.zero)) =
      naturalRelationalModel.construct 1 (some ⟨(), succShape⟩)
        (((positions naturalPresentation).coding succShape).extend naturalRelationalModel.bottom
          (fun _ => interpretedEncode naturalPresentation naturalRelationalModel Natural.zero)) :=
  interpretedEncode_constructor naturalPresentation naturalRelationalModel succShape (fun _ => Natural.zero)

#print axioms constructor_clause
end Mettapedia.GSLT.LanguageDef.IndexedInductive.RecursiveSpaceControls.Relations
