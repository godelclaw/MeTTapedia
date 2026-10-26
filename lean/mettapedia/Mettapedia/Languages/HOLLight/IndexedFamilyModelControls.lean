import Mettapedia.Languages.HOLLight.IndexedRegisteredFamilyModels
import Mettapedia.Languages.HOLLight.SourceProfileModelsControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec

/-!
# Source-parameter and indexed-family interpretation controls

A concrete accepted reference replay exercises parameter replacement and its
scope boundary. Relational carrier transport preserves genuine constructors.
The admitted Natural/Vector families instantiate the generic source-family
representation uniformly in received root evidence. Reversed vector contents
remain distinct; an empty-element length-one vector retains an empty guard.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IndexedFamilyModelControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open TypeFamilySemantics SourceProfileModels
open Mettapedia.TypeTheory
open IndexedPolynomial RecursiveSpaceRepresentation
open Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec

namespace Parameters

noncomputable def frame :=
  (sourceReplayFrame.{0} Controls.Phases.commands Controls.Phases.after Controls.Phases.replayed).frame

def prior : Assignment.{0} := fun _ => ⟨ULift.{1} Unit,.up ()⟩
def parameter : Name := Name.global "A"
def sibling : Name := Name.global "B"

noncomputable def model := frame.model TypeFamilySemantics.Controls.initialOther
  (ModelParameterInterpretation.assignment prior parameter Bool false)

theorem selected_carrier : HOL.Ty.denote.{0,1} model.Carrier (Ty.var parameter).toHOL = ULift.{1} Bool :=
  ModelParameterInterpretation.parameter_carrier frame.family _ prior parameter Bool false

noncomputable def equivalence : Bool ≃ HOL.Ty.denote.{0,1} model.Carrier (Ty.var parameter).toHOL :=
  ModelParameterInterpretation.parameterEquivalence frame.family _ prior parameter Bool false

theorem values_distinguished : equivalence false ≠ equivalence true := by
  intro same
  cases equivalence.injective same

theorem sibling_carrier : HOL.Ty.denote.{0,1} model.Carrier (Ty.var sibling).toHOL = ULift.{1} Unit :=
  ModelParameterInterpretation.other_parameter_carrier frame.family _ prior parameter Bool false sibling (by decide)

theorem sibling_boolean_equivalence_refused :
    ¬ Nonempty (Bool ≃ HOL.Ty.denote.{0,1} model.Carrier (Ty.var sibling).toHOL) := by
  rw [sibling_carrier]
  rintro ⟨wrong⟩
  have same := wrong.injective (Subsingleton.elim (wrong false) (wrong true))
  cases same

end Parameters

namespace CarrierTransport

def filler : RecursiveSpaceSemantics.Relation Bool := fun _ _ => False

noncomputable def transported : RecursiveSpace.Model Bool (RecursiveSpace.Tree Bool) :=
  (RecursiveSpaceSemantics.model filler).changeCarrier (RecursiveSpaceSemantics.representation filler)

theorem bottom_preserved :
    RecursiveSpaceSemantics.representation filler transported.bottom = RecursiveSpaceSemantics.bottom filler :=
  RecursiveSpace.Model.changeCarrier_bottom _ _

theorem constructor_preserved (tag : Nat) (payload : Bool) (children : Nat → RecursiveSpace.Tree Bool) :
    transported.construct tag payload children = RecursiveSpace.construct tag payload children := by
  apply (RecursiveSpaceSemantics.representation filler).injective
  change RecursiveSpaceSemantics.representation filler
    (((RecursiveSpaceSemantics.model filler).changeCarrier (RecursiveSpaceSemantics.representation filler)).construct
      tag payload children) = _
  rw [RecursiveSpace.Model.changeCarrier_construct]
  rfl

theorem concrete_constructor :
    RecursiveSpaceSemantics.representation filler
      (transported.construct 3 true (fun _ => RecursiveSpace.bottom)) =
      (RecursiveSpaceSemantics.model filler).construct 3 true
        (fun _ => RecursiveSpaceSemantics.representation filler RecursiveSpace.bottom) :=
  RecursiveSpace.Model.changeCarrier_construct (RecursiveSpaceSemantics.model filler)
    (RecursiveSpaceSemantics.representation filler) 3 true (fun _ => RecursiveSpace.bottom)

theorem changed_tag_refused :
    transported.construct 3 true (fun _ => transported.bottom) ≠
      transported.construct 8 true (fun _ => transported.bottom) := by
  intro same
  have impossible := ((transported.construct_injective _ _ _ _ _ _).mp same).1
  cases impossible

theorem hidden_child_refused :
    transported.construct 3 true
      (fun n => if n = 1 then transported.construct 8 false (fun _ => transported.bottom) else transported.bottom) ≠
      transported.construct 3 true (fun _ => transported.bottom) := by
  intro same
  have children := ((transported.construct_injective _ _ _ _ _ _).mp same).2.2
  have impossible := congrFun children 1
  simp only [ite_true] at impossible
  exact transported.construct_ne_bottom _ _ _ impossible

end CarrierTransport

namespace Families

abbrev naturalPresentation := Description.recursiveSpacePresentation Natural.constructors
noncomputable abbrev vectorPresentation (element : Type) :=
  Description.recursiveSpacePresentation (Vectors.constructors element)

noncomputable def naturalRepresentation (roots : IndexedFamilyModels.ReceivedRoots) :=
  IndexedFamilyModels.representation roots naturalPresentation PUnit.unit
    TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural) ()

noncomputable def vectorRepresentation (roots : IndexedFamilyModels.ReceivedRoots) (element : Type)
    (length : Natural.Carrier) :=
  IndexedFamilyModels.representation roots (vectorPresentation element) PUnit.unit
    TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural) length

theorem natural_two_distinguished (roots : IndexedFamilyModels.ReceivedRoots) :
    naturalRepresentation roots (Natural.succ (Natural.succ Natural.zero)) ≠ naturalRepresentation roots Natural.zero := by
  intro same
  have inputs := (naturalRepresentation roots).injective same
  have impossible := congrArg Natural.toNat inputs
  cases impossible

theorem vector_order_retained (roots : IndexedFamilyModels.ReceivedRoots) :
    vectorRepresentation roots Bool (Natural.succ (Natural.succ Natural.zero))
        (Vectors.cons true (Vectors.cons false Vectors.nil)) ≠
      vectorRepresentation roots Bool (Natural.succ (Natural.succ Natural.zero))
        (Vectors.cons false (Vectors.cons true Vectors.nil)) := by
  intro same
  have inputs := (vectorRepresentation roots Bool _).injective same
  have lists := congrArg (fun value => (Vectors.toList value).val) inputs
  change [true,false] = [false,true] at lists
  cases List.cons.inj lists |>.1

theorem empty_vector_guard_retained (roots : IndexedFamilyModels.ReceivedRoots) :
    IsEmpty (IndexedFamilyModels.Family roots (vectorPresentation Empty) PUnit.unit
      TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural)
      (Natural.succ Natural.zero)) := by
  refine ⟨fun value => ?_⟩
  let source := (vectorRepresentation roots Empty _).symm value
  obtain ⟨list,length⟩ := Vectors.toList source
  cases list with
  | nil => cases length
  | cons impossible _ => exact nomatch impossible

end Families

#print axioms Parameters.equivalence
#print axioms Parameters.sibling_boolean_equivalence_refused
#print axioms CarrierTransport.constructor_preserved
#print axioms CarrierTransport.hidden_child_refused
#print axioms Families.natural_two_distinguished
#print axioms Families.vector_order_retained
#print axioms Families.empty_vector_guard_retained

end Mettapedia.Languages.HOLLight.IndexedFamilyModelControls
