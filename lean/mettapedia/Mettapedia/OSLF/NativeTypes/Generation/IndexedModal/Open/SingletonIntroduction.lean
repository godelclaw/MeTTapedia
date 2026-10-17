import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingletonMembership
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyCoverage
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.LambdaEvents
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Interpretation

/-!
# Nonempty native response families from independent singleton inputs

The rely classifier is equality with the actual supplied rely value. The
constant target continuation classifies the actual target independently.
Every request is answered by the original source event. Replacing only the
target by false retains an actual request and rejects native membership.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingletonIntroduction

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations CertifiedProjection
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open SingleRelyParameters

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)
variable (rely target focus : D.Carrier) (kind sort : HSort)

noncomputable section

abbrev iface := SingleRelyParameters.interface rely target focus kind sort
abbrev requests := ContinuationSemantics.requests operational algebra vertex (iface rely target focus kind sort)

variable (observed : ResponseSemantics.Observations operational (iface rely target focus kind sort))

def relyName : observed.events ⟶ validPresheaf operational rely kind :=
  CertifiedSections.predicateName operational rely kind
    (SingletonMembership.singleton operational rely (observed.relies 0))

def targetName : observed.events ⟶ validPresheaf operational target sort :=
  CertifiedSections.predicateName operational target sort
    (SingletonMembership.singleton operational target observed.target)

def falseTarget : observed.events ⟶ validPresheaf operational target sort :=
  CertifiedSections.predicateName operational target sort
    (⊥ : Subfunctor (FunctorToTypes.prod (operational target) observed.events))

def parameters : observed.events ⟶ (requests operational algebra vertex rely target focus kind sort).parameters.1 :=
  encode operational algebra vertex rely target focus kind sort
    (relyName operational rely target focus kind sort observed)
    (targetName operational rely target focus kind sort observed)

def falseParameters : observed.events ⟶ (requests operational algebra vertex rely target focus kind sort).parameters.1 :=
  encode operational algebra vertex rely target focus kind sort
    (relyName operational rely target focus kind sort observed)
    (falseTarget operational rely target focus kind sort observed)

/-- The generated request's membership evidence forces the independently
chosen rely value; no image of successful responses defines the singleton. -/
theorem request_rely {world : Wᵒᵖ} (event : observed.events.obj world)
    (request : (requests operational algebra vertex rely target focus kind sort).values.obj world)
    (lyingOver : (requests operational algebra vertex rely target focus kind sort).project.app world request =
      (parameters operational algebra vertex rely target focus kind sort observed).app world event) :
    Code.Member (((requests operational algebra vertex rely target focus kind sort).relies 0).app world request)
      ((SingletonMembership.singletonName operational rely kind (observed.relies 0)).app world event) := by
  have member := SingleRelyEvidence.rely_member vertex operational algebra
    (iface rely target focus kind sort) 0 world request
  have classifier := ConcreteCategory.congr_hom
    (NatTrans.congr_app (encoded_classifier operational algebra vertex rely target focus kind sort
      (relyName operational rely target focus kind sort observed)
      (targetName operational rely target focus kind sort observed)) world) event
  change (SingleRelyEvidence.parameterClassifier vertex operational algebra
    (iface rely target focus kind sort) 0).app world
      ((parameters operational algebra vertex rely target focus kind sort observed).app world event) =
    ((SingletonMembership.singletonName operational rely kind (observed.relies 0)).app world event) at classifier
  rw [lyingOver, classifier] at member
  exact member

theorem source_meaning (world : Wᵒᵖ) (event : observed.events.obj world) :
    ResponseSemantics.SourceMeaning (requests operational algebra vertex rely target focus kind sort)
      observed world (observed.focus.app world event)
        ((parameters operational algebra vertex rely target focus kind sort observed).app world event) := by
  apply SingletonMembership.source_meaning_of_singleton_fibres operational
    (requests operational algebra vertex rely target focus kind sort) observed
    (parameters operational algebra vertex rely target focus kind sort observed)
  · intro world event request lyingOver position
    exact position.elim0
  · intro world event request lyingOver position
    have zero : position = 0 := Fin.eq_zero position
    cases zero
    exact request_rely operational algebra vertex rely target focus kind sort observed event request lyingOver
  · intro world event request lyingOver
    have targetRead := SingleRelyCoverage.fibre_target operational algebra vertex rely target focus kind sort
      (relyName operational rely target focus kind sort observed)
      (targetName operational rely target focus kind sort observed) world event request lyingOver
    rw [targetRead]
    exact SingletonMembership.singleton_requested operational target sort observed.target world event

/-- A genuine value-and-evidence request exists at every source event. -/
def request (world : Wᵒᵖ) (event : observed.events.obj world) :
    (requests operational algebra vertex rely target focus kind sort).values.obj world :=
  SingleRelyRequests.canonicalRequest operational algebra vertex rely target focus kind sort
    (relyName operational rely target focus kind sort observed)
    (targetName operational rely target focus kind sort observed) world event
    ((observed.relies 0).app world event)
    (SingletonMembership.singleton_requested operational rely kind (observed.relies 0) world event)

theorem request_project (world : Wᵒᵖ) (event : observed.events.obj world) :
    (requests operational algebra vertex rely target focus kind sort).project.app world
      (request operational algebra vertex rely target focus kind sort observed world event) =
      (parameters operational algebra vertex rely target focus kind sort observed).app world event :=
  SingleRelyRequests.canonicalRequest_project operational algebra vertex rely target focus kind sort _ _ _ _ _ _

theorem request_value (world : Wᵒᵖ) (event : observed.events.obj world) :
    ((requests operational algebra vertex rely target focus kind sort).relies 0).app world
      (request operational algebra vertex rely target focus kind sort observed world event) =
      .operational ((observed.relies 0).app world event) :=
  SingleRelyRequests.canonicalRequest_rely operational algebra vertex rely target focus kind sort _ _ _ _ _ _

/-- This is decoded membership in the actual generated modal former. -/
theorem native_membership (world : Wᵒᵖ) (event : observed.events.obj world) :
    Code.Member (.operational (observed.focus.app world event))
      (certifiedAtEquiv operational focus sort
        (requests operational algebra vertex rely target focus kind sort).parameters.1
        ⟨world, (parameters operational algebra vertex rely target focus kind sort observed).app world event⟩
        ((ResponseSemantics.former (requests operational algebra vertex rely target focus kind sort) observed).val
          ⟨world, (parameters operational algebra vertex rely target focus kind sort observed).app world event⟩)).val :=
  (ResponseSemantics.former_exact (requests operational algebra vertex rely target focus kind sort) observed world _ _).mpr
    (source_meaning operational algebra vertex rely target focus kind sort observed world event)

def falseRequest (world : Wᵒᵖ) (event : observed.events.obj world) :
    (requests operational algebra vertex rely target focus kind sort).values.obj world :=
  SingleRelyRequests.canonicalRequest operational algebra vertex rely target focus kind sort
    (relyName operational rely target focus kind sort observed)
    (falseTarget operational rely target focus kind sort observed) world event
    ((observed.relies 0).app world event)
    (SingletonMembership.singleton_requested operational rely kind (observed.relies 0) world event)

theorem false_request_project (world : Wᵒᵖ) (event : observed.events.obj world) :
    (requests operational algebra vertex rely target focus kind sort).project.app world
      (falseRequest operational algebra vertex rely target focus kind sort observed world event) =
      (falseParameters operational algebra vertex rely target focus kind sort observed).app world event :=
  SingleRelyRequests.canonicalRequest_project operational algebra vertex rely target focus kind sort _ _ _ _ _ _

/-- Failure here is not vacuous universal quantification: the same actual
operational rely value still gives an admitted request. -/
theorem false_source_meaning (world : Wᵒᵖ) (event : observed.events.obj world) :
    ¬ ResponseSemantics.SourceMeaning (requests operational algebra vertex rely target focus kind sort)
      observed world (observed.focus.app world event)
        ((falseParameters operational algebra vertex rely target focus kind sort observed).app world event) := by
  apply SingletonMembership.false_target_excludes_nonempty_request operational
    (requests operational algebra vertex rely target focus kind sort) observed world
    (observed.focus.app world event)
    ((falseParameters operational algebra vertex rely target focus kind sort observed).app world event)
    (falseRequest operational algebra vertex rely target focus kind sort observed world event)
    (false_request_project operational algebra vertex rely target focus kind sort observed world event) event
  exact SingleRelyRequests.canonicalRequest_target operational algebra vertex rely target focus kind sort _ _ _ _ _ _

/-- Every interface with one actual rely input has both an inhabited modal
family and a nonempty requested family whose false target is uninhabited. -/
theorem single_source_samples (interface : Interface D.Carrier)
    (observations : ResponseSemantics.Observations operational interface)
    (noIndices : interface.indices = []) (oneRely : interface.relies.length = 1)
    (world : Wᵒᵖ) (event : observations.events.obj world) :
    let generated := ContinuationSemantics.requests operational algebra vertex interface
    (∃ parameter request, generated.project.app world request = parameter ∧
      ResponseSemantics.SourceMeaning generated observations world
        (observations.focus.app world event) parameter) ∧
    (∃ parameter request, generated.project.app world request = parameter ∧
      ¬ ResponseSemantics.SourceMeaning generated observations world
        (observations.focus.app world event) parameter) := by
  rcases interface with ⟨indices, relies, target, focus, sort⟩
  dsimp only at noIndices oneRely
  subst indices
  cases relies with
  | nil => simp at oneRely
  | cons entry rest =>
      have restEmpty : rest = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at oneRely
        omega
      subst rest
      rcases entry with ⟨rely, kind⟩
      exact ⟨⟨(parameters operational algebra vertex rely target focus kind sort observations).app world event,
          request operational algebra vertex rely target focus kind sort observations world event,
          request_project operational algebra vertex rely target focus kind sort observations world event,
          source_meaning operational algebra vertex rely target focus kind sort observations world event⟩,
        ⟨(falseParameters operational algebra vertex rely target focus kind sort observations).app world event,
          falseRequest operational algebra vertex rely target focus kind sort observations world event,
          false_request_project operational algebra vertex rely target focus kind sort observations world event,
          false_source_meaning operational algebra vertex rely target focus kind sort observations world event⟩⟩

/-- The installation supplies the original complete event diagram. The
conclusion uses its actual generated native meaning and actual requests. -/
theorem authored_source_samples (installed : Joined.Installed) (index : installed.Index)
    (noIndices : (CurriedInterfaces.interface installed.indexed index).indices = [])
    (oneRely : (CurriedInterfaces.interface installed.indexed index).relies.length = 1)
    (world : (Interpretation.worlds installed)ᵒᵖ)
    (event : (BindingObservations.observations installed index).events.obj world) :
    let generated := Interpretation.requests installed index
    let focus := (BindingObservations.observations installed index).focus.app world event
    (∃ parameter request, generated.project.app world request = parameter ∧
      Interpretation.NativeMeaning installed index world focus parameter) ∧
    (∃ parameter request, generated.project.app world request = parameter ∧
      ¬ Interpretation.NativeMeaning installed index world focus parameter) := by
  obtain ⟨⟨positive, first, firstOver, positiveMeaning⟩, ⟨negative, second, secondOver, negativeMeaning⟩⟩ :=
    single_source_samples (AuthoredClassifiers.operational installed.indexed)
      (AuthoredClassifiers.algebra installed.indexed) installed.indexed.classifierVertex
      (CurriedInterfaces.interface installed.indexed index) (BindingObservations.observations installed index)
      noIndices oneRely world event
  refine ⟨⟨positive, first, firstOver, ?_⟩, ⟨negative, second, secondOver, ?_⟩⟩
  · exact (Interpretation.native_meaning_source installed index world _ positive).mpr positiveMeaning
  · intro member
    exact negativeMeaning ((Interpretation.native_meaning_source installed index world _ negative).mp member)

def lambdaWorld (event : LambdaEvents.Event) : (Interpretation.worlds event.installed)ᵒᵖ :=
  BindingResponses.world (plan := BindingObservations.planOf event.installed) []

def lambdaEvent (event : LambdaEvents.Event) :
    (BindingObservations.observations event.installed event.index).events.obj (lambdaWorld event) := by
  have positions : (BindingObservations.admitted event.installed event.index).programPosition =
      ((event.installed.semantic.authored event.installed.indexed).semanticHeaderAdmission
        event.installed.indexed.headers[event.index].origin).programPosition := by
    apply NativeSignature.Carrier.sort.inj
    exact (BindingObservations.admitted event.installed event.index).program.symm.trans
      ((event.installed.semantic.authored event.installed.indexed).semanticHeaderAdmission
        event.installed.indexed.headers[event.index].origin).program
  have programEq : BindingObservations.sort event.installed event.index =
      event.installed.programSort event.index := by
    change ((BindingObservations.planOf event.installed).snapshot.language.types[
      (BindingObservations.admitted event.installed event.index).programPosition]).name =
      ((BindingObservations.planOf event.installed).snapshot.language.types[
      ((event.installed.semantic.authored event.installed.indexed).semanticHeaderAdmission
        event.installed.indexed.headers[event.index].origin).programPosition]).name
    rw [positions]
    rfl
  change Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaFocus.Frame
    (event.installed.indexed.schema event.index) [] (BindingObservations.sort event.installed event.index)
  rw [programEq]
  exact event.frame

/-- The original authored beta event from the public generator has an
inhabited contextual native type. Keeping its nonempty rely request while
changing the mandatory target to false produces nonmembership. -/
theorem lambda_samples (event : LambdaEvents.Event) :
    let generated := Interpretation.requests event.installed event.index
    let focus := (BindingObservations.observations event.installed event.index).focus.app
      (lambdaWorld event) (lambdaEvent event)
    (∃ parameter request, generated.project.app (lambdaWorld event) request = parameter ∧
      Interpretation.NativeMeaning event.installed event.index (lambdaWorld event) focus parameter) ∧
    (∃ parameter request, generated.project.app (lambdaWorld event) request = parameter ∧
      ¬ Interpretation.NativeMeaning event.installed event.index (lambdaWorld event) focus parameter) :=
  authored_source_samples event.installed event.index event.no_indices event.one_rely
    (lambdaWorld event) (lambdaEvent event)

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingletonIntroduction
