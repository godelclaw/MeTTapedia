import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestMethodSpecialization
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllResultAdapter

/-!
# A native result adapter for a registered Vector-container method

The registered constructor code is instantiated at a natural-number algebra:
its constructor returns the supplied length. The method has a length field,
a Vector field and one nested result argument. The source method, its typed
original fields, the complete All bundle and the existing native projection
meet at one signature. This is an algebra/method instance; it makes no
initiality claim for the natural-number carrier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerNativeResultAdapter

open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation FormationSensitive FunctionArgumentAdapters
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies TypedEquality.Normalization
open IndexedInductive.Guest (TermEnv mapEnv)
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestResultArguments IndexedPositiveContainerGuestMethodSpecialization
open IndexedPositiveContainerGuestControls.Vectors
open NativeVectorAll.ResultView

abbrev rules := NativeVectorAllResultAdapter.rules
abbrev decoder := NativeVectorAllResultAdapter.decoder
abbrev choices := NativeVectorAllResultAdapter.choices

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def sourceContainers : RegistrySyntax I registry Tower.Head := { containers with
  bundleType := by
    intro context n name entry registered output environment element predicate field
    obtain rfl := registered_entry registered
    exact NativeVectorAll.Universes.Canonical.allTypeAtUniverse (.max Tower.zero (.succ Tower.zero))
      element predicate (lengthTerm output environment) field
  bundleType_substitute := by
    intro context n m name entry registered output environment element predicate field sigma
    obtain rfl := registered_entry registered
    change subst sigma (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (.max Tower.zero (.succ Tower.zero))
      element predicate (lengthTerm output environment) field) =
      NativeVectorAll.Universes.Canonical.allTypeAtUniverse (.max Tower.zero (.succ Tower.zero))
        (subst sigma element) (subst sigma predicate)
        (lengthTerm output (mapEnv (subst sigma) environment)) (subst sigma field)
    rw [NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse,
      lengthTerm_substitute output environment sigma] }

def resultSyntax : ResultSyntax I registry Tower.Head where
  viewType := by
    intro context n name entry registered output environment _ _ _
    obtain rfl := registered_entry registered
    exact OriginalInputUniverses.upperVec (sortTm Tower.zero) (lengthTerm output environment)
  projection := by
    intro context n name entry registered output environment element _ field
    obtain rfl := registered_entry registered
    exact appSpine (.const OriginalInputUniverses.ClosedResultDefinition.selfName)
      [element, sortTm Tower.zero, lengthTerm output environment, field]
  viewType_substitute := by
    intro context n m name entry registered output environment element predicate field sigma
    obtain rfl := registered_entry registered
    change subst sigma (OriginalInputUniverses.upperVec (sortTm Tower.zero) (lengthTerm output environment)) =
      OriginalInputUniverses.upperVec (sortTm Tower.zero) (lengthTerm output (mapEnv (subst sigma) environment))
    simp only [OriginalInputUniverses.upperVec, appSpine, List.foldl_cons, List.foldl_nil,
      subst, sortTm]
    exact congrArg (OriginalInputUniverses.upperVec (sortTm Tower.zero))
      (lengthTerm_substitute output environment sigma)
  projection_substitute := by
    intro context n m name entry registered output environment element predicate field sigma
    obtain rfl := registered_entry registered
    change subst sigma (appSpine (.const OriginalInputUniverses.ClosedResultDefinition.selfName)
      [element, sortTm Tower.zero, lengthTerm output environment, field]) =
      appSpine (.const OriginalInputUniverses.ClosedResultDefinition.selfName)
        [subst sigma element, sortTm Tower.zero, lengthTerm output (mapEnv (subst sigma) environment), subst sigma field]
    simp only [appSpine, List.foldl_cons, List.foldl_nil, subst, sortTm]
    exact congrArg (fun length => appSpine (.const OriginalInputUniverses.ClosedResultDefinition.selfName)
      [subst sigma element, sortTm Tower.zero, length, subst sigma field])
      (lengthTerm_substitute output environment sigma)

abbrev code := VectorControl.code

def algebraTypes {n : Nat} : TypeSyntax I Tower.Head n where
  dataType _ := natTm
  family := natTm
  constructor _ := .lam (.lam (.var 1))

def motive {n : Nat} : Tower.Tm n := predicate (sortTm Tower.zero)
def constructorType : Tower.Tm 0 :=
  IndexedPositiveContainerGuestTypes.constructorType indexing sourceContainers code algebraTypes PUnit.unit
def constructorProgramme : Tower.Tm 0 := .lam (.lam (.var 1))
def constructorContext : Tower.Ctx 1 := .snoc .nil constructorType
def methodTypeAt {n : Nat} (constructor : Tower.Tm n) : Tower.Tm n :=
  methodBody indexing (resultSyntax.viewRegistry sourceContainers) code algebraTypes PUnit.unit motive constructor []
def sourceMethod : Tower.Tm 1 := methodTypeAt (.var 0)
def context : Tower.Ctx 2 := .snoc constructorContext sourceMethod
def constructor : Tower.Tm 2 := .var 1
def methodType : Tower.Tm 2 := methodTypeAt constructor

/-- Independently written length/children/results interface. -/
def methodSpine : Tower.Tm 2 :=
  .pi natTm (.pi (vecApp natTm (.var 0))
    (.pi (OriginalInputUniverses.upperVec (sortTm Tower.zero) (.var 1))
      (.app (predicate (sortTm Tower.zero)) (.app (.app (.var 4) (.var 2)) (.var 1)))))

theorem method_spine_exact : methodType = methodSpine := by decide +kernel

def fields : Fin (fieldCount code) → Tower.Tm 2 :=
  fun index => if index.val = 0 then liftClosed (NativeVectorAll.CanonicalAdequacy.numeral 2)
    else liftClosed OriginalInputUniverses.ClosedResultDefinition.source
def argumentSlots : List (Slot Tower.Head 2) :=
  slots indexing sourceContainers resultSyntax code algebraTypes PUnit.unit motive fields
def remainingType : Tower.Tm 2 := hypotheses (argumentSlots.map Slot.output)
  (conclusion indexing code PUnit.unit motive constructor fields)

set_option maxRecDepth 8192 in
theorem constructor_formed : NativeVectorAllResultAdapter.checked constructorType (sortTm Tower.zero) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem constructor_checked : NativeVectorAllResultAdapter.checked constructorProgramme constructorType = true := by
  decide +kernel

theorem constructor_context_formed : ContextFormation rules constructorContext :=
  .snoc .nil (NativeVectorAllResultAdapter.checked_sound constructor_formed).typing (.sort _)

def methodChecked : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 256 constructorContext
    sourceMethod (sortTm (.succ Tower.zero))).isSome

set_option maxRecDepth 8192 in
theorem method_formed : methodChecked = true := by decide +kernel

theorem method_formation : Judgment rules constructorContext sourceMethod (sortTm (.succ Tower.zero)) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp method_formed
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 constructorContext
    _ _ submission produced

set_option maxRecDepth 8192 in
theorem number_checked : NativeVectorAllResultAdapter.checked (NativeVectorAll.CanonicalAdequacy.numeral 2) natTm = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem vector_checked : NativeVectorAllResultAdapter.checked OriginalInputUniverses.ClosedResultDefinition.source
    (vecApp natTm (NativeVectorAll.CanonicalAdequacy.numeral 2)) = true := by decide +kernel

theorem context_formed : ContextFormation rules context :=
  .snoc constructor_context_formed method_formation.typing (.sort _)

theorem method_open : methodType = rename wk sourceMethod := by decide +kernel

theorem source_typed : Judgment rules context (.var 0) methodType := by
  refine ⟨context_formed, ?_⟩
  rw [method_open]
  exact .var 0

theorem field_evidence : SuppliedFields rules context code fields methodType remainingType := by
  have number : Typing rules context (fields ⟨0, by decide +kernel⟩) natTm := by
    have lifted := (NativeVectorAllResultAdapter.checked_sound number_checked).typing.substitute
      (Δ := context) (σ := Fin.elim0) (fun index => Fin.elim0 index)
    simpa [fields, TelescopeAbstraction.subst_empty, liftClosed, natTm, rename] using lifted
  have vector : Typing rules context (fields ⟨1, by decide +kernel⟩) (vecApp natTm (fields ⟨0, by decide +kernel⟩)) := by
    have lifted := (NativeVectorAllResultAdapter.checked_sound vector_checked).typing.substitute
      (Δ := context) (σ := Fin.elim0) (fun index => Fin.elim0 index)
    simpa [fields, TelescopeAbstraction.subst_empty, liftClosed, vecApp, natTm, rename] using lifted
  rw [method_spine_exact]
  unfold methodSpine
  refine SuppliedFields.data (I := I) VectorControl.DataSort.length _ fields
    number ?_
  refine SuppliedFields.nested "Vector" VectorControl.entry (by simp [VectorControl.registry])
    .here () (.result ()) (fun i => fields i.succ)
    vector ?_
  let body : Tower.Tm 4 :=
    .pi (OriginalInputUniverses.upperVec (sortTm Tower.zero) (.var 1))
      (.app (predicate (sortTm Tower.zero)) (.app (.app (.var 4) (.var 2)) (.var 1)))
  have readback : inst0 (fields ⟨1, by decide +kernel⟩)
      (subst (liftSub (subst0 (fields ⟨0, by decide +kernel⟩))) body) = remainingType := by
    decide +kernel
  change SuppliedFields (I := I) (registry := registry) (parameters := 0)
    (context := [VectorControl.DataSort.length]) rules context (.result ()) (fun i => fields i.succ.succ)
    (inst0 (fields ⟨1, by decide +kernel⟩)
      (subst (liftSub (subst0 (fields ⟨0, by decide +kernel⟩))) body)) remainingType
  rw [readback]
  exact .result _ _ _

theorem slots_exact : argumentSlots = [NativeVectorAllResultAdapter.nestedSlot.weaken.weaken] := by
  have injective : Function.Injective
      (fun slot : Slot Tower.Head 2 => (slot.input, slot.output, slot.projection)) := by
    intro first second same
    cases first
    cases second
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    rfl
  apply (List.map_inj_right (fun _ _ same => injective same)).mp
  decide +kernel

theorem primitive_evidence : SlotsTyped rules context (.sort (.succ Tower.zero)) argumentSlots := by
  rw [slots_exact]
  intro slot present
  have selected : slot = NativeVectorAllResultAdapter.nestedSlot.weaken.weaken := by simpa using present
  subst slot
  have primitive := (NativeVectorAllResultAdapter.slots_typed.weaken constructorType).weaken sourceMethod
  exact primitive NativeVectorAllResultAdapter.nestedSlot.weaken.weaken (by
    simp [NativeVectorAllResultAdapter.slots])

def resultChecked : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 256 context
    (conclusion indexing code PUnit.unit motive constructor fields) (sortTm (.succ Tower.zero))).isSome

set_option maxRecDepth 8192 in
theorem result_formed : resultChecked = true := by decide +kernel

theorem result_typed : Typing rules context
    (conclusion indexing code PUnit.unit motive constructor fields) (sortTm (.succ Tower.zero)) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp result_formed
  exact (FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 context
    _ _ submission produced).typing

def programme : Tower.Tm 2 :=
  adapter indexing sourceContainers resultSyntax code algebraTypes PUnit.unit motive fields
    (applyFields code fields (.var 0))

theorem source_after_fields_typed : Judgment rules context (applyFields code fields (.var 0)) remainingType :=
  ⟨source_typed.context, field_evidence.apply_typed source_typed.typing⟩

theorem argument_adapter_typed : Judgment rules context programme
    (hypotheses (argumentSlots.map Slot.input)
      (conclusion indexing code PUnit.unit motive constructor fields)) :=
  adapt_judgment NativeVectorAllResultAdapter.method_universe NativeVectorAllResultAdapter.product_closure
    argumentSlots primitive_evidence result_typed source_after_fields_typed

theorem programme_typed : Judgment rules context programme
    (hypotheses (argumentSlots.map Slot.input)
      (conclusion indexing code PUnit.unit motive constructor fields)) :=
  adaptedMethod_typed indexing sourceContainers resultSyntax code algebraTypes PUnit.unit motive constructor fields
    NativeVectorAllResultAdapter.method_universe NativeVectorAllResultAdapter.product_closure
    primitive_evidence result_typed source_typed field_evidence

set_option maxRecDepth 8192 in
theorem evidence_checked : NativeVectorAllResultAdapter.checked
    OriginalInputUniverses.ClosedResultDefinition.witnesses NativeVectorAllResultAdapter.inputType = true := by
  decide +kernel

def application : Tower.Tm 2 :=
  .app programme (liftClosed OriginalInputUniverses.ClosedResultDefinition.witnesses)

theorem application_typed : Judgment rules context application
    (conclusion indexing code PUnit.unit motive constructor fields) := by
  have arrowType : hypotheses (argumentSlots.map Slot.input)
      (conclusion indexing code PUnit.unit motive constructor fields) =
      arrow (liftClosed NativeVectorAllResultAdapter.inputType)
        (conclusion indexing code PUnit.unit motive constructor fields) := by decide +kernel
  have function := programme_typed.typing
  rw [arrowType] at function
  exact ⟨context_formed, arrow_apply function
    (NativeVectorAllResultAdapter.checked_sound evidence_checked).typing.weaken.weaken⟩

def projectedApplication : Tower.Tm 2 :=
  .app (applyFields code fields (.var 0)) (liftClosed OriginalInputUniverses.ClosedResultDefinition.output)

theorem projected_application_typed : Judgment rules context projectedApplication
    (conclusion indexing code PUnit.unit motive constructor fields) := by
  have arrowType : remainingType = arrow (liftClosed OriginalInputUniverses.ClosedResultDefinition.outputType)
      (conclusion indexing code PUnit.unit motive constructor fields) := by decide +kernel
  have function := source_after_fields_typed.typing
  rw [arrowType] at function
  exact ⟨context_formed, arrow_apply function
    OriginalInputUniverses.ClosedResultDefinition.output_typed.typing.weaken.weaken⟩

def constructorSubstitution : Sub Tower.Head 1 0 := fun _ => constructorProgramme

theorem constructor_substitution_typed : FormationSensitive.CtxMor rules constructorContext .nil constructorSubstitution := by
  intro index
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
  have exactType : subst constructorSubstitution (Ctx.lookup constructorContext 0) = constructorType := by
    decide +kernel
  rw [exactType]
  exact (NativeVectorAllResultAdapter.checked_sound constructor_checked).typing

def closedMethodType : Tower.Tm 0 := subst constructorSubstitution sourceMethod

theorem closed_method_formed : Judgment rules .nil closedMethodType (sortTm (.succ Tower.zero)) := by
  exact method_formation.substitute .nil constructor_substitution_typed

def closedContext : Tower.Ctx 1 := .snoc .nil closedMethodType

theorem closed_context_formed : ContextFormation rules closedContext :=
  .snoc .nil closed_method_formed.typing (.sort _)

def programmeSubstitution : Sub Tower.Head 2 1 :=
  Fin.cases (.var 0) (fun _ => liftClosed constructorProgramme)

theorem programme_substitution_typed : FormationSensitive.CtxMor rules context closedContext programmeSubstitution := by
  intro index
  fin_cases index
  · change Typing rules closedContext (.var 0) (subst programmeSubstitution (Ctx.lookup context 0))
    have exactType : subst programmeSubstitution (Ctx.lookup context 0) = Ctx.lookup closedContext 0 := by
      decide +kernel
    rw [exactType]
    exact .var 0
  · change Typing rules closedContext (liftClosed constructorProgramme)
      (subst programmeSubstitution (Ctx.lookup context 1))
    have exactType : subst programmeSubstitution (Ctx.lookup context 1) = liftClosed constructorType := by
      decide +kernel
    rw [exactType]
    have lifted := (NativeVectorAllResultAdapter.checked_sound constructor_checked).typing.substitute
      (Δ := closedContext) (σ := Fin.elim0) (fun impossible => Fin.elim0 impossible)
    simpa only [TelescopeAbstraction.subst_empty] using lifted

def closedProgramme : Tower.Tm 1 := subst programmeSubstitution programme
def closedProgrammeType : Tower.Tm 1 := subst programmeSubstitution
  (hypotheses (argumentSlots.map Slot.input)
    (conclusion indexing code PUnit.unit motive constructor fields))

/-- Typed substitution installs the independently checked length constructor.
The method remains arbitrary at its formed, specialized source interface. -/
theorem closed_constructor_programme_typed : Judgment rules closedContext closedProgramme closedProgrammeType :=
  programme_typed.substitute closed_context_formed programme_substitution_typed

theorem closed_constructor_application_typed : Judgment rules closedContext
    (subst programmeSubstitution application)
    (subst programmeSubstitution (conclusion indexing code PUnit.unit motive constructor fields)) :=
  application_typed.substitute closed_context_formed programme_substitution_typed

#print axioms field_evidence
#print axioms primitive_evidence
#print axioms programme_typed
#print axioms application_typed
#print axioms projected_application_typed
#print axioms closed_constructor_programme_typed
#print axioms closed_constructor_application_typed

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerNativeResultAdapter
