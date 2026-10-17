import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes
import Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction

open Mettapedia.OSLF.Framework

/-!
# Introduction in a native sort model

An interpretation is an operation-closed model when its actual typed native
constructor introductions preserve the authored input and output subobjects.
Its equation law is stated on primitive equation completions. Neither law
contains a generated type-code predicate or a modal inhabitant assumption.

Those independent laws imply membership of every classified structural code.
Computed base-rule introduction then builds a complete dependent modal family
inside the requested focus subobject, retaining the actual matched captures.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated StructuralInputs structuralDeclaration structuralInputSort structuralOutputSort)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema TypeCode Evidence TypedRequest)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (relyMeaning continuationMeaning)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (Code LeafCodes Carries Kinded ClassifiedCode)
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes
open ModalHypercube (HSort)

/-- This law concerns the primitive native interpretation of an authored
constructor and its ordered typed arguments. It contains no generated code. -/
def OperationClosed {generated : Generated} (model : Model generated) : Prop :=
  ∀ bound (index : Fin generated.snapshot.language.terms.length)
    (value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index)),
    (∀ position, (model bound).sortDomain (structuralDeclaration generated index).params[position].typeExpr
      (structuralInputSort generated index position)
      (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))) →
    (model bound).sortDomain (.base (structuralDeclaration generated index).category)
      (structuralOutputSort generated index) value.pattern

/-- The model interprets actual equation generators, rather than assuming
invariance of every generated judgment as a field. -/
def EquationsInterpreted {generated : Generated} (model : Model generated) : Prop :=
  ∀ bound carrier sort source (receipt : GeneralEquationJobs.Receipt),
    GeneralEquationJobs.Completion generated.plan bound carrier source receipt →
    ((model bound).sortDomain carrier sort source ↔
      (model bound).sortDomain carrier sort receipt.target)

theorem equation_sort_transport {generated : Generated} {model : Model generated}
    (interpreted : EquationsInterpreted model) (bound : List TypeExpr) (carrier : TypeExpr) (sort : HSort)
    {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound carrier) first second) :
    (model bound).sortDomain carrier sort first ↔ (model bound).sortDomain carrier sort second := by
  induction related with
  | rel first second equation =>
      obtain ⟨receipt, complete, endpoint⟩ := equation
      exact endpoint ▸ interpreted bound carrier sort first receipt complete
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- M-INTRO for structural formers derives the output sort from the actual
operation law and each input certificate. Output membership is not a premise. -/
theorem structural_intro_from_inputs {generated : Generated} {model : Model generated}
    (closed : OperationClosed model) {bound : List TypeExpr}
    (index : Fin generated.snapshot.language.terms.length) (inputs : StructuralInputs generated bound index)
    (value : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
      (structuralDeclaration generated index))
    (arguments : ∀ position, (restrictCode (model bound) (inputs position)).meaning
      (value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt))) :
    (structuralCode (model bound) index inputs).meaning value.pattern :=
  structural_intro (model bound) index inputs value
    (closed bound index value (fun position => (arguments position).1)) arguments

theorem classified_meaning_in_model {generated : Generated} {model : Model generated}
    (closed : OperationClosed model) (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafInterpretation : ∀ index term, (leaves index).2.2.meaning term →
      (model bound).sortDomain (leaves index).1 (leaves index).2.1 term)
    (expression : Code generated.snapshot.language) :
    ∀ carrier sort, Carries (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.leafCarriers leaves) expression carrier →
      Kinded generated.vertex.2 (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.leafSorts leaves) expression sort →
      ∀ term, Mettapedia.OSLF.NativeTypes.SortProfiles.Source.meaning generated bound leaves expression term →
        (model bound).sortDomain carrier sort term := by
  induction expression with
  | variableCode index =>
      intro carrier sort carried formed term inhabited
      cases carried
      cases formed
      exact leafInterpretation index term inhabited
  | constructor index children ih =>
      intro carrier sort carried formed term inhabited
      cases carried with
      | constructor _ _ childrenCarried =>
        cases formed with
        | constructor _ _ childrenFormed =>
          obtain ⟨_, value, related, arguments⟩ := inhabited
          apply (equation_sort_transport equations bound _ _ related).mpr
          apply closed bound index value
          intro position
          exact ih position _ _ (childrenCarried position) (childrenFormed position) _ (arguments position)

theorem classified_code_in_model {generated : Generated} {model : Model generated}
    (closed : OperationClosed model) (equations : EquationsInterpreted model)
    {bound : List TypeExpr} {leaves : LeafCodes generated bound}
    (leafInterpretation : ∀ index term, (leaves index).2.2.meaning term →
      (model bound).sortDomain (leaves index).1 (leaves index).2.1 term)
    {carrier : TypeExpr} {sort : HSort} (code : ClassifiedCode generated bound leaves carrier sort)
    {term : Pattern} (inhabited : code.code.meaning term) :
    (model bound).sortDomain carrier sort term :=
  classified_meaning_in_model closed equations leafInterpretation code.expression _ _
    code.carrierFormation code.universeFormation term ((code.meaningComparison term).mp inhabited)

theorem lifted_request {generated : Generated} {schema : Schema generated.plan}
    {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters))
    {anchor assignment : Assignment}
    (request : TypedRequest schema
      (relyMeaning (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.nativeModalInputs (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs inputs)).1)
      anchor assignment) : TypedRequest schema (relyMeaning inputs.1) anchor assignment := by
  refine ⟨?_, request.2⟩
  intro name present
  obtain ⟨value, found, named, meaningful⟩ := request.1 name present
  refine ⟨value, found, named, ?_⟩
  exact (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.lifted_rely_readout (inputs.1 ⟨name, named⟩) value).mp meaningful

/-- Lifting input codes to classifier syntax does not replace the response
family or the origins stored in any actual primitive receipt. -/
def liftEvidence {generated : Generated} {schema : Schema generated.plan}
    {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)) {term : Pattern}
    (implementation : Evidence schema (relyMeaning inputs.1) (continuationMeaning inputs.2) term) :
    Evidence schema
      (relyMeaning (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.nativeModalInputs (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs inputs)).1)
      (continuationMeaning (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.nativeModalInputs (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs inputs)).2)
      term where
  carrier := implementation.carrier
  anchor := implementation.anchor
  anchorTyped := implementation.anchorTyped
  anchorPresent := implementation.anchorPresent
  respond assignment request := implementation.respond assignment (lifted_request inputs request)

theorem lifted_evidence_keeps_response {generated : Generated} {schema : Schema generated.plan}
    {parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema}
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters)) {term : Pattern}
    (implementation : Evidence schema (relyMeaning inputs.1) (continuationMeaning inputs.2) term)
    (assignment : Assignment)
    (request : TypedRequest schema
      (relyMeaning (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.nativeModalInputs (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs inputs)).1)
      implementation.anchor assignment) :
    ((liftEvidence inputs implementation).respond assignment request).receipt =
      (implementation.respond assignment (lifted_request inputs request)).receipt := rfl

/-- Modal introduction consumes actual computed source admission and dependent
continuation certificates. Its focus sort follows from a classified structural
expression in the operation-closed native model. -/
def introduce {generated : Generated} {model : Model generated}
    (closed : OperationClosed model) (equations : EquationsInterpreted model)
    {schema : Schema generated.plan} (parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema)
    (computed : generated.modalParameters? schema = some parameters)
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters))
    {leaves : LeafCodes generated schema.focusBound}
    (leafInterpretation : ∀ index term, (leaves index).2.2.meaning term →
      (model schema.focusBound).sortDomain (leaves index).1 (leaves index).2.1 term)
    (focusCode : ClassifiedCode generated schema.focusBound leaves schema.focusCarrier parameters.output)
    {term : Pattern} (focusReading : focusCode.code.meaning term)
    (anchor : Assignment)
    (anchorTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment generated.plan) schema.context anchor)
    (anchorPresent : ∀ name ∈ schema.matchedNames, ∃ value, lookup anchor name = some value)
    (focus : ∀ assignment, TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) anchor assignment →
      Mettapedia.OSLF.NativeTypes.Modal.Instantiation.FocusInstance schema.operation schema.declaration.rule
        schema.declaration.binding.spec schema.bound.length .left assignment [] 0
        schema.declaration.rule.left schema.position term)
    (choices : ∀ assignment, TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) anchor assignment →
      List Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.BagChoice)
    (accepted : ∀ assignment, ∀ request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) anchor assignment,
      Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.baseIntroductions schema assignment (choices assignment request) ≠ [])
    (certificate : ∀ assignment,
      TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1)) anchor assignment →
      ∀ target, schema.rhs? assignment = some target →
        Mettapedia.OSLF.NativeTypes.Modal.Rules.substituteContinuation
          (continuationMeaning (restrictContinuations model inputs.2)) assignment target) :
    {_implementation : Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
      (continuationMeaning (restrictContinuations model inputs.2)) term //
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.form model parameters computed inputs).code.meaning term} := by
  let implementation := Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.m_intro_computed
    (focusCode.code.bounded term focusReading) anchor anchorTyped anchorPresent focus choices accepted certificate
  refine ⟨implementation, classified_code_in_model closed equations leafInterpretation focusCode focusReading, ?_⟩
  apply (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classifiedModalCode parameters computed
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.restrictInputs model inputs))).meaningComparison term |>.mpr
  exact ⟨liftEvidence (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.restrictInputs model inputs) implementation⟩

theorem generated_m_intro {generated : Generated} {model : Model generated}
    (closed : OperationClosed model) (equations : EquationsInterpreted model)
    {schema : Schema generated.plan} (parameters : Mettapedia.OSLF.NativeTypes.Generation.ModalParameters schema)
    (computed : generated.modalParameters? schema = some parameters)
    (inputs : Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema (some parameters))
    {leaves : LeafCodes generated schema.focusBound}
    (leafInterpretation : ∀ index term, (leaves index).2.2.meaning term →
      (model schema.focusBound).sortDomain (leaves index).1 (leaves index).2.1 term)
    (focusCode : ClassifiedCode generated schema.focusBound leaves schema.focusCarrier parameters.output)
    {term : Pattern} (focusReading : focusCode.code.meaning term)
    (implementation : Evidence schema (relyMeaning (restrictRelyCodes model inputs.1))
      (continuationMeaning (restrictContinuations model inputs.2)) term) :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.form model parameters computed inputs).code.meaning term := by
  refine ⟨classified_code_in_model closed equations leafInterpretation focusCode focusReading, ?_⟩
  apply (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classifiedModalCode parameters computed
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.liftModalInputs (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.restrictInputs model inputs))).meaningComparison term |>.mpr
  exact ⟨liftEvidence (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.restrictInputs model inputs) implementation⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction
