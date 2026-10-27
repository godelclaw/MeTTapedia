import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.HOLLight.ConstructorPayloadGuards

/-!
# Exact formula readback controls on an accepted source replay

A registered reflexivity command supplies the positive cache entry. Changed
conclusions, retained hypotheses and absent cache entries are refused. A term
with an uninterpreted equality symbol has the same reversed source bytes as
primitive equality but is correctly refused by the fragment check.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExactFormulaReadback.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution SourceProfileModels

def sourceVariable : SourceVar := ⟨Name.global "readback_value",Ty.bool⟩
def source : CanonicalTerm := .free sourceVariable
def value : HOL.ClosedTerm Symbol .prop := .const (.variable sourceVariable (by simp [sourceVariable]))
def formula : HOL.ClosedFormula Symbol := .eq value value

theorem reflexivity_available : (checkRefl source).isSome = true := by decide +kernel
def reflexivity : Theorem := (checkRefl source).get reflexivity_available

def command : Registered.Command := .proof
  ⟨reflexivity,.inference (.refl source),[],("formula-readback",0)⟩
  (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)

theorem replay_available : (Registered.replayFrom policy
    (Registered.empty SourceProfile.primitiveContext) [command]).isSome = true := by decide +kernel

def after : Registered.State := (Registered.replayFrom policy
  (Registered.empty SourceProfile.primitiveContext) [command]).get replay_available

theorem replayed : Registered.replayFrom policy
    (Registered.empty SourceProfile.primitiveContext) [command] = some after :=
  (Option.some_get replay_available).symm

theorem reading_available : (read? after 0 formula).isSome = true := by decide +kernel
def reading : ReadFact after formula := (read? after 0 formula).get reading_available

theorem cached_translation : Translates [] reading.fact.sequent.concl.term .prop formula :=
  reading.translated

theorem reversed_formula_translation : Translates [] (ReverseTranslation.reverseTermOpen formula) .prop formula :=
  readable_translates formula (by decide +kernel)

theorem exact_reflexivity_statement : reflexivity.sequent.hyp = ∅ ∧
    Translates [] reflexivity.sequent.concl.term .prop formula :=
  matches_sound (by decide +kernel : matchesB reflexivity formula = true)

theorem received_model :
    ((sourceReplayFrame [command] after replayed).frame.model
      TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).models formula :=
  read_models _ _ _ formula reading

def otherValue : HOL.ClosedTerm Symbol .prop :=
  .const (.variable ⟨Name.global "different_value",Ty.bool⟩ (by simp))

theorem changed_conclusion_refused : (read? after 0 (.eq value otherValue)).isNone = true := by decide +kernel

def conditionalFact : Theorem := {reflexivity with sequent := {reflexivity.sequent with hyp := {source}}}

theorem retained_hypothesis_refused : matchesB conditionalFact formula = false := by decide +kernel

def uninterpretedEquality : HOL.ClosedFormula Symbol :=
  .app (.app (.const (.constant Const.equality (Ty.equality Ty.bool) (by simp [Ty.equality]))) value) value

theorem same_reverse_source : ReverseTranslation.reverseTermOpen uninterpretedEquality =
    ReverseTranslation.reverseTermOpen formula := rfl

theorem uninterpreted_equality_refused : (read? after 0 uninterpretedEquality).isNone = true := by decide +kernel

theorem absent_cache_refused : (read? after 1 formula).isNone = true := by decide +kernel

namespace GeneratedDefinition

open DefinitionAdapters ReverseTranslation

def body : HOL.ClosedTerm Symbol (ConstructorPayload.payload.arr .prop) :=
  HOL.FiniteConstructorEncoding.predicate (Const := Symbol) ConstructorPayload.signature

theorem body_symbols_readable : symbolsReadable body = true := by decide +kernel

theorem body_symbols_free : ReverseTranslation.EqualitySymbolFree body :=
  symbolsReadable_free body body_symbols_readable

def name : Name := Name.global "receivedConstructorPayloadImage"
def initial : Registered.State := Registered.empty SourceProfile.primitiveContext
def bodySource : SourceTerm := IndexedConstructorDefinitions.source body
def instances := ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature
def admission := admitConstantInTheory SourceProfile.primitiveContext instances name bodySource

set_option maxRecDepth 16384 in
theorem admission_available : admission.isSome = true := by decide +kernel

def result : ContextConstantDefinitionResult := admission.get admission_available

def installed : HOL.ClosedTerm Symbol (ConstructorPayload.payload.arr .prop) :=
  .const (.constant result.output.constant (reverseTy (ConstructorPayload.payload.arr .prop))
    (toHOL_reverseTy _))

def command : Registered.Command := IndexedConstructorDefinitions.command initial
  ("received-constructor-image", 0) name bodySource

set_option maxRecDepth 16384 in
theorem replay_available : (Registered.replayFrom policy initial [command]).isSome = true := by decide +kernel

def after : Registered.State := (Registered.replayFrom policy initial [command]).get replay_available

theorem replayed : Registered.replayFrom policy initial [command] = some after :=
  (Option.some_get replay_available).symm

set_option maxRecDepth 16384 in
theorem meaning_available : (readEquation? after 0 installed body).isSome = true := by decide +kernel

def reading : ReadMeaning after (.eq installed (HOL.ImpredicativeConnectives.expand body)) :=
  (readEquation? after 0 installed body).get meaning_available

theorem installed_body_meaning :
    ((sourceReplayFrame [command] after replayed).frame.model
      TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).denote
        installed (fun index => nomatch index) =
    ((sourceReplayFrame [command] after replayed).frame.model
      TypeFamilySemantics.Controls.initialOther (fun _ => TypeFamilySemantics.Controls.natural.{0})).denote
        body (fun index => nomatch index) :=
  readEquation_denote _ _ _ installed body reading

set_option maxRecDepth 16384 in
theorem changed_body_refused : (readEquation? after 0 installed (.lam .top)).isNone = true := by decide +kernel

theorem absent_definition_refused : (readEquation? after 1 installed body).isNone = true := by decide +kernel

end GeneratedDefinition

theorem meaning_uninterpreted_equality_refused :
    (readMeaning? after 0 uninterpretedEquality).isNone = true := by decide +kernel

theorem meaning_retained_hypothesis_refused : meaningMatchesB conditionalFact formula = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("formula-readback/checked-reflexivity",(read? after 0 formula).isSome),
   ("formula-readback/changed-conclusion-refused",(read? after 0 (.eq value otherValue)).isNone),
   ("formula-readback/hypotheses-retained",!matchesB conditionalFact formula),
   ("formula-readback/uninterpreted-equality-refused",(read? after 0 uninterpretedEquality).isNone),
   ("formula-readback/absent-cache-refused",(read? after 1 formula).isNone),
   ("formula-meaning/generated-definition",(readEquation? GeneratedDefinition.after 0 GeneratedDefinition.installed GeneratedDefinition.body).isSome),
   ("formula-meaning/changed-body-refused",(readEquation? GeneratedDefinition.after 0 GeneratedDefinition.installed (.lam .top)).isNone),
   ("formula-meaning/absent-definition-refused",(readEquation? GeneratedDefinition.after 1 GeneratedDefinition.installed GeneratedDefinition.body).isNone),
   ("formula-meaning/uninterpreted-equality-refused",(readMeaning? after 0 uninterpretedEquality).isNone),
   ("formula-meaning/hypotheses-retained",!meaningMatchesB conditionalFact formula)]

#print axioms cached_translation
#print axioms reversed_formula_translation
#print axioms exact_reflexivity_statement
#print axioms received_model
#print axioms same_reverse_source
#print axioms uninterpreted_equality_refused
#print axioms GeneratedDefinition.installed_body_meaning
#print axioms GeneratedDefinition.changed_body_refused
#print axioms meaning_uninterpreted_equality_refused

end Mettapedia.Languages.HOLLight.ExactFormulaReadback.Controls
