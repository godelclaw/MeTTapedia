import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.SourceProfileModels

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

def verdicts : List (String × Bool) :=
  [("formula-readback/checked-reflexivity",(read? after 0 formula).isSome),
   ("formula-readback/changed-conclusion-refused",(read? after 0 (.eq value otherValue)).isNone),
   ("formula-readback/hypotheses-retained",!matchesB conditionalFact formula),
   ("formula-readback/uninterpreted-equality-refused",(read? after 0 uninterpretedEquality).isNone),
   ("formula-readback/absent-cache-refused",(read? after 1 formula).isNone)]

#print axioms cached_translation
#print axioms reversed_formula_translation
#print axioms exact_reflexivity_statement
#print axioms received_model
#print axioms same_reverse_source
#print axioms uninterpreted_equality_refused

end Mettapedia.Languages.HOLLight.ExactFormulaReadback.Controls
