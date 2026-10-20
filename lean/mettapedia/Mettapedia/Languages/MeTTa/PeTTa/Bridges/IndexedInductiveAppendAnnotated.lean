import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendPolicy
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedAppend

/-!
# Annotated authority for an accepted append specialization

The emitter's actual source proposal is passed to the existing bidirectional
annotator with the independently formed dependent function type. The owner's
typing and erasure theorems identify that result. The smaller typing policy
does not thereby acquire the vector computation permissions of a larger one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend.Annotated

open Mettapedia.GSLT.LanguageDef IndexedInductive
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Annotated
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

/-- The maintained annotator, with the actual selected expected type. -/
def annotate (term : Tower.Tm 0) : CTm Tower.Head 0 :=
  (elaborate (Programs.Annotated.church Programs.ComputationProfiles.naturalOnly).constantType
    Knowledge.empty (some Programs.Annotated.Append.appendFunctionType) none term).1

/-- The emitted bytes and the precise dependent checking subject travel
together. This record is not a serialized native-kernel proof. -/
structure Output where
  text : String
  sourceFunction : Tower.Tm 0
  annotation : CTm Tower.Head 0
  expectedType : CTm Tower.Head 0

def emit? (input : ModuleSource.Module) : Option Output := do
  let text ← Policy.emit? input
  let proposed ← AppendSource.propose .declaredNullary input
  return ⟨text, proposed.appendFunction, annotate proposed.appendFunction,
    Programs.Annotated.Append.appendFunctionType⟩

/-- Both judgments refer to the same accepted source function. No general
raw-to-annotated typing reflection or richer package admission is assumed. -/
theorem emitted_contract (input : ModuleSource.Module) (text : String)
    (emitted : Policy.emit? input = some text) :
    text = source.text ∧ ∃ proposed,
      AppendSource.propose .declaredNullary input = some proposed ∧
      CTyped (Programs.Annotated.church Programs.ComputationProfiles.naturalOnly) .nil
        (annotate proposed.appendFunction) Programs.Annotated.Append.appendFunctionType ∧
      (annotate proposed.appendFunction).erase = proposed.appendFunction ∧
      Programs.Annotated.Append.appendFunctionType.erase = Programs.appendType ∧
      annotate proposed.appendFunction = Programs.Annotated.Append.appendFunction := by
  obtain ⟨sameText, proposed, found, sameCore, _, _⟩ := Policy.emitted_contract input text emitted
  refine ⟨sameText, proposed, found, ?_, ?_, Programs.Annotated.Append.appendFunctionType_erases, ?_⟩
  all_goals rw [sameCore]
  · exact Programs.Annotated.Append.producedAppendFunction_typed _
      (by decide +kernel) (by decide +kernel)
  · change (Programs.Annotated.Append.producedAppendFunction _).erase = Programs.appendTerm
    rw [Programs.Annotated.Append.producedAppendFunction_exact]
    exact Programs.Annotated.Append.appendFunction_erases
  · exact Programs.Annotated.Append.producedAppendFunction_exact _

/-- Enlarging the declared computation permissions transports the same
annotated source function by the owner's two composed policy morphisms. -/
theorem emitted_full_policy (input : ModuleSource.Module) (text : String)
    (emitted : Policy.emit? input = some text) :
    ∃ proposed, AppendSource.propose .declaredNullary input = some proposed ∧
      CTyped (Programs.Annotated.church (fun _ => true)) .nil
        (annotate proposed.appendFunction) Programs.Annotated.Append.appendFunctionType := by
  obtain ⟨_, proposed, found, _, _, _, same⟩ := emitted_contract input text emitted
  refine ⟨proposed, found, ?_⟩
  rw [same]
  exact Programs.Annotated.Append.function_after_two_extensions

/-- Adding the checking subject preserves exactly the previously admitted
emitted bytes, including refusal. -/
theorem emit_text (input : ModuleSource.Module) :
    (emit? input).map Output.text = Policy.emit? input := by
  cases legacy : Policy.emit? input with
  | none => simp [emit?, legacy]
  | some text =>
      obtain ⟨_, proposed, found, _⟩ := Policy.emitted_contract input text legacy
      simp [emit?, legacy, found]

theorem output_sound (input : ModuleSource.Module) (output : Output)
    (emitted : emit? input = some output) :
    Policy.emit? input = some output.text ∧
    (∃ proposed, AppendSource.propose .declaredNullary input = some proposed ∧
      output.sourceFunction = proposed.appendFunction) ∧
    CTyped (Programs.Annotated.church Programs.ComputationProfiles.naturalOnly) .nil
      output.annotation output.expectedType ∧
    output.annotation.erase = output.sourceFunction ∧
    output.expectedType.erase = Programs.appendType ∧
    CTyped (Programs.Annotated.church (fun _ => true)) .nil
      output.annotation output.expectedType := by
  cases legacy : Policy.emit? input with
  | none => simp [emit?, legacy] at emitted
  | some text =>
      obtain ⟨_, proposed, found, typed, erases, typeErases, same⟩ :=
        emitted_contract input text legacy
      simp [emit?, legacy, found] at emitted
      subst output
      refine ⟨rfl, ⟨proposed, found, rfl⟩, typed, erases, typeErases, ?_⟩
      change CTyped _ .nil (annotate proposed.appendFunction) _
      rw [same]
      exact Programs.Annotated.Append.function_after_two_extensions

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend.Annotated
