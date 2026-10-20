import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendChecking

/-!
# Generated-policy admission of the append specialization

The source proposal checked by the generated declaration policy is the same
proposal whose core the specialization recognizes. The selected policy licenses
the natural computation rows for checking. It does not authorize arbitrary
vector computation or replace the separate reference execution comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend.Policy

open Mettapedia.GSLT.LanguageDef IndexedInductive
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

def emit? (input : ModuleSource.Module) : Option String :=
  if AppendChecking.replaySource AppendChecking.naturalOnly input then
    IndexedInductiveAppend.emit? input
  else none

/-- Both checks refer to the actual producer output, not independently chosen
terms with the same type. The source is still an untrusted proposal producer. -/
theorem emitted_contract (input : ModuleSource.Module) (text : String)
    (emitted : emit? input = some text) :
    text = source.text ∧ ∃ proposed,
      AppendSource.propose .declaredNullary input = some proposed ∧
      proposed.appendFunction = Programs.appendTerm ∧
      proposed.addition = Programs.add (.var 1) (.var 0) ∧
      FormationSensitive.Judgment
        (Declaration.extendRules Tower.rules
          (AppendChecking.generatedSignature AppendChecking.naturalOnly))
        .nil proposed.appendFunction Programs.appendType := by
  unfold emit? at emitted
  split at emitted
  · rename_i checked
    obtain ⟨supported, sameText⟩ := emitted_source input text emitted
    obtain ⟨proposed, found, core, addition, _⟩ := supports_core input supported
    obtain ⟨checkedProposal, checkedFound, typed⟩ :=
      AppendChecking.replaySource_sound AppendChecking.naturalOnly input checked
    have same : checkedProposal = proposed := Option.some.inj (checkedFound.symm.trans found)
    subst checkedProposal
    exact ⟨sameText, proposed, found, core, addition, typed⟩
  · cases emitted

theorem actual_emitted :
    emit? AppendSource.IndexedNatVecAppend.module = some source.text := by
  have accepted := AppendChecking.replay_naturalOnly
  change AppendChecking.replaySource AppendChecking.naturalOnly
    AppendSource.IndexedNatVecAppend.module = true at accepted
  simp only [emit?, accepted, ↓reduceIte]
  exact IndexedInductiveAppend.actual_emitted

theorem refused_check (input : ModuleSource.Module)
    (refused : AppendChecking.replaySource AppendChecking.naturalOnly input = false) :
    emit? input = none := by
  simp [emit?, refused]

theorem refused_core (input : ModuleSource.Module) (refused : supports input = false) :
    emit? input = none := by
  simp [emit?, IndexedInductiveAppend.emit?, refused]

/-- Actual represented arguments and the canonical output use the emitted
function's natural-only checker. The forward execution uses the original
operational rules. No extra checking permission is inferred from that path. -/
theorem emitted_selected_contract (input : ModuleSource.Module) (text : String)
    (emitted : emit? input = some text) (element : Tower.Tm 0)
    {A : Type} (payload : A → Tower.Tm 0)
    (elementTyped : Guest.AppendTyping.Selected.Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Guest.AppendTyping.Selected.Typed .nil (payload value) element)
    (left right : Array A) :
    ∃ proposed, AppendSource.propose .declaredNullary input = some proposed ∧
      FormationSensitive.Judgment Guest.AppendTyping.Selected.rules .nil
        (Declaration.IndexedFamily.applyArgs proposed.appendFunction
          [element, Guest.VectorMeaning.numeral left.size, Guest.VectorMeaning.numeral right.size,
            VectorArray.quoteArray element payload left, VectorArray.quoteArray element payload right])
        (vecApp element (Programs.add
          (Guest.VectorMeaning.numeral left.size) (Guest.VectorMeaning.numeral right.size))) ∧
      Guest.AppendMeaning.ProgramExecutes
        (Declaration.IndexedFamily.applyArgs proposed.appendFunction
          [element, Guest.VectorMeaning.numeral left.size, Guest.VectorMeaning.numeral right.size,
            VectorArray.quoteArray element payload left, VectorArray.quoteArray element payload right])
        (VectorArray.quoteArray element payload (left ++ right)) ∧
      FormationSensitive.Judgment Guest.AppendTyping.Selected.rules .nil
        (VectorArray.quoteArray element payload (left ++ right))
        (vecApp element (Programs.add
          (Guest.VectorMeaning.numeral left.size) (Guest.VectorMeaning.numeral right.size))) := by
  obtain ⟨_, proposed, found, core, _, _⟩ := emitted_contract input text emitted
  refine ⟨proposed, found, ?_⟩
  rw [core]
  exact VectorArray.compiled_selected_contract Programs.appendTerm AppendSource.append_matches_reference
    element payload elementTyped payloadTyped left right

theorem emitted_executes (input : ModuleSource.Module) (text : String)
    (emitted : emit? input = some text) (element : Tower.Tm 0)
    {A : Type} (payload : A → Tower.Tm 0)
    (elementTyped : Guest.AppendTyping.Selected.Typed .nil element (sortTm elementLevel))
    (payloadTyped : ∀ value, Guest.AppendTyping.Selected.Typed .nil (payload value) element)
    (left right : Array A) :
    ∃ proposed, AppendSource.propose .declaredNullary input = some proposed ∧
      Guest.AppendMeaning.ProgramExecutes
        (Declaration.IndexedFamily.applyArgs proposed.appendFunction
          [element, Guest.VectorMeaning.numeral left.size, Guest.VectorMeaning.numeral right.size,
            VectorArray.quoteArray element payload left, VectorArray.quoteArray element payload right])
        (VectorArray.quoteArray element payload (left ++ right)) := by
  obtain ⟨proposed, found, _, path, _⟩ :=
    emitted_selected_contract input text emitted element payload elementTyped payloadTyped left right
  exact ⟨proposed, found, path⟩

#print axioms emitted_contract
#print axioms emitted_selected_contract
#print axioms emitted_executes
#print axioms actual_emitted

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend.Policy
