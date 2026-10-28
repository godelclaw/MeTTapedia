import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSource
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.AppendDefinitionCompletion

/-!
# The maintained source append programme reaches checked definition completion

The existing source producer proposes a closed body from the complete module.
The declaration checker then checks that body and its specified dependent
type before returning a definition entry. The retained certificate is an
ordinary input, not a privilege attached to the producer's name.

The selected textual module has a proved comparison with the independent
recursive append program. For other modules, success below certifies the
proposed body's typing; source-equation fidelity additionally needs the
corresponding producer comparison.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendSourceCompletion

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration
open OperationSource

local instance : DecidableRel Programs.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred Programs.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (Programs.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel Programs.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel Programs.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

local instance : DecidableRel AppendDefinitionCompletion.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def completeProposal? (policy : NamePolicy) (source : ModuleSource.Module)
    (name : DeclName) (certificate : AppendDefinitionCompletion.EntryCode) :
    Option (DeclName × Entry Tower.Head) := do
  let proposal ← AppendSource.propose policy source
  if checkComplete Programs.rules Programs.decoder []
      (name, Programs.appendType) (name, proposal.appendFunction) certificate then
    complete? (name, Programs.appendType) (name, proposal.appendFunction)
  else none

theorem completeProposal_sound (policy : NamePolicy) (source : ModuleSource.Module)
    (name : DeclName) (certificate : AppendDefinitionCompletion.EntryCode)
    (entry : DeclName × Entry Tower.Head)
    (completed : completeProposal? policy source name certificate = some entry) :
    ∃ proposal, AppendSource.propose policy source = some proposal ∧
      entry = (name, ⟨Programs.appendType, some proposal.appendFunction⟩) ∧
      DeclarationAdmissionReplay.Admitted Programs.rules [] [entry] := by
  unfold completeProposal? at completed
  cases proposed : AppendSource.propose policy source with
  | none => simp [proposed] at completed
  | some proposal =>
      simp only [proposed, Bind.bind, Option.bind] at completed
      split at completed
      · rename_i accepted
        have shape := (complete?_eq_some_iff _ _ _).mp completed
        refine ⟨proposal, rfl, shape.2, ?_⟩
        rw [shape.2]
        exact (checkComplete_admitted Programs.rules Programs.decoder accepted).2
      · cases completed

def sourceBodyCompletion : Bool :=
  match AppendSource.proposedAppend with
  | none => false
  | some body => checkComplete Programs.rules Programs.decoder []
      (AppendDefinitionCompletion.name, Programs.appendType)
      (AppendDefinitionCompletion.name, body) AppendDefinitionCompletion.certificate

theorem source_body_checked : sourceBodyCompletion = true := by
  rw [sourceBodyCompletion, AppendSource.append_matches_reference]
  exact AppendDefinitionCompletion.accepted_true

/-- The actual named source body yields the already qualified declaration
entry, including its full dependent type and recursive implementation. -/
theorem source_body_entry :
    (AppendSource.proposedAppend.bind fun body =>
      complete? (AppendDefinitionCompletion.name, Programs.appendType)
        (AppendDefinitionCompletion.name, body)) =
      some (AppendDefinitionCompletion.name, ⟨Programs.appendType, some Programs.appendTerm⟩) := by
  rw [AppendSource.append_matches_reference]
  simp [complete?]

/-- Ordinary calls through the completed definition recover the recursive
program obtained from the source, for every scoped argument assignment. -/
theorem source_call_checked {n : Nat} (element first second left right : Tower.Tm n) :
    (AppendDefinitionCompletion.callEvidence element first second left right).check
      AppendDefinitionCompletion.rules.headEq AppendDefinitionCompletion.decoder.decode
      (AppendDefinitionCompletion.call element first second left right)
      (Programs.append element first second left right) = true :=
  AppendDefinitionCompletion.call_checked element first second left right

def verdicts : List (String × Bool) :=
  ("source module body completes", sourceBodyCompletion) :: AppendDefinitionCompletion.verdicts

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, source_body_checked, AppendDefinitionCompletion.all_verdicts]

#print axioms completeProposal_sound
#print axioms source_body_checked
#print axioms source_body_entry
#print axioms source_call_checked

end Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendSourceCompletion
