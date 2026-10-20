import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSelectedTypingControls
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppendPolicy

/-! Selected input/output checking and the live emitted module share one policy. -/

open Mettapedia.GSLT.LanguageDef IndexedInductive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies

namespace SelectedInputs

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Guest.AppendTyping.Selected.Controls
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.IndexedInductiveAppend

theorem emitted_instance :
    ∃ proposed, AppendSource.propose .declaredNullary AppendSource.IndexedNatVecAppend.module = some proposed ∧
      FormationSensitive.Judgment Guest.AppendTyping.Selected.rules .nil
        (Declaration.IndexedFamily.applyArgs proposed.appendFunction
          [natTm, Guest.VectorMeaning.numeral left.size, Guest.VectorMeaning.numeral right.size,
            VectorArray.quoteArray natTm Guest.VectorMeaning.numeral left,
            VectorArray.quoteArray natTm Guest.VectorMeaning.numeral right]) resultType ∧
      Guest.AppendMeaning.ProgramExecutes
        (Declaration.IndexedFamily.applyArgs proposed.appendFunction
          [natTm, Guest.VectorMeaning.numeral left.size, Guest.VectorMeaning.numeral right.size,
            VectorArray.quoteArray natTm Guest.VectorMeaning.numeral left,
            VectorArray.quoteArray natTm Guest.VectorMeaning.numeral right])
        (VectorArray.quoteArray natTm Guest.VectorMeaning.numeral (left ++ right)) ∧
      FormationSensitive.Judgment Guest.AppendTyping.Selected.rules .nil
        (VectorArray.quoteArray natTm Guest.VectorMeaning.numeral (left ++ right)) resultType :=
  Policy.emitted_selected_contract _ _ Policy.actual_emitted
    natTm Guest.VectorMeaning.numeral natural_element payload_typed left right

#print axioms emitted_instance

end SelectedInputs

def main : IO Unit := do
  let controls := Guest.AppendTyping.Selected.Controls.verdicts
  for (label, accepted) in controls do
    unless accepted do throw (IO.userError s!"Selected input contract failed: {label}")
  IO.println s!"Selected input contracts: {controls.length}/{controls.length}; natural-only checking; original operational path"
