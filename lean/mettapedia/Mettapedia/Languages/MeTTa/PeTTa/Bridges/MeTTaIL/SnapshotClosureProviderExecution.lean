import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseQueryExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Lower
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProviderCongruence

/-! Row validation in the actual snapshot library reuses the established
signature and row-checker operations. Replacing a snapshot does not weaken
the check performed on each candidate provider row. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem signature_returns (state : State) (provider : ProviderSnapshot) (relation : String) (arity : Nat) :
    PureReturns runtime [] state
      (apply "gslt:premise:signature" [encoded (.string relation),number arity,
        encoded (PremiseOperationsExecution.GeneralExecution.providerTerm provider)]) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.signatureTerm
        (GeneralPremise.signature? provider relation arity))) := by
  have old := PremiseOperationsExecution.GeneralExecution.QueryLower.signature_returns [] state provider relation arity
    (encoded (.string relation)) (number arity)
    (encoded (PremiseOperationsExecution.GeneralExecution.providerTerm provider)) (by simp)
  have common : PureReturns CompleteExecution.descentLibrary.runtime [] state
      (apply "gslt:premise:signature" [encoded (.string relation),number arity,
        encoded (PremiseOperationsExecution.GeneralExecution.providerTerm provider)]) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.signatureTerm
        (GeneralPremise.signature? provider relation arity))) := by
    metta_lower ["relation","arity","provider"] old
  have runner := runner_from_base% ["relation","arity","provider"] common using RetainedMatchingWire.scopedPrimitive_agreement
  metta_lift checked ["relation","arity","provider"] runner

theorem check_row_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (signature : Signature) (row : ProviderRow) :
    PureReturns runtime [] state
      (apply "gslt:premise:check-row"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms),encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (PremiseOperationsExecution.GeneralExecution.signatureTerm signature),
         encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm row)]) state
      (Effects.boolean (GeneralPremise.checkRow language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound signature row)) := by
  have old := PremiseOperationsExecution.GeneralExecution.QueryLower.row_typed_returns [] state language free bound signature row
    (encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms)) (encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free))
    (encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound))
    (encoded (PremiseOperationsExecution.GeneralExecution.signatureTerm signature))
    (encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm row)) (by simp)
  have common : PureReturns CompleteExecution.descentLibrary.runtime [] state
      (apply "gslt:premise:check-row"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms),encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (PremiseOperationsExecution.GeneralExecution.signatureTerm signature),
         encoded (PremiseOperationsExecution.GeneralExecution.providerRowTerm row)]) state
      (Effects.boolean (GeneralPremise.checkRow language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound signature row)) := by
    metta_lower ["declarations","free","bound","signature","row"] old
  have runner := runner_from_base% ["declarations","free","bound","signature","row"] common using RetainedMatchingWire.scopedPrimitive_agreement
  metta_lift checked ["declarations","free","bound","signature","row"] runner

theorem length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  have runner := runner_from_base% ["items"]
    (CompleteExecution.complete_length_returns element state items) using RetainedMatchingWire.scopedPrimitive_agreement
  metta_lift checked ["items"] runner

def rowsAccepted (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (signatures : List Signature) (rows : List ProviderRow) : Bool :=
  rows.all fun row =>
    match GeneralPremise.signature? ⟨signatures,[],[]⟩ row.relation row.values.length with
    | none => false
    | some signature => GeneralPremise.checkRow language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound signature row

theorem check_rows_returns (state : State) (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (signatures : List Signature) (rows : List ProviderRow) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:check-rows"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.signatureTerm signatures),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm rows)]) state
      (Effects.boolean (rowsAccepted language free bound signatures rows)) := by
  induction rows with
  | nil =>
    metta_call checked
    metta_eval with checked unfolding [rowsAccepted]
  | cons row rest ih =>
    have length := length_returns InferenceCettaWire.encodePattern state row.values
    have signature := signature_returns state ⟨signatures,row :: rest,[]⟩ row.relation row.values.length
    have sameSignature : GeneralPremise.signature? ⟨signatures,row :: rest,[]⟩ row.relation row.values.length =
        GeneralPremise.signature? ⟨signatures,[],[]⟩ row.relation row.values.length := signature_congr rfl _ _
    rw [sameSignature] at signature
    cases selected : GeneralPremise.signature? ⟨signatures,[],[]⟩ row.relation row.values.length with
    | none =>
      rw [selected] at signature
      simp only [rowsAccepted,List.all_cons,selected,Bool.false_and]
      metta_call checked
      metta_eval [length,signature] with checked unfolding [rowsAccepted,selected,
        PremiseOperationsExecution.GeneralExecution.providerRowTerm,
        PremiseOperationsExecution.GeneralExecution.providerTerm,
        PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
        InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList]
    | some chosen =>
      rw [selected] at signature
      have rowCheck := check_row_returns state language free bound chosen row
      cases valid : GeneralPremise.checkRow language
          (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound chosen row <;>
        (rw [valid] at rowCheck
         simp only [rowsAccepted,List.all_cons,selected,valid,Bool.false_and,Bool.true_and]
         metta_call checked
         metta_eval [length,signature,rowCheck,ih] with checked unfolding [rowsAccepted,selected,valid,
           PremiseOperationsExecution.GeneralExecution.providerRowTerm,
           PremiseOperationsExecution.GeneralExecution.providerTerm,
           PremiseOperationsExecution.GeneralExecution.Base.patternsTerm,
           InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList])

#print axioms signature_returns
#print axioms check_row_returns
#print axioms check_rows_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
