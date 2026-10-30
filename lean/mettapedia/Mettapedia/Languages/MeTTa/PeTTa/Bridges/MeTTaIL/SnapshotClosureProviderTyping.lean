import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureProviderExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotRows

/-! Native snapshot row validation realizes the independent typing judgment.
Datalog preparation supplies well-formed, unambiguous signatures, so its
row-validation result is exactly the full provider-closure check. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem rowsAccepted_iff_typed (language : LanguageDef) (free : List (String × TypeExpr))
    (bound : List TypeExpr) (signatures : List Signature) (rows : List ProviderRow) :
    rowsAccepted language free bound signatures rows = true ↔
      ∀ row ∈ rows, ∃ signature,
        GeneralPremise.signature? ⟨signatures,[],[]⟩ row.relation row.values.length = some signature ∧
        RowTyped language (FreeTypeContext.ofList free) bound signature row := by
  unfold rowsAccepted
  rw [List.all_eq_true]
  constructor
  · intro accepted row member
    have checked := accepted row member
    cases found : GeneralPremise.signature? ⟨signatures,[],[]⟩ row.relation row.values.length with
    | none => simp [found] at checked
    | some signature =>
      exact ⟨signature,rfl,checkRow_sound (by simpa only [found] using checked)⟩
  · intro typed row member
    obtain ⟨signature,found,valid⟩ := typed row member
    simpa only [found] using checkRow_complete valid

private theorem ofList_eq_find (entries : List (String × TypeExpr)) :
    FreeTypeContext.ofList entries = fun name => (entries.find? (·.1 == name)).map Prod.snd := by
  funext name
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key,type⟩
    by_cases same : key = name
    · simp [FreeTypeContext.ofList,same]
    · simp [FreeTypeContext.ofList,same,ih]

theorem snapshot_closed_eq_rowsAccepted (prepared : Executable.Prepared) (known : List Pattern) :
    ClosureMachine.closed prepared known =
      rowsAccepted prepared.compiled (Executable.freeTypes prepared.vocabulary) []
        (Executable.snapshot prepared known).provider.signatures
        (Executable.snapshot prepared known).provider.rows := by
  have free : (Executable.snapshot prepared known).free = FreeTypeContext.ofList
      (Executable.freeTypes prepared.vocabulary) := (ofList_eq_find _).symm
  unfold ClosureMachine.closed GeneralPremise.checkProviderClosed
  dsimp only
  rw [Executable.snapshot_signature_modes]
  simp only [Executable.snapshot_signature_keys_nodup,decide_true,Bool.true_and]
  unfold rowsAccepted
  apply congrArg (fun predicate => (Executable.snapshot prepared known).provider.rows.all predicate)
  funext row
  rw [GeneralPremise.signature_congr (before := (Executable.snapshot prepared known).provider)
    (after := ⟨(Executable.snapshot prepared known).provider.signatures,[],[]⟩) rfl]
  rw [free]
  rfl

theorem snapshot_check_rows_returns (state : State) (prepared : Executable.Prepared) (known : List Pattern) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:check-rows"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm prepared.compiled.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm (Executable.freeTypes prepared.vocabulary)),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm []),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.signatureTerm
           (Executable.snapshot prepared known).provider.signatures),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm
           (Executable.snapshot prepared known).provider.rows)]) state
      (Effects.boolean (ClosureMachine.closed prepared known)) := by
  rw [snapshot_closed_eq_rowsAccepted]
  exact check_rows_returns state prepared.compiled (Executable.freeTypes prepared.vocabulary) [] _ _

#print axioms rowsAccepted_iff_typed
#print axioms snapshot_closed_eq_rowsAccepted
#print axioms snapshot_check_rows_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
