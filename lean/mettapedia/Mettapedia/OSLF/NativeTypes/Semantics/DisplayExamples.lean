import Mettapedia.OSLF.NativeTypes.Semantics.Display
import Mettapedia.OSLF.NativeTypes.Instances.Rho.UnrestrictedContextControl
import Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts
import Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenterControls

open Mettapedia.OSLF.Framework

/-!
# Run the authored native-type generator on three languages

The executable entry point prints the same generated catalogue and checked
frontier for a literal-channel COMM companion with authored parallel
contexts, annotated scoped beta and an authored F/G law. The COMM profile
selects no equations or canonical-channel comparison.
It also prints a paused query, a genuine negative query, a refused connective,
and rejected/unresolved selected vertices.

Run this module with `lake env lean` to execute `main` below. The output is a
presentation of receipt-bearing native queries, not a full-family inference
procedure for arbitrary dependent modalities.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.DisplayExamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Semantics.Display

def anyTarget {request : GeneralOccurrenceFrontier.Request} : InvariantTest request :=
  {accepts := fun _ => true, invariant := fun _ _ _ => rfl}

def noTarget {request : GeneralOccurrenceFrontier.Request} : InvariantTest request :=
  {accepts := fun _ => false, invariant := fun _ _ _ => rfl}

def rhoRun (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated.searchModal [] (.base "Proc")
    GeneralRho.FrontierControls.rootSource .possibility anyTarget budget

def rhoUniversalRun :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated.searchModal [] (.base "Proc")
    GeneralRho.FrontierControls.rootSource .outgoingUniversal noTarget 40

def rhoOutput (budget : Nat) : QueryView :=
  runNative Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated [] (.base "Proc")
    GeneralRho.FrontierControls.rootSource .possibility anyTarget budget
def rhoUniversalOutput : QueryView :=
  runNative Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated [] (.base "Proc")
    GeneralRho.FrontierControls.rootSource .outgoingUniversal noTarget 40

def rhoParallelOutput : QueryView :=
  runNative Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated [] (.base "Proc")
    GeneralRho.FrontierControls.parallelSource .possibility anyTarget 60

/-- An unfinished negative probe stays unknown even where the separate
whole-profile semantic theorem proves that this constructor cannot step. -/
def rhoGuardedPausedOutput : QueryView :=
  runNative Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated [] (.base "Proc")
    Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.guardedSource .possibility anyTarget 3

def rhoDuplicateOutput : QueryView :=
  collectNative Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated [] (.base "Proc")
    GeneralRho.FrontierControls.duplicates .possibility anyTarget 75

def betaRun (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.generated.checkAnnotatedModalInstance
    Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.checked
    Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.codes
    Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.decisions
    Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.supplied Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.source budget 0

def betaOutput (budget : Nat) : Except ModalInstanceIssue QueryView :=
  (betaRun budget).map (instanceView budget)

def betaMissingAssignment :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.generated.checkAnnotatedModalInstance
    Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.checked
    Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.codes
    Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.decisions [] Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.source 40 0

def betaRefusedConnective :=
  Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.generated.checkFormula [] Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.term
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.source (.neg .top) 40

/-- The open argument is well scoped in its explicit ambient sort context.
No second executor or hand-specified occurrence list is introduced. -/
def centerSource : Pattern := .apply "F" [.bvar 0]

def centerRun :=
  Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.accepted.checkModal
    [Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier] Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier
    centerSource .possibility anyTarget 80

def centerOutput : QueryView :=
  runNative Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.accepted
    [Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier] Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier
    centerSource .possibility anyTarget 80

def rejectedCenterRun :=
  Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.rejected.checkModal
    [Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier] Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier
    centerSource .possibility anyTarget 80

def guardedCenterRun :=
  Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.guarded.checkModal
    [Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier] Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.carrier
    centerSource .possibility anyTarget 80

def renderBeta (title : String) (result : Except ModalInstanceIssue QueryView) : String :=
  match result with
  | .ok output => renderQuery title output
  | .error issue => renderInstanceError title issue

def main : IO Unit := do
  IO.println "=== Rho-signature COMM companion: literal channels, authored parallel contexts ==="
  IO.println (renderCatalogue (catalogue Mettapedia.OSLF.NativeTypes.Instances.Rho.LiteralChannelContexts.generated))
  IO.println (renderQuery "Companion COMM has an outgoing successor" (rhoOutput 40))
  IO.println (renderQuery "Authored parallel context permits COMM" rhoParallelOutput)
  IO.println (renderQuery "Input-guard query with unfinished coverage" rhoGuardedPausedOutput)
  IO.println (renderQuery "Every companion COMM successor satisfies false" rhoUniversalOutput)
  IO.println (renderQuery "COMM before any execution work" (rhoOutput 0))
  IO.println (renderQuery "Equal endpoints retain two native COMM origins" rhoDuplicateOutput)
  IO.println "\n=== Annotated beta: generated dependent modal instance ==="
  IO.println (renderCatalogue (catalogue Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.generated))
  IO.println (renderBeta "Beta reaches its specified substituted RHS" (betaOutput 40))
  IO.println (renderBeta "Beta with an exhausted source budget" (betaOutput 0))
  IO.println (renderBeta "Beta with missing actual assignments"
    (betaMissingAssignment.map (instanceView 40)))
  IO.println (renderQuery "Negation outside the selected finite-limit vocabulary"
    (queryView .structuralFormula 40 betaRefusedConnective))
  IO.println "\n=== Authored F/G theory: proper generated center ==="
  IO.println (renderCatalogue (catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.accepted))
  IO.println (renderQuery "F/G execution at an admitted vertex" centerOutput)
  IO.println (renderQuery "F/G query at a rejected vertex"
    (queryView .outgoingPossibility 80 rejectedCenterRun))
  IO.println (renderQuery "F/G guarded source retains unresolved admission"
    (queryView .outgoingPossibility 80 guardedCenterRun))
  IO.println ("Rejected vertex joint status: " ++ renderAdmission
    (catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.rejected).jointAdmission)
  IO.println ("Guarded vertex joint status: " ++ renderAdmission
    (catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.guarded).jointAdmission)
  IO.println ("Guarded source diagnostics: " ++ String.intercalate "; "
    ((catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.guarded).equationDiagnostics.map renderDiagnostic))

#guard (rhoOutput 40).result == .decided true
#guard rhoUniversalOutput.result == .decided false
#guard rhoParallelOutput.result == .decided true
#guard (rhoParallelOutput.receipts.map ReceiptView.position) == [[1]]
#guard rhoGuardedPausedOutput.result == .unknown
#guard rhoGuardedPausedOutput.receipts.isEmpty
#guard !rhoGuardedPausedOutput.coverageCertified
#guard (rhoOutput 0).result == .unknown
#guard (betaOutput 40).map (fun output => output.result) == .ok (.decided true)
#guard (betaOutput 0).map (fun output => output.result) == .ok .unknown
#guard betaMissingAssignment.map (fun output => output.result) == .error .unavailableRightHandSide
#guard betaRefusedConnective.result == .illFormed (.unsupportedConnective .negation)
#guard centerOutput.result == .decided true
#guard rejectedCenterRun.result == .rejectedCube
#guard guardedCenterRun.result == .unknown
#guard (catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.accepted).jointAdmission == some true
#guard (catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.rejected).jointAdmission == some false
#guard (catalogue Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.guarded).jointAdmission == none
#guard (rhoOutput 40).selectedNativeReceipts == some 1
#guard (rhoOutput 0).selectedNativeReceipts == some 0
#guard rhoUniversalOutput.selectedNativeReceipts == some 0
#guard centerOutput.selectedNativeReceipts == some 1
#guard rhoDuplicateOutput.result == .decided true
#guard rhoDuplicateOutput.receipts.length == 2
#guard rhoDuplicateOutput.selectedNativeReceipts == some 2
#guard (rhoDuplicateOutput.receipts.map ReceiptView.target).eraseDups.length == 1
#guard (rhoDuplicateOutput.receipts.map ReceiptView.matcherChoices).eraseDups.length == 2

theorem actual_beta_positive :
    (betaRun 40).map (fun result => result.result) = .ok (.decided true) :=
  Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.actual_beta_answer

theorem actual_beta_paused :
    (betaRun 0).map (fun result => result.result) = .ok .unknown :=
  Mettapedia.OSLF.NativeTypes.Generation.Annotated.BetaChecking.paused_beta_unknown

theorem displayed_center_is_nonempty_and_proper :
    (Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.center
      Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.snapshot
      Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.fragment
      Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.logic).Nonempty ∧
    Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.center
      Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.snapshot
      Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.fragment
      Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.logic ≠ Finset.univ :=
  Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls.proper_nonempty_actual_generated_center

#eval main

end Mettapedia.OSLF.NativeTypes.Semantics.DisplayExamples
