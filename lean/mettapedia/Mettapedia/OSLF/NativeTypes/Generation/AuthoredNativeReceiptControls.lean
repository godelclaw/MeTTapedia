import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeReceiptChecking
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredControls
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeDisplay
import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecution

/-!
# Actual original executions checked in their generated native families

Every consumer uses the same installation, original scoped executor, authored
source decoder and generated frame checker. Schema indices and parameter
readouts come from the generated catalogue, including nonroot positions and
nonempty rely lists. Complete execution origins accompany each checked frame.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.ReceiptControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking
open NativeBindingEventAction (bound)
open RuleBinding ScopedRuleMatching
open CurriedBindingLanguage

structure ParameterReadout where
  name : String
  dependencies : List TypeExpr
  expected : TypeExpr
  value : Option ContextualValue
  deriving DecidableEq, Repr

structure FrameReadout where
  declaration : Nat
  ordinal : Nat
  position : List Nat
  focusBound : List TypeExpr
  source : Pattern
  focus : Pattern
  rely : List ParameterReadout
  matched : List ParameterReadout
  nativeChecks : List NativeLogic.CheckResult
  receipt : Payload
  deriving DecidableEq, Repr

def readParameter {plan : GeneralExecutionAdmission.Plan}
    {schema : Modal.Rules.Schema plan} {ambient : List String} {sort : String}
    (point : NativeBindingSchemaCaptures.Selected schema ambient sort)
    (slot : NativeEventParameters.Slot schema) : ParameterReadout :=
  ⟨slot.name, slot.dependencies, slot.expected,
    (NativeBindingSchemaCaptures.readSlot schema point slot).map Subtype.val⟩

def readFrame (installed : Installed) (index : Fin installed.operational.modal.length)
    {ambient : List String}
    (frame : NativeBindingSchemaFocus.Frame (installed.nativeSchema index)
      ambient (installed.nativeProgramSort index)) : FrameReadout where
  declaration := (installed.nativeSchema index).declaration.declarationIndex
  ordinal := (installed.nativeSchema index).ordinal
  position := (installed.nativeSchema index).position
  focusBound := (installed.nativeSchema index).focusBound
  source := toPattern frame.point.val.source
  focus := frame.focus
  rely := (List.finRange installed.operational.modal[index].rely.length).map fun parameter =>
    readParameter frame.point installed.operational.modal[index].rely[parameter].slot
  matched := (List.finRange installed.operational.modal[index].matched.length).map fun parameter =>
    readParameter frame.point installed.operational.modal[index].matched[parameter].slot
  nativeChecks :=
    ((NativeModalSignature.projections installed.nativePlan installed.operational.modal).filter
      (fun projection => projection.index == index)).map fun projection =>
      let derivation := installed.operationalDerivation
        (NativeModalSignature.projectionFormation installed.nativePlan installed.operational.declarations
          installed.operational.modal projection)
      let certificate := Certificates.Refinement.erase derivation
      installed.check certificate certificate.root.conclusion
  receipt := read frame.point.val.receipt

def castSort {environment : Environment} {ambient : List String} {left right : String}
    {pattern : Pattern} (same : left = right)
    (receipt : Execution.RootAnswer environment (bound ambient) (.base left) pattern) :
    Execution.RootAnswer environment (bound ambient) (.base right) pattern := same ▸ receipt

theorem castSort_read {environment : Environment} {ambient : List String} {left right : String}
    {pattern : Pattern} (same : left = right)
    (receipt : Execution.RootAnswer environment (bound ambient) (.base left) pattern) :
    read (castSort same receipt) = read receipt := by cases same; rfl

def checkAt? (installed : Installed) (index : Fin installed.operational.modal.length)
    {ambient : List String} {sort : String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base sort) pattern) : Option FrameReadout :=
  if same : installed.nativeProgramSort index = sort then
    let transported := castSort same.symm receipt
    if selected : transported.index = (installed.nativeSchema index).ordinal then
      (installed.checkReceiptFrame? index transported selected).map (readFrame installed index)
    else none
  else none

def checkReceipt (installed : Installed)
    {ambient : List String} {sort : String} {pattern : Pattern}
    (receipt : Execution.RootAnswer installed.operational.Environment (bound ambient)
      (.base sort) pattern) : List FrameReadout :=
  (List.finRange installed.operational.modal.length).filterMap fun index =>
    checkAt? installed index receipt

def execute (installed : Installed) (ambient : List String) (sort : String)
    (pattern : Pattern) (budget : Nat) : List FrameReadout :=
  let source : BindingPipeline.Installed.Source := ⟨bound ambient, .base sort, pattern⟩
  let session := (BindingPipeline.Installed.CertifiedExecution.begin installed.operational source).resume budget
  session.receipts.flatMap (checkReceipt installed)

def generatedExecution (language : LanguageDef) (ambient : List String) (sort : String)
    (pattern : Pattern) (budget : Nat) : Option (List FrameReadout) := do
  let installed ← (Controls.generateLanguage language).toOption
  return execute installed ambient sort pattern budget

def parameterComplete (parameter : ParameterReadout) : Bool :=
  parameter.value.isSome

def frameComplete (frame : FrameReadout) : Bool :=
  frame.rely.all parameterComplete && frame.matched.all parameterComplete &&
    frame.nativeChecks.all (· == .accepted)

def lambdaFrames := generatedExecution BindingPipeline.Controls.originalLambda [] "Term"
  BindingPipeline.Controls.lambdaSource.term 2000

def machineFrames := generatedExecution BindingPipeline.Controls.originalMachine [] "Cfg"
  BindingPipeline.Controls.machineSource.term 500

def letCaseFrames := generatedExecution BindingPipeline.Controls.originalLetCase [] "Computation"
  BindingPipeline.Controls.letCaseSource.term 2000

def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def relySource : Pattern := .apply "App" [.apply "App" [identity, identity], identity]
def relyTarget : Pattern := .apply "App" [identity, identity]
def lambdaRelyFrames := generatedExecution BindingPipeline.Controls.originalLambda [] "Term" relySource 2000

def underBinderSource : Pattern := .apply "Lam" [.lambda none
  (.apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0])]
def underBinderTarget : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def lambdaBinderFrames := generatedExecution BindingPipeline.Controls.originalLambda [] "Term" underBinderSource 2000

#guard lambdaFrames.map (fun frames => !frames.isEmpty && frames.all frameComplete) == some true
#guard machineFrames.map (fun frames => !frames.isEmpty && frames.all frameComplete) == some true
#guard letCaseFrames.map (fun frames => !frames.isEmpty && frames.all frameComplete) == some true

#guard lambdaRelyFrames.map (fun frames => frames.any fun frame =>
  !frame.position.isEmpty && !frame.rely.isEmpty && frame.receipt.target == relyTarget &&
    frame.rely.all (fun parameter => parameter.value.map (·.body) == some identity)) == some true
#guard lambdaBinderFrames.map (fun frames => frames.any fun frame =>
  !frame.position.isEmpty && frame.focusBound == [.base "Term"] &&
    frame.receipt.target == underBinderTarget && frameComplete frame) == some true

#guard generatedExecution BindingPipeline.Controls.originalLambda [] "Term" relySource 0 == some []
#guard generatedExecution BindingPipeline.Controls.originalLambda [] "Term"
    (.apply "Lam" [.lambda none (.bvar 1)]) 500 == some []
#guard generatedExecution BindingPipeline.Controls.originalLambda [] "Cfg" relySource 500 == some []

def renderFrame (frame : FrameReadout) : String :=
  "  declaration=" ++ toString frame.declaration ++ "; schema=" ++ toString frame.ordinal ++
    "; position=" ++ reprStr frame.position ++ "; local binders=" ++ reprStr frame.focusBound ++
    "; rely=" ++ reprStr frame.rely ++ "; matched=" ++ reprStr frame.matched ++
    "; focus=" ++ reprStr frame.focus ++ "; target=" ++ reprStr frame.receipt.target ++
    "; native projection certificates=" ++ reprStr frame.nativeChecks ++
    "; ordered premises=" ++ toString frame.receipt.history.length

def renderExecution (language : LanguageDef) (ambient : List String) (sort : String)
    (pattern : Pattern) (budget : Nat) : String :=
  match generatedExecution language ambient sort pattern budget with
  | none => "Native installation refused: " ++ language.name
  | some frames =>
      "Native frames " ++ language.name ++ "; checked=" ++ toString frames.length ++
        "; complete parameters=" ++ toString (frames.all frameComplete) ++ "\n" ++
        String.intercalate "\n" (frames.map renderFrame)

def main : IO Unit := do
  IO.println (renderExecution BindingPipeline.Controls.originalLambda [] "Term"
    BindingPipeline.Controls.lambdaSource.term 2000)
  IO.println (renderExecution BindingPipeline.Controls.originalMachine [] "Cfg"
    BindingPipeline.Controls.machineSource.term 500)
  IO.println (renderExecution BindingPipeline.Controls.originalLetCase [] "Computation"
    BindingPipeline.Controls.letCaseSource.term 2000)
  IO.println (renderExecution BindingPipeline.Controls.originalLambda [] "Term" relySource 2000)
  IO.println (renderExecution BindingPipeline.Controls.originalLambda [] "Term" underBinderSource 2000)

#eval main

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.ReceiptControls
