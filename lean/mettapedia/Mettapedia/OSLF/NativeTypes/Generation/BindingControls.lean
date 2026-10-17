import Mettapedia.OSLF.NativeTypes.Generation.BindingReadoutLaws
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarationControls
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledControls

/-!
# Runnable generic authored-language controls

The same generator and retained execution function consume each original
presentation. No language identifier chooses an implementation. Binding and
recursive context execution come from the authored declaration data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Controls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission GeneralPremise
open Mettapedia.OSLF.NativeTypes

def snapshot (language : LanguageDef) : Snapshot :=
  ⟨language, [], {signatures := [], rows := [], dynamicRelations := []}⟩

def fragment : LanguageFragment :=
  {operational := {sites := .rootOnly, equationIndices := some [], includeDerivedEquations := false}}

def fullLogic : Logic := ⟨Structural.heytingFragment, NativeLogic.full⟩

def installLanguage (language : LanguageDef) : Except GenerationIssue Installed :=
  BindingPipeline.generate (snapshot language) fragment fullLogic (fun _ => .star, fun _ => .star)

def installed (language : LanguageDef) : Bool := (installLanguage language).isOk

def runTargets (language : LanguageDef) (source : Installed.Source) (budget : Nat) :
    Option (List Pattern × Bool × Installed.Answer × Installed.Answer) :=
  match installLanguage language with
  | .error _ => none
  | .ok generated =>
      let state := generated.resume source budget (generated.begin source)
      some ((generated.receipts state).map (·.target), Scheduler.complete state,
        generated.possibility source (fun _ => true) state,
        generated.outgoingAll source (fun _ => true) state)

def originalLambda := Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
def originalMachine := Mettapedia.Languages.PartrecMachine.partrecMachine
def originalLetCase := Instances.LetCase.language

def lambdaSource : Installed.Source :=
  ⟨[], .base "Term", StructuralDescent.Controls.nestedRedex⟩

def machineSource : Installed.Source :=
  ⟨[], .base "Cfg", StructuralDescent.Controls.partrecStart⟩

def letCaseSource : Installed.Source :=
  ⟨[], Instances.LetCase.computation, StructuralDescent.Controls.LetCaseControls.nested⟩

#guard installed originalLambda
#guard installed originalMachine
#guard installed originalLetCase

#guard runTargets originalLambda lambdaSource 0 == some ([], false, .unknown, .unknown)
#guard runTargets originalLambda lambdaSource 1 == some ([], false, .unknown, .unknown)
#guard runTargets originalLambda lambdaSource 2000 ==
  some ([StructuralDescent.Controls.nestedTarget], true, .proved, .proved)

#guard (runTargets originalMachine machineSource 500).map Prod.fst ==
  some StructuralDescent.Controls.partrecTargets
#guard (runTargets originalMachine machineSource 500).map (fun result => result.2.1) == some true
#guard (runTargets originalLetCase letCaseSource 2000).map (fun result => result.2.1) == some true

def stoppedMachine : Installed.Source := ⟨[], .base "Cfg", .apply "Halt" [.apply "Nil" []]⟩

#guard runTargets originalMachine stoppedMachine 500 == some ([], true, .refuted, .proved)

def invalidLambda : Installed.Source := ⟨[], .base "Term", StructuralDescent.Controls.illScoped⟩

#guard (runTargets originalLambda invalidLambda 500).map (fun result => result.2.2.1) == some .unknown

def renderExecution (language : LanguageDef) (source : Installed.Source) (budget : Nat) : String :=
  match installLanguage language with
  | .error reason => "Generation refused: " ++ reprStr reason
  | .ok generated =>
      let state := generated.resume source budget (generated.begin source)
      "Language " ++ language.name ++ "; source " ++ reprStr source.term ++ "\n" ++
      "  work=" ++ toString state.work ++ "; pending=" ++ toString state.agenda.length ++
        "; unresolved=" ++ toString state.unresolved.length ++
        "; possibility=" ++ reprStr (generated.possibility source (fun _ => true) state) ++
        "; outgoing universal=" ++ reprStr (generated.outgoingAll source (fun _ => true) state) ++ "\n" ++
      String.intercalate "\n" ((generated.receipts state).map fun receipt =>
        let origin := ((plan generated.generated).rules[receipt.index]?).map (·.declarationIndex)
        "  declaration " ++ reprStr origin ++ "; ordered premises=" ++ toString receipt.history.length ++
          "; target=" ++ reprStr receipt.target)

def main : IO Unit := do
  IO.println (NativeSignature.Controls.render originalLambda)
  IO.println (renderExecution originalLambda lambdaSource 2000)
  IO.println (NativeSignature.Controls.render originalMachine)
  IO.println (renderExecution originalMachine machineSource 500)
  IO.println (NativeSignature.Controls.render originalLetCase)
  IO.println (renderExecution originalLetCase letCaseSource 2000)
  IO.println (renderExecution originalMachine stoppedMachine 500)

#eval main

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Controls
