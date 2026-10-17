import Mettapedia.OSLF.NativeTypes.Generation.CertifiedExecution
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-!
# Safe readout controls on original authored presentations

The same replay-certified session executes original lambda, partial-recursive
machine and let/case declarations. A genuine independent beta firing also
shows why an empty raw scheduler state cannot establish absence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed.CertifiedExecution.Controls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open ScopedRuleMatching RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule)

def term : TypeExpr := .base "Term"
def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def betaSource : Installed.Source := ⟨[], term, .apply "App" [identity, identity]⟩
def bodyCapture : ScopedRuleMatching.Assignment := [("B", ⟨[term], 0, .bvar 0⟩)]
def betaCapture : ScopedRuleMatching.Assignment := ("A", ⟨[], 0, identity⟩) :: bodyCapture

theorem beta_firing : RootFiring StructuralDescent.Controls.lambdaEnvironment [] term
    betaSource.term 0 [] betaCapture betaCapture [] identity := by
  refine .fire rfl rfl (by decide +kernel)
    (checkOpenPatternWellSorted_sound (by decide +kernel)) ?_
    (checkTypedAssignment_sound (by decide +kernel)) .nil (by decide +kernel)
    (checkOpenPatternWellSorted_sound (by decide +kernel))
  refine .constructor (.cons (middle := bodyCapture) (.constructor (.cons (.binder (.capture ?_)) .nil))
    (.cons (.capture ?_) .nil))
  · decide +kernel
  · decide +kernel

theorem lambda_forged_not_reachable (budget : Nat) :
    Scheduled.resume StructuralDescent.Controls.lambdaEnvironment [] term betaSource.term budget
      (Scheduled.begin StructuralDescent.Controls.lambdaEnvironment [] term betaSource.term) ≠ {} := by
  intro fake
  let answer : Execution.RootAnswer StructuralDescent.Controls.lambdaEnvironment [] term betaSource.term :=
    ⟨0, [], betaCapture, betaCapture, [], identity, beta_firing⟩
  have drained : (Scheduled.resume StructuralDescent.Controls.lambdaEnvironment [] term betaSource.term budget
      (Scheduled.begin StructuralDescent.Controls.lambdaEnvironment [] term betaSource.term)).agenda = [] :=
    congrArg (fun state => state.agenda) fake
  have found := Scheduled.drained_receipts_complete StructuralDescent.Controls.lambdaEnvironment
    StructuralDescent.Controls.lambda_structural_admission [] term betaSource.term budget drained answer
  rw [fake] at found
  exact List.not_mem_nil found

theorem lambda_firing_rejects_forged_session (installed : BindingPipeline.Installed)
    (original : installed.Environment = StructuralDescent.Controls.lambdaEnvironment)
    (session : Session installed betaSource) :
    session.state ≠ forged installed betaSource ∧ session.absence ≠ .proved := by
  have actual : installed.HasSuccessor betaSource identity :=
    ⟨0, [], betaCapture, betaCapture, [], original.symm ▸ beta_firing⟩
  exact ⟨no_forged_session installed betaSource actual session,
    actual_successor_prevents_absence installed betaSource actual session⟩

def originalControls (language : LanguageDef) (source : Installed.Source) (budget : Nat) : Bool :=
  match BindingPipeline.Controls.installLanguage language with
  | .error _ => false
  | .ok installed =>
      let initial := begin installed source
      let paused := initial.resume 1
      let complete := paused.resume (budget - 1)
      let direct := initial.resume budget
      let counterfeit := forged installed source
      let targets := complete.receipts.map (·.target)
      initial.possibility (fun _ => true) == .unknown && initial.absence == .unknown &&
        paused.possibility (fun _ => true) == .unknown &&
        complete.complete && !targets.isEmpty &&
        complete.possibility (fun _ => true) == .proved && complete.absence == .refuted &&
        complete.outgoingAll (fun _ => true) == .proved &&
        complete.outgoingAll (fun _ => false) == .refuted &&
        targets == direct.receipts.map (·.target) && complete.state.work == direct.state.work &&
        (complete.resume 7).state.work == complete.state.work &&
        (complete.resume 7).absence == complete.absence &&
        installed.possibility source (fun _ => true) counterfeit == .refuted &&
        installed.outgoingAll source (fun _ => false) counterfeit == .proved

def stoppedControls : Bool :=
  match BindingPipeline.Controls.installLanguage BindingPipeline.Controls.originalMachine with
  | .error _ => false
  | .ok installed =>
      let initial := begin installed BindingPipeline.Controls.stoppedMachine
      let completed := initial.resume 500
      initial.absence == .unknown && completed.complete &&
        completed.receipts.isEmpty && completed.absence == .proved &&
        completed.possibility (fun _ => true) == .refuted &&
        completed.outgoingAll (fun _ => false) == .proved

#guard originalControls BindingPipeline.Controls.originalLambda BindingPipeline.Controls.lambdaSource 2000
#guard originalControls BindingPipeline.Controls.originalMachine BindingPipeline.Controls.machineSource 500
#guard originalControls BindingPipeline.Controls.originalLetCase BindingPipeline.Controls.letCaseSource 2000
#guard stoppedControls

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed.CertifiedExecution.Controls
