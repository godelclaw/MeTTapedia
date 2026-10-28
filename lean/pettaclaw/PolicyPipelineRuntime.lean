import PolicyPipeline

/-!
# PolicyPipelineRuntime — concrete witness for the MeTTa loop presets

`PolicyPipeline` is deliberately open and knows nothing about loop-policy
fields.  This module is the small refinement witness for the currently shipped
MeTTa presets.  Each named fragment is an ordinary successful process; the
generic pipeline runner and its success/failure semantics remain unchanged.
-/

namespace PolicyPipelineRuntime

open WeakSelfHostingCore
open WeakAgentEcology
open PolicyPipeline

inductive Reasoning
  | inherit
  | high
deriving Repr, DecidableEq

structure LoopPolicy where
  burstBudget : Nat
  idleWait : Nat
  autonomousRenewal : Bool
  reasoning : Reasoning
deriving Repr, DecidableEq

def fullBurst : Nat := 50
def agentIdleWait : Nat := 1
def iterIdleWait : Nat := 60

def basePolicy : LoopPolicy :=
  { burstBudget := fullBurst
    idleWait := agentIdleWait
    autonomousRenewal := false
    reasoning := .inherit }

inductive Stage
  | base
  | iterRenewal
  | codingReasoning
deriving Repr, DecidableEq

def registry : Registry Stage LoopPolicy
  | .base => hostChange (fun _ => basePolicy)
  | .iterRenewal => hostChange (fun policy =>
      { policy with
        idleWait := iterIdleWait
        autonomousRenewal := true })
  | .codingReasoning => hostChange (fun policy =>
      { policy with reasoning := .high })

def agent : Preset Stage := ⟨[.base]⟩
def iter : Preset Stage := ⟨[.base, .iterRenewal]⟩
def coding : Preset Stage := ⟨[.base, .codingReasoning]⟩
def iterCoding : Preset Stage :=
  ⟨[.base, .iterRenewal, .codingReasoning]⟩

def evaluate (preset : Preset Stage) : LoopPolicy :=
  (run registry preset
    ({ root := (), periphery := basePolicy } : Rooted Unit LoopPolicy)).periphery

theorem agent_values : evaluate agent = basePolicy := by
  rfl

theorem iter_values : evaluate iter =
    { basePolicy with
      idleWait := iterIdleWait
      autonomousRenewal := true } := by
  rfl

theorem coding_values : evaluate coding =
    { basePolicy with reasoning := .high } := by
  rfl

/-- The MVP combination changes only the two coordinates named by its
fragments.  It does not introduce a fourth execution path. -/
theorem iter_coding_values : evaluate iterCoding =
    { burstBudget := fullBurst
      idleWait := iterIdleWait
      autonomousRenewal := true
      reasoning := .high } := by
  rfl

/-- The combination is exactly sequential preset composition. -/
theorem iter_coding_is_composition :
    iterCoding = append iter ⟨[.codingReasoning]⟩ := by
  rfl

end PolicyPipelineRuntime

#print axioms PolicyPipelineRuntime.agent_values
#print axioms PolicyPipelineRuntime.iter_values
#print axioms PolicyPipelineRuntime.coding_values
#print axioms PolicyPipelineRuntime.iter_coding_values
#print axioms PolicyPipelineRuntime.iter_coding_is_composition
