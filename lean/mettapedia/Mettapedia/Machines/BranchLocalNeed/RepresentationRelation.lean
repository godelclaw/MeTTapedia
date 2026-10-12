import Mettapedia.Machines.BranchLocalNeed.Representation
import Mettapedia.Machines.BranchLocalNeed.ExecutionMachine
import Mettapedia.GSLT.Distinction.OrderedSimulation

/-!
# The owned Need machine as an ordered system, and representation changes as
ordered simulations

The Need reference machine steps to an ordered list of successor machines and
runs a frontier.  It is an `OrderedSystem` whose frontier runner is the
machine's own (`needSystem_runFrontier`).  A compatible change of language
representation is then an ordered simulation of its graph
(`Compatible.orderedSimulation`), so complete frontiers of full machines are
related position by position at every fuel (`Compatible.frontiers_related`),
pending machines and their order included, and the relation runs back from
target to source (`Compatible.frontiers_related_back`).  This wraps the
existing commutation laws; the relation it states is the place where
non-functional relations between machine states enter the same theorems.

The independent execution machine uses this interface too. Receipt projection
is an ordered simulation, and recorded depth-first prefixes recover the full
reference frontier, including causal graphs and pending alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedRepresentation

open NeedReference
open Mettapedia.GSLT.Distinction

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
  {Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect' : Type*}

/-- The Need reference machine as an ordered nondeterministic system. -/
def needSystem (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    OrderedSystem (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) where
  step := step spec
  halted := isHalted

/-- The independently defined execution machine uses the same ordered-system
interface, with the world's receipt-retention choice preserved. -/
def executionSystem
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    OrderedSystem
      (NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) where
  step := NeedExecution.step spec
  halted := NeedExecution.isHalted

theorem executionSystem_advance
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (executionSystem spec).advance machine = NeedExecution.advance spec machine := by
  simp only [OrderedSystem.advance, NeedExecution.advance, executionSystem]
  cases NeedExecution.step spec machine <;> rfl

/-- Receipt projection is an ordered simulation because its independently
defined transitions commute, including alternative occurrence positions. -/
theorem projection_orderedSimulation
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (keepReceipts : Bool) :
    OrderedSimulation (needSystem spec) (executionSystem spec)
      (fun source target => target = NeedExecution.projectMachine keepReceipts source) :=
  OrderedSimulation.ofMap (NeedExecution.projectMachine keepReceipts)
    (fun machine => (NeedExecution.project_step_commutes spec machine).symm)
    NeedExecution.isHalted_project

/-- The common depth-first scheduler commutes with receipt projection at
every prefix, including prefixes with unresolved alternatives. -/
theorem project_depthFirst
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (keepReceipts : Bool) (count : Nat)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    ((executionSystem spec).expandFirst)^[count]
        (states.map (NeedExecution.projectMachine keepReceipts)) =
      (((needSystem spec).expandFirst)^[count] states).map
        (NeedExecution.projectMachine keepReceipts) :=
  OrderedSimulation.expandFirst_iterate_map (NeedExecution.projectMachine keepReceipts)
    (fun machine => (NeedExecution.project_step_commutes spec machine).symm)
    NeedExecution.isHalted_project count states

/-- Read the complete rich frontier from an unfinished recorded depth-first
execution. No producer is rerun to reconstruct its causal graph. -/
theorem recording_depthFirst_readback
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (count : Nat)
    (states : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (((executionSystem spec).expandFirst)^[count]
      (states.map (NeedExecution.projectMachine true))).mapM
        NeedExecution.CoreMachine.readback? =
      some (((needSystem spec).expandFirst)^[count] states) := by
  rw [project_depthFirst]
  generalize ((needSystem spec).expandFirst)^[count] states = final
  induction final with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem needSystem_advance (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (needSystem spec).advance machine = advance spec machine := by
  simp only [OrderedSystem.advance, advance, needSystem]
  cases step spec machine <;> rfl

/-- The ordered system's frontier runner is the Need machine's own. -/
theorem needSystem_runFrontier
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (needSystem spec).runFrontier fuel machines = runFrontier spec fuel machines := by
  induction fuel generalizing machines with
  | zero => rfl
  | succ fuel ih =>
      have halted : (needSystem spec).halted = isHalted := rfl
      by_cases done : machines.all isHalted = true
      · simp [OrderedSystem.runFrontier, NeedReference.runFrontier, halted, done]
      · simp only [OrderedSystem.runFrontier, NeedReference.runFrontier, halted, done,
          Bool.false_eq_true, if_false, ih]
        congr 1
        exact List.flatMap_congr fun machine _ => needSystem_advance spec machine

namespace Compatible

variable {mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
  Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
  {source : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
  {target : Spec Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}

/-- **A compatible representation change is an ordered simulation of its
graph.** -/
theorem orderedSimulation (compatible : Compatible mapping source target) :
    OrderedSimulation (needSystem source) (needSystem target)
      (fun machine machine' => machine' = mapping.mapMachine machine) :=
  OrderedSimulation.ofMap mapping.mapMachine
    (fun machine => (compatible.step_map machine).symm)
    (fun machine => Compatible.isHalted_map machine)

/-- **Complete frontiers are related position by position at every fuel**,
pending machines included. -/
theorem frontiers_related (compatible : Compatible mapping source target) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    List.Forall₂ (fun machine machine' => machine' = mapping.mapMachine machine)
      (runFrontier source fuel machines) (runFrontier target fuel (machines.map mapping.mapMachine)) := by
  rw [← needSystem_runFrontier, ← needSystem_runFrontier]
  exact compatible.orderedSimulation.runFrontier fuel
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))

/-- The same frontiers related from the target back to the source. -/
theorem frontiers_related_back (compatible : Compatible mapping source target) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    List.Forall₂ (fun machine' machine => machine' = mapping.mapMachine machine)
      (runFrontier target fuel (machines.map mapping.mapMachine)) (runFrontier source fuel machines) := by
  rw [← needSystem_runFrontier, ← needSystem_runFrontier]
  exact compatible.orderedSimulation.symm.runFrontier fuel
    (OrderedSimulation.forall₂_swap
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl)))

end Compatible

/-- The relational frontier theorem agrees with the existing functional one. -/
example {mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
      Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
    {source : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {target : Spec Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
    (compatible : Compatible mapping source target) (fuel : ℕ)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    runFrontier target fuel (machines.map mapping.mapMachine) =
      (runFrontier source fuel machines).map mapping.mapMachine :=
  (compatible.runFrontier_map fuel machines).symm

end Mettapedia.Machines.BranchLocalNeed.NeedRepresentation
