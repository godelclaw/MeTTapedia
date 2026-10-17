import Mettapedia.Machines.BranchLocalNeed.RepresentationRelation
import Mettapedia.OSLF.Framework.OrderedSystemNativeTypes

/-!
# Native types of the Need machine's representations

Receipt projection is an ordered simulation from the reference Need machine to
the execution machine (`projection_orderedSimulation`). Every Hennessy--Milner
native type over halting therefore holds of a reference configuration exactly
when it holds of its projection, whether receipts are kept or erased. A
compatible change of language representation transports native types in the
same way. Outcome observations survive receipt erasure. Arbitrary inspections
of the rich machine transport through retained readback; they need not survive
erasure. These are formula-extension laws, not decision procedures or a
correspondence proof for the native C evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedRepresentation

open NeedReference
open Mettapedia.GSLT.Distinction Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
open Mettapedia.OSLF.Framework.OrderedSystemNativeTypes

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

/-- An observation that agrees with receipt projection transports every formula
built from it. The simulation is constructed independently of the observer. -/
theorem projection_nativeType_iff_of_observations
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (keepReceipts : Bool) {Atom : Type*}
    (observes : Atom → Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → Prop)
    (observesCore : Atom →
      NeedExecution.CoreMachine Origin Local Resume Rule Value StableFault RetryableFault Effect → Prop)
    (agree : ∀ atom machine,
      observes atom machine ↔ observesCore atom (NeedExecution.projectMachine keepReceipts machine))
    (formula : Formula Atom Unit)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (gsltOSLF (gslt (needSystem spec))).satisfies (S := ()) machine
        (formulaNativeType (stepSystem (needSystem spec) observes) formula).pred ↔
      (gsltOSLF (gslt (executionSystem spec))).satisfies (S := ())
        (NeedExecution.projectMachine keepReceipts machine)
        (formulaNativeType (stepSystem (executionSystem spec) observesCore) formula).pred := by
  apply nativeType_iff_of_simulation (projection_orderedSimulation spec keepReceipts)
      (fun atom _ _ related => by
        subst related
        exact agree atom _) formula rfl

/-- Values, stable faults and retry reasons are observed separately. Receipt
erasure preserves their formula extensions at every related machine state. -/
theorem projection_outcome_nativeType_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (keepReceipts : Bool) (formula : Formula (Produced Value StableFault RetryableFault) Unit)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (gsltOSLF (gslt (needSystem spec))).satisfies (S := ()) machine
        (formulaNativeType (stepSystem (needSystem spec)
          (fun outcome state => haltedOutcome state = some outcome)) formula).pred ↔
      (gsltOSLF (gslt (executionSystem spec))).satisfies (S := ())
        (NeedExecution.projectMachine keepReceipts machine)
        (formulaNativeType (stepSystem (executionSystem spec)
          (fun outcome state => NeedExecution.haltedOutcome state = some outcome)) formula).pred :=
  projection_nativeType_iff_of_observations spec keepReceipts _ _
    (fun _ _ => by rw [NeedExecution.haltedOutcome_project]) formula machine

/-- Retained readback transports any inspection of the rich machine, including
its causal graph. This theorem requires receipt retention. -/
theorem recording_nativeType_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) {Atom : Type*}
    (observes : Atom → Machine Origin Local Resume Rule Value StableFault RetryableFault Effect → Prop)
    (formula : Formula Atom Unit)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (gsltOSLF (gslt (needSystem spec))).satisfies (S := ()) machine
        (formulaNativeType (stepSystem (needSystem spec) observes) formula).pred ↔
      (gsltOSLF (gslt (executionSystem spec))).satisfies (S := ())
        (NeedExecution.projectMachine true machine)
        (formulaNativeType (stepSystem (executionSystem spec)
          (fun atom state => ∃ rich, state.readback? = some rich ∧ observes atom rich)) formula).pred :=
  projection_nativeType_iff_of_observations spec true observes _
    (fun _ _ => by simp) formula machine

/-- A reference configuration and its receipt projection have the same native
types over halting. -/
theorem projection_nativeType_iff
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (keepReceipts : Bool) (formula : Formula Unit Unit)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (gsltOSLF (gslt (needSystem spec))).satisfies (S := ()) machine
        (formulaNativeType (stepSystem (needSystem spec) (halts (needSystem spec))) formula).pred ↔
      (gsltOSLF (gslt (executionSystem spec))).satisfies (S := ())
        (NeedExecution.projectMachine keepReceipts machine)
        (formulaNativeType (stepSystem (executionSystem spec) (halts (executionSystem spec))) formula).pred :=
  halting_nativeType_iff (projection_orderedSimulation spec keepReceipts) formula rfl

namespace ObservationControls

/-- One effect followed by a value, with a genuine intermediate state. -/
def spec : Spec Unit Bool Unit Unit Nat Unit Unit Nat where
  alternatives _ := [((), false)]
  action state := if state then .done (.value 7) else .perform 42 true
  afterDemand _ _ := true
  afterAllocation _ _ := true

def start : Machine Unit Bool Unit Unit Nat Unit Unit Nat where
  world := ⟨1, [], Heap.empty, ReceiptGraph.empty, 0, 0⟩
  control := .run false []

def afterEffect : Machine Unit Bool Unit Unit Nat Unit Unit Nat :=
  finished start (recorded start.world (.effect 42)) (.run true []) 0 0 1 0

def afterResult : Machine Unit Bool Unit Unit Nat Unit Unit Nat :=
  finished afterEffect afterEffect.world (.returned (.value 7) []) 0 0 0 0

def completed : Machine Unit Bool Unit Unit Nat Unit Unit Nat :=
  finished afterResult afterResult.world (.halted (.value 7)) 0 0 0 0

theorem effect_step : step spec start = [afterEffect] := rfl

theorem completes_after_effect : runFrontier spec 3 [start] = [completed] := rfl

/-- Both retention modes preserve the actual returned value. -/
theorem value_seven_survives (keepReceipts : Bool) :
    (stepSystem (executionSystem spec)
      (fun outcome state => NeedExecution.haltedOutcome state = some outcome)).sat
        (.atom (.value 7)) (NeedExecution.projectMachine keepReceipts completed) :=
  (projection_outcome_nativeType_iff spec keepReceipts (.atom (.value 7)) completed).mp rfl

theorem value_eight_is_refused (keepReceipts : Bool) :
    ¬ (stepSystem (executionSystem spec)
      (fun outcome state => NeedExecution.haltedOutcome state = some outcome)).sat
        (.atom (.value 8)) (NeedExecution.projectMachine keepReceipts completed) := by
  intro observed
  have impossible :=
    (projection_outcome_nativeType_iff spec keepReceipts (.atom (.value 8)) completed).mpr observed
  cases impossible

def hasEffect (_ : Unit) (state : Machine Unit Bool Unit Unit Nat Unit Unit Nat) : Prop :=
  42 ∈ state.world.receipts.effects

def readEffect (_ : Unit)
    (state : NeedExecution.CoreMachine Unit Bool Unit Unit Nat Unit Unit Nat) : Prop :=
  ∃ rich, state.readback? = some rich ∧ hasEffect () rich

theorem recorded_effect_is_inspectable :
    (stepSystem (executionSystem spec) readEffect).sat (.atom ())
      (NeedExecution.projectMachine true afterEffect) :=
  (recording_nativeType_iff spec hasEffect (.atom ()) afterEffect).mp
    (by change 42 ∈ ([42] : List Nat); exact List.mem_singleton_self _)

/-- Identical returned values do not make an erased causal graph inspectable. -/
theorem erased_effect_is_not_inspectable :
    (stepSystem (needSystem spec) hasEffect).sat (.atom ()) afterEffect ∧
      ¬ (stepSystem (executionSystem spec) readEffect).sat (.atom ())
        (NeedExecution.projectMachine false afterEffect) := by
  refine ⟨?_, ?_⟩
  · change 42 ∈ ([42] : List Nat)
    exact List.mem_singleton_self _
  change ¬ ∃ rich, (NeedExecution.projectMachine false afterEffect).readback? = some rich ∧ _
  simp

end ObservationControls

end Mettapedia.Machines.BranchLocalNeed.NeedRepresentation
