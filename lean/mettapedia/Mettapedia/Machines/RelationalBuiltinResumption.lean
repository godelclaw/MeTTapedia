import Mettapedia.Machines.RelationalBuiltinModes
import Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Prepared relational reads through weighted resumptions

The reference machine reads each input in its branch-specific binding world,
then returns an occurrence. The specialized machine contracts the two reads
only after the existing singleton preparation succeeds. Its reply retains both
source choice indices and the two ordered coefficient factors.

This is a finite pure-primitive profile with already settled edge coefficients.
It does not specialize unknown equations, execute effectful coefficient services,
authorize force, merge worlds, or provide a native C realization. Pending and
effectful coefficient work requires the existing nested owned handlers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationalBuiltinResumption

open RelationalBuiltinModes
open Mettapedia.GSLT.Core.InferenceControl (WorkOccurrence)
open Mettapedia.GSLT.Dynamics
open WeightedResumption WeightedBranchingResumption

universe u v w c
variable {Var : Type u} {Value : Type v} {Result : Type w} {V : Type c}
variable [DecidableEq Var]

abbrev Packet (Var : Type u) (Value : Type v) (Result : Type w) (V : Type c) :=
  WorkOccurrence (Answer Var Value Result × (V × V))

inductive Control (Var : Type u) (Value : Type v) (Result : Type w) (V : Type c) where
  | input (store : Store Var Value)
  | right (value : Value) (middle : Store Var Value) (paid : V) (index : Nat)
  | returned (packet : Packet Var Value Result V)

variable [Monoid V]

def source (domain : List Value) (operation : Value → Value → Result)
    (left right : Input Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V) :
    Coalgebra (Control Var Value Result V) (Packet Var Value Result V) V
  | .input store => .inr ((read domain store left).zipIdx.map fun first =>
      let paid := leftWeight store first.1.1 first.1.2
      (.right first.1.1 first.1.2 paid first.2, paid))
  | .right first middle paid index => .inr ((read domain middle right).zipIdx.map fun second =>
      let next := rightWeight first middle second.1.1 second.1.2
      let answer : Answer Var Value Result :=
        ⟨first, second.1.1, operation first second.1.1, second.1.2⟩
      (.returned ⟨(answer, (paid, next)), [index, second.2]⟩, next))
  | .returned packet => .inl packet

def completed (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V) :
    Contributions (Packet Var Value Result V) V :=
  (read domain store left).zipIdx.flatMap fun first =>
    (read domain first.1.2 right).zipIdx.map fun second =>
      let paid := leftWeight store first.1.1 first.1.2
      let next := rightWeight first.1.1 first.1.2 second.1.1 second.1.2
      let answer : Answer Var Value Result :=
        ⟨first.1.1, second.1.1, operation first.1.1 second.1.1, second.1.2⟩
      (⟨(answer, (paid, next)), [first.2, second.2]⟩, paid * next)

/-- Independent frontier execution recovers the ordered weighted relation,
including complete binding stores and physical choice indices. -/
theorem source_three_steps (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V) :
    contributions (source domain operation left right leftWeight rightWeight) 3 (.input store) =
      (completed domain operation store left right leftWeight rightWeight).map
        (fun item => (.inl item.1, item.2)) := by
  simp [contributions, source, WeightedResumption.sequence, completed,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
    ← List.map_eq_flatMap]

def preparedPacket (operation : Value → Value → Result) (store : Store Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V)
    (prepared : Prepared Var Value) : Packet Var Value Result V :=
  ⟨(direct operation prepared,
    (leftWeight store prepared.left prepared.middle,
      rightWeight prepared.left prepared.middle prepared.right prepared.store)), [0, 0]⟩

def compiled (domain : List Value) (operation : Value → Value → Result)
    (left right : Input Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V) :
    Coalgebra (Control Var Value Result V) (Packet Var Value Result V) V
  | .input store => match prepareBinary? domain store left right with
    | none => source domain operation left right leftWeight rightWeight (.input store)
    | some prepared =>
        let packet := preparedPacket operation store leftWeight rightWeight prepared
        .inr [(.returned packet, packet.state.2.1 * packet.state.2.2)]
  | state => source domain operation left right leftWeight rightWeight state

/-- Contracting the two reads keeps their separate factors and source route.
The target edge carries their product in the source's execution order. -/
theorem compiled_prepared (domain : List Value) (operation : Value → Value → Result)
    (store : Store Var Value) (left right : Input Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V)
    (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    contributions (compiled domain operation left right leftWeight rightWeight) 2 (.input store) =
      contributions (source domain operation left right leftWeight rightWeight) 3 (.input store) := by
  have reads := prepareBinary_reads domain store left right prepared accepted
  rw [source_three_steps]
  simp [contributions, compiled, accepted, source, WeightedResumption.sequence,
    completed, reads.1, reads.2, preparedPacket, direct]

section Resumption

variable (domain : List Value) (operation : Value → Value → Result)
  (left right : Input Var Value)
  (leftWeight : Store Var Value → Value → Store Var Value → V)
  (rightWeight : Value → Store Var Value → Value → Store Var Value → V)

/-- Erasing accounting recovers the independently specified relational
execution, with its full result stores and physical duplicate occurrences. -/
theorem completed_answer_erasure (store : Store Var Value) :
    (completed domain operation store left right leftWeight rightWeight).map
        (fun item => item.1.state.1) =
      binary domain operation store left right := by
  unfold completed binary
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 (read domain store left), List.flatMap_map]
  apply List.flatMap_congr
  intro first _
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 (read domain first.1.2 right), List.map_map]
  rfl

theorem completed_count (store : Store Var Value) :
    (completed domain operation store left right leftWeight rightWeight).length =
      binaryCount domain store left right := by
  have same := congrArg List.length
    (completed_answer_erasure domain operation left right leftWeight rightWeight store)
  simpa only [List.length_map, binary_length] using same

/-- This finite pure profile has a constructed delivery bound in addition
to its cardinality bound. Such a bound is not supplied by `multi` in general. -/
theorem nonempty_source_delivers (store : Store Var Value)
    (nonempty : 0 < binaryCount domain store left right) :
    ∃ packet coefficient,
      (.inl packet, coefficient) ∈ contributions
        (source domain operation left right leftWeight rightWeight) 3 (.input store) := by
  have count := completed_count domain operation left right leftWeight rightWeight store
  cases completedCut : completed domain operation store left right leftWeight rightWeight with
  | nil => simp only [completedCut, List.length_nil] at count; omega
  | cons item rest =>
      refine ⟨item.1, item.2, ?_⟩
      rw [source_three_steps, completedCut]
      exact List.mem_cons_self

theorem compiled_returned (fuel : Nat) (packet : Packet Var Value Result V) :
    contributions (compiled domain operation left right leftWeight rightWeight) fuel
        (.returned packet) =
      contributions (source domain operation left right leftWeight rightWeight) fuel
        (.returned packet) := by
  cases fuel <;> rfl

theorem compiled_right (fuel : Nat) (value : Value) (middle : Store Var Value)
    (paid : V) (index : Nat) :
    contributions (compiled domain operation left right leftWeight rightWeight) fuel
        (.right value middle paid index) =
      contributions (source domain operation left right leftWeight rightWeight) fuel
        (.right value middle paid index) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [contributions, compiled, source, WeightedResumption.sequence,
        List.flatMap_map, compiled_returned]

/-- A rejected preparation preserves every bounded reference frontier,
including its pending binding world and already accumulated coefficient. -/
theorem compiled_fallback (fuel : Nat) (store : Store Var Value)
    (rejected : prepareBinary? domain store left right = none) :
    contributions (compiled domain operation left right leftWeight rightWeight) fuel
        (.input store) =
      contributions (source domain operation left right leftWeight rightWeight) fuel
        (.input store) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp [contributions, compiled, rejected, source, WeightedResumption.sequence,
        List.flatMap_map, compiled_right]

/-- One specialized dispatch corresponds to two reference reads. This relates
pending frontiers as well as replies; equal wall-clock or fuel budgets are not
claimed to denote equal partially executed states. -/
theorem compiled_prepared_frontier (fuel : Nat) (store : Store Var Value)
    (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    contributions (compiled domain operation left right leftWeight rightWeight) (fuel + 1)
        (.input store) =
      contributions (source domain operation left right leftWeight rightWeight) (fuel + 2)
        (.input store) := by
  have reads := prepareBinary_reads domain store left right prepared accepted
  cases fuel <;>
    simp [contributions, compiled, accepted, source, WeightedResumption.sequence,
      reads.1, reads.2, preparedPacket, direct, mul_assoc]

/-- Splitting a specialized run retains the contracted frontier and its
payment, rather than preparing or charging the inputs again. -/
theorem compiled_prepared_resume (first second : Nat) (store : Store Var Value)
    (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    WeightedResumption.sequence
      (contributions (compiled domain operation left right leftWeight rightWeight)
        (first + 1) (.input store))
      (fun leaf => match leaf with
        | .inl packet => [(.inl packet, 1)]
        | .inr pending => contributions
            (compiled domain operation left right leftWeight rightWeight) second pending) =
      contributions (source domain operation left right leftWeight rightWeight)
        (first + second + 2) (.input store) := by
  calc
    _ = contributions (compiled domain operation left right leftWeight rightWeight)
        ((first + 1) + second) (.input store) := by
      apply Eq.trans ?_ (WeightedBranchingResumption.contributions_add
        (compiled domain operation left right leftWeight rightWeight) (first + 1) second
        (.input store)).symm
      apply congrArg (WeightedResumption.sequence
        (contributions (compiled domain operation left right leftWeight rightWeight)
          (first + 1) (.input store)))
      funext leaf
      cases leaf <;> rfl
    _ = contributions (compiled domain operation left right leftWeight rightWeight)
        ((first + second) + 1) (.input store) := by rw [Nat.add_right_comm first 1 second]
    _ = _ := compiled_prepared_frontier domain operation left right leftWeight rightWeight
      (first + second) store prepared accepted

/-- The independently counted frontier algorithm performs two dispatches
instead of three for a prepared call. Primitive preparation, coefficient
evaluation and machine allocation are outside this particular cost readout. -/
theorem prepared_dispatches (store : Store Var Value) (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    dispatches (compiled domain operation left right leftWeight rightWeight) 2 (.input store) = 2 ∧
      dispatches (source domain operation left right leftWeight rightWeight) 3 (.input store) = 3 := by
  have reads := prepareBinary_reads domain store left right prepared accepted
  simp [dispatches, compiled, accepted, source, reads.1, reads.2]

end Resumption

/-- Output rejection retains the completed producer occurrence. A successful
answer observer may omit it, but accounting must not erase the work and factors
that produced it. The check runs only when the producer actually returns. -/
def checkedReply (output : OutputCheck Var Value Result)
    (packet : Packet Var Value Result V) : Packet Var Value Result V × Bool :=
  (packet, output.accepts packet.state.1)

def checkReplies (output : OutputCheck Var Value Result)
    (machine : Coalgebra (Control Var Value Result V) (Packet Var Value Result V) V) :
    Coalgebra (Control Var Value Result V) (Packet Var Value Result V × Bool) V :=
  fun state => match machine state with
    | .inl packet => .inl (checkedReply output packet)
    | .inr alternatives => .inr alternatives

omit [DecidableEq Var] in
theorem checkReplies_contributions (output : OutputCheck Var Value Result)
    (machine : Coalgebra (Control Var Value Result V) (Packet Var Value Result V) V)
    (fuel : Nat) (state : Control Var Value Result V) :
    contributions (checkReplies output machine) fuel state =
      (contributions machine fuel state).map
        (fun leaf => (Sum.map (checkedReply output) id leaf.1, leaf.2)) := by
  exact contributions_reindex machine (checkReplies output machine) id (checkedReply output)
    (fun before => by cases inspected : machine before <;> simp [checkReplies, inspected])
    fuel state

/-- The optional worker has the same retained completed/rejected occurrences
and pending states as the checked reference, at the contracted source budget. -/
theorem compiled_checked_frontier (domain : List Value) (operation : Value → Value → Result)
    (left right : Input Var Value)
    (leftWeight : Store Var Value → Value → Store Var Value → V)
    (rightWeight : Value → Store Var Value → Value → Store Var Value → V)
    (output : OutputCheck Var Value Result) (fuel : Nat) (store : Store Var Value)
    (prepared : Prepared Var Value)
    (accepted : prepareBinary? domain store left right = some prepared) :
    contributions
      (checkReplies output (compiled domain operation left right leftWeight rightWeight))
      (fuel + 1) (.input store) =
    contributions
      (checkReplies output (source domain operation left right leftWeight rightWeight))
      (fuel + 2) (.input store) := by
  rw [checkReplies_contributions, checkReplies_contributions,
    compiled_prepared_frontier domain operation left right leftWeight rightWeight
      fuel store prepared accepted]

namespace Controls

private def unbound : Store Nat Nat := fun _ => none

private def leftFactor (_before : Store Nat Nat) (_value : Nat) (_after : Store Nat Nat) :
    FreeMonoid String := FreeMonoid.of "left"

private def rightFactor (_first : Nat) (_before : Store Nat Nat) (_value : Nat)
    (_after : Store Nat Nat) : FreeMonoid String := FreeMonoid.of "right"

private def observeWords
    (leaves : Contributions
      (Packet Nat Nat Nat (FreeMonoid String) ⊕ Control Nat Nat Nat (FreeMonoid String))
      (FreeMonoid String)) : List (Nat × List Nat × List String) :=
  (returnedContributions leaves).map fun leaf =>
    (leaf.1.state.1.result, leaf.1.trace, FreeMonoid.toList leaf.2)

theorem direct_worker_keeps_ordered_factors :
    observeWords (contributions
      (compiled [7, 7] Nat.add (.literal 3) (.literal 4) leftFactor rightFactor)
      2 (.input unbound)) = [(7, [0, 0], ["left", "right"])] := rfl

theorem duplicate_values_keep_distinct_source_choices :
    observeWords (contributions
      (compiled [7, 7] Nat.add (.var 0) (.var 0) leftFactor rightFactor)
      3 (.input unbound)) =
        [(14, [0, 0], ["left", "right"]), (14, [1, 0], ["left", "right"])] := rfl

theorem contracted_pending_reply_is_not_delivered_early :
    returnedContributions (contributions
      (compiled [7] Nat.add (.var 0) (.literal 1) leftFactor rightFactor)
      1 (.input unbound)) = [] := rfl

theorem second_factor_reads_the_intermediate_binding_world :
    observeWords (contributions
      (compiled [7] Nat.add (.var 0) (.literal 1) leftFactor
        (fun _ middle _ _ => if middle 0 = some 7 then FreeMonoid.of "bound"
          else FreeMonoid.of "unbound"))
      2 (.input unbound)) = [(8, [0, 0], ["left", "bound"])] := rfl

theorem zero_coefficient_retains_the_answer_occurrence :
    ((returnedContributions (contributions
      (compiled [7] Nat.add (.var 0) (.literal 1)
        (fun _ _ _ => (0 : Nat)) (fun _ _ _ _ => 5))
      2 (.input unbound))).map fun leaf =>
        (leaf.1.state.1.result, leaf.1.trace, leaf.2)) = [(8, [0, 0], 0)] := rfl

theorem rejected_output_keeps_its_completed_account :
    ((returnedContributions (contributions
      (checkReplies (.checked fun answer => decide (answer.result = 99))
        (compiled [7] Nat.add (.var 0) (.literal 1) leftFactor rightFactor))
      2 (.input unbound))).map fun leaf =>
        (leaf.1.1.state.1.result, leaf.1.2, FreeMonoid.toList leaf.2)) =
      [(8, false, ["left", "right"])] := rfl

end Controls

end Mettapedia.Machines.RelationalBuiltinResumption
