import Mettapedia.Languages.Dataflow.Operational

/-!
# Compiled canaries for the dataflow language

A concrete arithmetic instantiation, exercising both sides of the boundary.

Positive: a program with two *independent* instructions runs to the same
answer under two genuinely different schedules, and that answer is its
denotation.

Negative, one per well-formedness condition — none asserted, all proved:

* two writers for one cell;
* an operand with no writer and no input;
* a dependency cycle;
* an operator applied at the wrong arity.

The cycle case is the interesting one: no acyclicity predicate is consulted,
the cell simply denotes nothing at any budget.
-/

namespace Mettapedia.Languages.Dataflow.Canary

open Mettapedia.Languages.Dataflow

/-- A two-operator arithmetic signature. -/
inductive ArithOp where
  | add
  | mul
deriving DecidableEq, Repr

/-- Both operators are binary. -/
def arith : PureOperatorSpec ArithOp Nat where
  arity := fun _ => 2
  apply := fun op args =>
    match op, args with
    | .add, [x, y] => x + y
    | .mul, [x, y] => x * y
    | _, _ => 0

/-! ## Positive: independent instructions, two schedules, one answer -/

private def addNode : Instruction ArithOp Nat := .apply 10 .add [1, 2]
private def mulNode : Instruction ArithOp Nat := .apply 11 .mul [1, 2]
private def joinNode : Instruction ArithOp Nat := .apply 12 .add [10, 11]

/-- `c10 = c1 + c2` and `c11 = c1 * c2` are independent; `c12` joins them.
With `c1 = 5` and `c2 = 7` the answer is `12 + 35 = 47`. -/
def sumProduct : Program ArithOp Nat where
  inputs := [(1, 5), (2, 7)]
  instructions := [addNode, mulNode, joinNode]
  result := 12

private theorem sumProduct_producers_denote :
    Denotes arith sumProduct 10 12 ∧ Denotes arith sumProduct 11 35 := by
  have input1 : sumProduct.inputValue? 1 = some 5 := rfl
  have input2 : sumProduct.inputValue? 2 = some 7 := rfl
  have denote10 : Denotes arith sumProduct 10 12 :=
    Denotes.apply (c := 10) rfl rfl rfl
      (DenotesList.cons (Denotes.input input1)
        (DenotesList.cons (Denotes.input input2) DenotesList.nil))
  have denote11 : Denotes arith sumProduct 11 35 :=
    Denotes.apply (c := 11) rfl rfl rfl
      (DenotesList.cons (Denotes.input input1)
        (DenotesList.cons (Denotes.input input2) DenotesList.nil))
  exact ⟨denote10, denote11⟩

/-- The returned cell denotes 47. -/
theorem sumProduct_denotes : Denotes arith sumProduct 12 47 :=
  Denotes.apply (spec := arith) (p := sumProduct) (c := 12)
    (op := ArithOp.add) rfl rfl rfl
    (DenotesList.cons sumProduct_producers_denote.1
      (DenotesList.cons sumProduct_producers_denote.2 DenotesList.nil))

/-! ### Two genuinely different schedules

Schedule A fires the sum before the product; schedule B fires the product
first.  Both reach the same terminal state content. -/

private def envStart : List (CellId × Nat) := [(1, 5), (2, 7)]

theorem schedule_add_first :
    Steps arith sumProduct.initialState
      ⟨[(12, 47), (11, 35), (10, 12)] ++ envStart, []⟩ := by
  refine Relation.ReflTransGen.head (b := ⟨(10, 12) :: envStart,
    [mulNode, joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := envStart) (pre := [])
      (post := [mulNode, joinNode]) (i := addNode) (v := 12) rfl
  refine Relation.ReflTransGen.head (b := ⟨(11, 35) :: (10, 12) :: envStart,
    [joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := (10, 12) :: envStart) (pre := [])
      (post := [joinNode]) (i := mulNode) (v := 35) rfl
  refine Relation.ReflTransGen.head (b := ⟨(12, 47) :: (11, 35) ::
    (10, 12) :: envStart, []⟩) ?_ Relation.ReflTransGen.refl
  exact Step.fire (computed := (11, 35) :: (10, 12) :: envStart) (pre := [])
    (post := []) (i := joinNode) (v := 47) rfl

theorem schedule_mul_first :
    Steps arith sumProduct.initialState
      ⟨[(12, 47), (10, 12), (11, 35)] ++ envStart, []⟩ := by
  refine Relation.ReflTransGen.head (b := ⟨(11, 35) :: envStart,
    [addNode, joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := envStart) (pre := [addNode])
      (post := [joinNode]) (i := mulNode) (v := 35) rfl
  refine Relation.ReflTransGen.head (b := ⟨(10, 12) :: (11, 35) :: envStart,
    [joinNode]⟩) ?_ ?_
  · exact Step.fire (computed := (11, 35) :: envStart) (pre := [])
      (post := [joinNode]) (i := addNode) (v := 12) rfl
  refine Relation.ReflTransGen.head (b := ⟨(12, 47) :: (10, 12) ::
    (11, 35) :: envStart, []⟩) ?_ Relation.ReflTransGen.refl
  exact Step.fire (computed := (10, 12) :: (11, 35) :: envStart) (pre := [])
    (post := []) (i := joinNode) (v := 47) rfl

/-- The two schedules are genuinely different runs — their intermediate
environments differ — yet they agree on the returned cell. -/
theorem schedules_differ_but_agree :
    ([(12, 47), (11, 35), (10, 12)] ++ envStart) ≠
      ([(12, 47), (10, 12), (11, 35)] ++ envStart) ∧
    lookup ([(12, 47), (11, 35), (10, 12)] ++ envStart) 12 =
      lookup ([(12, 47), (10, 12), (11, 35)] ++ envStart) 12 := by
  refine ⟨by simp, rfl⟩

/-- The general dependency square applies to the two ready arithmetic
instructions and retains the still-pending join in both orders. -/
theorem sumProduct_ready_fork_join :
    Step arith ⟨(10, 12) :: envStart, [mulNode, joinNode]⟩
      ⟨(11, 35) :: (10, 12) :: envStart, [joinNode]⟩ ∧
    Step arith ⟨(11, 35) :: envStart, [addNode, joinNode]⟩
      ⟨(10, 12) :: (11, 35) :: envStart, [joinNode]⟩ ∧
    ∀ cell, lookup ((11, 35) :: (10, 12) :: envStart) cell =
      lookup ((10, 12) :: (11, 35) :: envStart) cell := by
  have square := ready_pair_diamond arith envStart [] [] [joinNode]
    addNode mulNode 12 35 (by decide) rfl rfl rfl rfl
  exact ⟨square.2.2.1, square.2.2.2.1, square.2.2.2.2⟩

/-- A dependent join cannot enter the ready batch with its producers.
One completed producer is insufficient; both values make it ready. -/
theorem sumProduct_join_waits_for_both :
    readyValue arith envStart joinNode = none ∧
    readyValue arith ((10, 12) :: envStart) joinNode = none ∧
    readyValue arith ((11, 35) :: (10, 12) :: envStart) joinNode = some 47 :=
  ⟨rfl, rfl, rfl⟩

/-- The positive example supplies the full admission contract used by the
general reachability and delayed-readiness laws. -/
theorem sumProduct_wellFormed : sumProduct.WellFormed arith where
  writersUnique := by decide
  inputsUnique := by decide
  inputsNotWritten := by
    intro instruction member
    simp only [sumProduct, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  aritiesOk := by
    intro instruction member
    simp only [sumProduct, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  destinationsDenote := by
    intro instruction member
    simp only [sumProduct, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨12, sumProduct_producers_denote.1⟩
    · exact ⟨35, sumProduct_producers_denote.2⟩
    · exact ⟨47, sumProduct_denotes⟩
  resultDenotes := ⟨47, sumProduct_denotes⟩

/-- A held product computation keeps its value across every reachable
schedule prefix, including prefixes that have already finished the join. -/
theorem sumProduct_ready_survives_every_run (state : State ArithOp Nat)
    (run : Steps arith sumProduct.initialState state) :
    readyValue arith state.computed mulNode = some 35 :=
  (Invariant.initial sumProduct_wellFormed).ready_preserved_steps
    sumProduct_wellFormed run rfl

/-- The executable policy skips an unavailable join and retains it exactly. -/
theorem executable_scheduler_retains_waiting_join :
    (readyMachine arith).step ⟨envStart, [joinNode, addNode, mulNode]⟩ =
      some ⟨(10, 12) :: envStart, [joinNode, mulNode]⟩ := rfl

/-- A one-firing pause retains both unfinished instructions. Resuming that
state finishes in two more firings, with no restart of the completed sum. -/
theorem executable_split_preserves_residual :
    (readyMachine arith).runSlice 1 sumProduct.initialState =
      (⟨(10, 12) :: envStart, [mulNode, joinNode]⟩, 1) ∧
    (readyMachine arith).runSlice 2
        ((readyMachine arith).runSlice 1 sumProduct.initialState).1 =
      (⟨[(12, 47), (11, 35), (10, 12)] ++ envStart, []⟩, 2) := ⟨rfl, rfl⟩

/-- Excess allowance does not charge fictitious transitions after completion. -/
theorem executable_completion_charges_three :
    (readyMachine arith).runSlice 20 sumProduct.initialState =
      (⟨[(12, 47), (11, 35), (10, 12)] ++ envStart, []⟩, 3) := rfl

/-- Readiness alone does not protect a delayed computation from an overwrite.
The unrestricted step relation permits this malformed input-writer pair. -/
theorem overwriting_an_input_changes_ready_value :
    readyValue arith [(1, 5)] (.apply 2 .add [1, 1]) = some 10 ∧
    Step arith ⟨[(1, 5)], [.const 1 8]⟩ ⟨[(1, 8), (1, 5)], []⟩ ∧
    readyValue arith [(1, 8), (1, 5)] (.apply 2 .add [1, 1]) = some 16 := by
  exact ⟨rfl, Step.fire (pre := []) (post := []) rfl, rfl⟩

/-! ## Negative: two writers for one cell -/

def twoWriters : Program ArithOp Nat where
  inputs := [(1, 5)]
  instructions := [.const 7 1, .const 7 2]
  result := 7

theorem twoWriters_not_wellFormed : ¬ twoWriters.WellFormed arith := by
  intro wf
  have := wf.writersUnique
  simp [twoWriters, Instruction.dst] at this

/-- Readiness alone does not license reordering: these two ready writers
overwrite the same cell, and actual operational runs disagree. -/
theorem twoWriters_order_changes_result :
    Steps arith twoWriters.initialState ⟨[(7, 2), (7, 1), (1, 5)], []⟩ ∧
    Steps arith twoWriters.initialState ⟨[(7, 1), (7, 2), (1, 5)], []⟩ ∧
    lookup [(7, 2), (7, 1), (1, 5)] 7 ≠ lookup [(7, 1), (7, 2), (1, 5)] 7 := by
  refine ⟨?_, ?_, by decide⟩
  · refine Relation.ReflTransGen.head
      (Step.fire (computed := [(1, 5)]) (pre := [])
        (post := [.const 7 2]) (i := .const 7 1) rfl) ?_
    exact Relation.ReflTransGen.single
      (Step.fire (pre := []) (post := []) (i := .const 7 2) rfl)
  · refine Relation.ReflTransGen.head
      (Step.fire (computed := [(1, 5)]) (pre := [.const 7 1])
        (post := []) (i := .const 7 2) rfl) ?_
    exact Relation.ReflTransGen.single
      (Step.fire (pre := []) (post := []) (i := .const 7 1) rfl)

/-! ## Negative: an operand with no writer and no input -/

def danglingOperand : Program ArithOp Nat where
  inputs := [(1, 5)]
  instructions := [.apply 0 .add [1, 9]]
  result := 0

/-- A malformed program can be machine-final while work remains. No missing
dependency is silently discarded or reported as a completed result. -/
theorem executable_stuck_retains_pending :
    (readyMachine arith).runSlice 20 danglingOperand.initialState =
      (danglingOperand.initialState, 0) ∧
    danglingOperand.initialState.pending ≠ [] := by
  exact ⟨rfl, by decide⟩

/-- Cell 9 is supplied by nothing, so it denotes at no budget. -/
theorem dangling_cell_never_denotes :
    ∀ fuel, denoteCell arith danglingOperand fuel 9 = none := by
  intro fuel
  cases fuel with
  | zero => rw [denoteCell_zero]; rfl
  | succ fuel => rw [denoteCell_succ]; rfl

/-- Hence the returned cell denotes at no budget either. -/
theorem dangling_result_never_denotes :
    ∀ fuel, denoteCell arith danglingOperand fuel 0 = none := by
  intro fuel
  cases fuel with
  | zero => rw [denoteCell_zero]; rfl
  | succ fuel =>
      have operandsNone :
          denoteOperands arith danglingOperand fuel [1, 9] = none := by
        cases headValue : denoteCell arith danglingOperand fuel 1 with
        | none => simp [denoteOperands_cons, headValue]
        | some w =>
            simp [denoteOperands_cons, headValue,
              dangling_cell_never_denotes fuel]
      rw [denoteCell_succ,
        show danglingOperand.inputValue? 0 = none from rfl,
        show danglingOperand.writerOf? 0 =
          some (.apply 0 .add [1, 9]) from rfl]
      simp [operandsNone]

theorem danglingOperand_not_wellFormed :
    ¬ danglingOperand.WellFormed arith := by
  intro wf
  obtain ⟨v, fuel, evaluated⟩ := wf.resultDenotes
  have evaluated' : denoteCell arith danglingOperand fuel 0 = some v :=
    evaluated
  rw [dangling_result_never_denotes fuel] at evaluated'
  cases evaluated'

/-! ## Negative: a dependency cycle -/

def cyclic : Program ArithOp Nat where
  inputs := []
  instructions := [.apply 0 .add [1, 1], .apply 1 .add [0, 0]]
  result := 0

/-- Neither cell of the cycle denotes at any budget.  Nothing about
acyclicity is consulted: the recursion simply never bottoms out. -/
theorem cyclic_never_denotes : ∀ fuel,
    denoteCell arith cyclic fuel 0 = none ∧
      denoteCell arith cyclic fuel 1 = none := by
  intro fuel
  induction fuel with
  | zero => exact ⟨by rw [denoteCell_zero]; rfl, by rw [denoteCell_zero]; rfl⟩
  | succ fuel inductionHypothesis =>
      constructor
      · have operandsNone :
            denoteOperands arith cyclic fuel [1, 1] = none := by
          simp [denoteOperands_cons, inductionHypothesis.2]
        rw [denoteCell_succ,
          show cyclic.inputValue? 0 = none from rfl,
          show cyclic.writerOf? 0 = some (.apply 0 .add [1, 1]) from rfl]
        simp [operandsNone]
      · have operandsNone :
            denoteOperands arith cyclic fuel [0, 0] = none := by
          simp [denoteOperands_cons, inductionHypothesis.1]
        rw [denoteCell_succ,
          show cyclic.inputValue? 1 = none from rfl,
          show cyclic.writerOf? 1 = some (.apply 1 .add [0, 0]) from rfl]
        simp [operandsNone]

theorem cyclic_not_wellFormed : ¬ cyclic.WellFormed arith := by
  intro wf
  obtain ⟨v, fuel, evaluated⟩ := wf.resultDenotes
  have evaluated' : denoteCell arith cyclic fuel 0 = some v := evaluated
  rw [(cyclic_never_denotes fuel).1] at evaluated'
  cases evaluated'

/-! ## Negative: wrong operator arity -/

def wrongArity : Program ArithOp Nat where
  inputs := [(1, 5), (2, 7), (3, 9)]
  instructions := [.apply 0 .add [1, 2, 3]]
  result := 0

theorem wrongArity_not_wellFormed : ¬ wrongArity.WellFormed arith := by
  intro wf
  have := wf.aritiesOk (.apply 0 .add [1, 2, 3]) (by simp [wrongArity])
  simp [Instruction.arityOk, arith] at this

/-! ## Independent retained children and their ordered parent join -/

namespace Retained

open Mettapedia.Machines

def sumChild : OwnedPullDriver.Program Nat Nat :=
  .child (.emit 1 (.done 2)) (fun value => .emit 1 (.emit 3 (.done (value + 10))))

def productChild : OwnedPullDriver.Program Nat Nat := .emit 9 (.done 35)

theorem sumChild_runs : OwnedPullDriver.CostedRuns sumChild [1, 1, 3] 12 1 1 :=
  .child (resume := fun value => .emit 1 (.emit 3 (.done (value + 10))))
    (.emit (.done (value := 2))) (.emit (.emit .done))

theorem productChild_runs : OwnedPullDriver.CostedRuns productChild [9] 35 0 0 :=
  .emit .done

def pool : CellId → Nat × OwnedPullDriver.State Nat Nat := fun cell =>
  if cell = 10 then (2, ⟨sumChild, []⟩)
  else if cell = 11 then (7, ⟨productChild, []⟩)
  else (0, ⟨.done 0, []⟩)

private def kernel := OwnedPullDriver.paidKernel CellId Nat Nat

theorem partial_child_cannot_supply_internal_return :
    let paused := kernel.run () (fun _ => ()) pool [(10, 2), (11, 1)]
    (paused 10).2.work = .done 2 ∧
      OwnedPullDriver.completedValue (paused 10).2 = none ∧
      RetainedChildren.completedCells [10, 11] paused = [(11, 35)] ∧
      readyValue arith
        (RetainedChildren.completedCells [10, 11] paused ++ envStart) joinNode = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The product finishes first; the parent still reads sum, product, sum.
Repeated operand occurrences remain repeated in the ordered result. -/
theorem resumed_children_keep_parent_order_and_paid_work :
    let finished := kernel.run () (fun _ => ()) pool [(10, 2), (11, 1), (10, 3)]
    finished 10 = (7, ⟨.done 12, []⟩) ∧
      finished 11 = (8, ⟨.done 35, []⟩) ∧
      evalOperands (RetainedChildren.completedCells [11, 10] finished) [10, 11, 10] =
        some [12, 35, 12] ∧
      readyValue arith
        (RetainedChildren.completedCells [11, 10] finished ++ envStart) joinNode = some 47 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem two_child_interleavings_keep_complete_pool :
    kernel.run () (fun _ => ()) pool [(10, 2), (11, 1), (10, 3)] =
      kernel.run () (fun _ => ()) pool [(11, 1), (10, 2), (10, 3)] := by
  apply OwnedPullDriver.paidKernel_interleaving
  intro owner
  by_cases atSum : 10 = owner
  · subst owner; decide
  · by_cases atProduct : 11 = owner
    · subst owner; decide
    · simp [atSum, atProduct]

/-- This instantiates the general implementation-to-ready-firing theorem,
using real child derivations and reversed worker completion. -/
theorem completed_children_realize_parent_firings :
    let result := kernel.partitioned () (fun _ => ()) pool [[(11, 1)], [(10, 5)]]
    result 10 = (7, ⟨.done 12, []⟩) ∧
      result 11 = (8, ⟨.done 35, []⟩) ∧
      Steps arith sumProduct.initialState
        ⟨RetainedChildren.completedCells [10, 11] result ++ envStart, [joinNode]⟩ ∧
      ∀ observer, readyValue arith
          (RetainedChildren.completedCells [10, 11] result ++ envStart) observer =
        readyValue arith
          (RetainedChildren.completedCells [11, 10] result ++ envStart) observer := by
  exact RetainedChildren.completed_pair_fires arith envStart [] [] [joinNode]
    addNode mulNode 12 35 sumChild productChild [1, 1, 3] [9]
    1 1 0 0 2 7 0 0 sumChild_runs productChild_runs
    (by decide) rfl rfl rfl rfl pool rfl rfl [[(11, 1)], [(10, 5)]] (by decide)

theorem parent_instruction_allowance_does_not_complete_child :
    OwnedPullDriver.completedValue
        (OwnedPullDriver.paidSlice sumProduct.instructions.length
          (0, ⟨OwnedPullDriver.nested 10, []⟩)).2 = none := rfl

theorem completed_children_do_not_charge_unused_quanta :
    let before := kernel.run () (fun _ => ()) pool [(10, 5), (11, 1)]
    kernel.run () (fun _ => ()) before [(11, 50), (10, 50)] = before := by
  funext cell
  by_cases atSum : cell = 10
  · subst cell; rfl
  · by_cases atProduct : cell = 11
    · subst cell; rfl
    · simp [kernel, OwnedPullDriver.paidKernel, SnapshotBatch.Kernel.run,
        SnapshotBatch.Kernel.step, atSum, atProduct]

/-- Starting both quanta from one snapshot silently loses the first prefix.
The kernel's disjoint-owner condition excludes this mistaken parallelization. -/
theorem preparing_one_child_twice_loses_progress :
    (kernel.batch () (fun _ => ()) pool [(10, 2), (10, 3)] 10).1 = 5 ∧
      (kernel.run () (fun _ => ()) pool [(10, 2), (10, 3)] 10).1 = 7 ∧
      OwnedPullDriver.completedValue
        (kernel.batch () (fun _ => ()) pool [(10, 2), (10, 3)] 10).2 = none := by
  exact ⟨rfl, rfl, rfl⟩

end Retained

end Mettapedia.Languages.Dataflow.Canary
