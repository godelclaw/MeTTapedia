import Mettapedia.Machines.RunContracts.FilesystemObservation

/-!
# Selected finite walking and an explicit traversal stack

The provider supplies a finite forest of occurrences. Selection prunes an
occurrence and its children; descent selects whether an included directory's
children are visited. Payloads can retain paths, link kinds and origins. Nothing
is identified by equal payloads. This fixed-input model is not a filesystem
snapshot, a cycle detector or a proof of native syscall adequacy.

The recursive specification is independent of the fuelled stack machine.
Its invariant accounts for both the delivered prefix and untouched work.
The observation protocol supplies faults and interruption separately: this
pure ordering theorem does not turn either into completed enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RunContracts.FilesystemWalking

universe u
variable {α : Type u}

mutual
  inductive Node (α : Type u) where
    | leaf (value : α)
    | directory (value : α) (children : Forest α)
  inductive Forest (α : Type u) where
    | nil
    | cons (node : Node α) (rest : Forest α)
end

mutual
  def referenceNode (select descend : α → Bool) : Node α → List α
    | .leaf value => if select value then [value] else []
    | .directory value children =>
      if select value then value :: (if descend value then referenceForest select descend children else [])
      else []
  def referenceForest (select descend : α → Bool) : Forest α → List α
    | .nil => []
    | .cons node rest => referenceNode select descend node ++ referenceForest select descend rest
end

def referenceStack (select descend : α → Bool) : List (Forest α) → List α
  | [] => []
  | first :: rest => referenceForest select descend first ++ referenceStack select descend rest

inductive Tick (α : Type u) where
  | ended
  | advance (value : Option α) (remaining : List (Forest α))

/-- One explicit stack transition. An excluded node costs a transition but
does not become data; an empty frame is popped rather than certifying end. -/
def step (select descend : α → Bool) : List (Forest α) → Tick α
  | [] => .ended
  | .nil :: rest => .advance none rest
  | .cons (.leaf value) more :: rest =>
    .advance (if select value then some value else none) (more :: rest)
  | .cons (.directory value children) more :: rest =>
    if select value then
      .advance (some value) (if descend value then children :: more :: rest else more :: rest)
    else .advance none (more :: rest)

theorem step_reference (select descend : α → Bool) (stack : List (Forest α)) :
    match step select descend stack with
    | .ended => referenceStack select descend stack = []
    | .advance value remaining => referenceStack select descend stack =
        value.toList ++ referenceStack select descend remaining := by
  cases stack with
  | nil => rfl
  | cons first rest =>
    cases first with
    | nil => rfl
    | cons node more =>
      cases node with
      | leaf value =>
        cases selected : select value <;>
          simp [step, referenceStack, referenceForest, referenceNode, selected]
      | directory value children =>
        cases selected : select value <;> cases descended : descend value <;>
          simp [step, referenceStack, referenceForest, referenceNode, selected, descended,
            List.append_assoc]

structure Report (α : Type u) where
  values : List α
  remaining : List (Forest α)
  completed : Bool

def prepend (value : Option α) (report : Report α) : Report α :=
  {report with values := value.toList ++ report.values}

def run (select descend : α → Bool) : Nat → List (Forest α) → Report α
  | 0, stack => ⟨[], stack, false⟩
  | fuel + 1, stack =>
    match step select descend stack with
    | .ended => ⟨[], [], true⟩
    | .advance value remaining =>
      prepend value (run select descend fuel remaining)

/-- Resume only unfinished traversal, using its retained stack rather than
restarting the root and replaying the delivered prefix. -/
def resume (select descend : α → Bool) (fuel : Nat) (earlier : Report α) : Report α :=
  if earlier.completed then earlier
  else
    let next := run select descend fuel earlier.remaining
    {next with values := earlier.values ++ next.values}

theorem resume_prepend (select descend : α → Bool) (fuel : Nat)
    (value : Option α) (report : Report α) :
    resume select descend fuel (prepend value report) =
      prepend value (resume select descend fuel report) := by
  cases report with
  | mk values remaining completed =>
    cases completed <;> simp [resume, prepend, List.append_assoc]

theorem run_add (select descend : α → Bool) (first second : Nat) (stack : List (Forest α)) :
    run select descend (first + second) stack =
      resume select descend second (run select descend first stack) := by
  induction first generalizing stack with
  | zero => simp [run, resume]
  | succ first ih =>
    cases transition : step select descend stack with
    | ended => simp [Nat.succ_add, run, transition, resume]
    | advance value remaining =>
      simp [Nat.succ_add, run, transition, ih, resume_prepend]

theorem run_keeps_work (select descend : α → Bool) (fuel : Nat) (stack : List (Forest α)) :
    (run select descend fuel stack).values ++
      referenceStack select descend (run select descend fuel stack).remaining =
      referenceStack select descend stack := by
  induction fuel generalizing stack with
  | zero => rfl
  | succ fuel ih =>
    have law := step_reference select descend stack
    cases transition : step select descend stack with
    | ended =>
      simp only [transition] at law
      simpa only [run, transition, referenceStack, List.nil_append] using law.symm
    | advance value remaining =>
      simp only [transition] at law
      simp [run, transition, prepend, List.append_assoc, ih, law]

theorem completed_has_no_work (select descend : α → Bool) (fuel : Nat)
    (stack : List (Forest α)) (completed : (run select descend fuel stack).completed = true) :
    (run select descend fuel stack).remaining = [] := by
  induction fuel generalizing stack with
  | zero => simp [run] at completed
  | succ fuel ih =>
    cases transition : step select descend stack with
    | ended => simp [run, transition]
    | advance value remaining =>
      simpa [run, transition, prepend] using
        ih remaining (by simpa [run, transition, prepend] using completed)

/-- Completed stack execution agrees with the independently recursive order,
including every selected occurrence and all of its payload fields. -/
theorem completed_agrees (select descend : α → Bool) (fuel : Nat)
    (stack : List (Forest α)) (completed : (run select descend fuel stack).completed = true) :
    (run select descend fuel stack).values = referenceStack select descend stack := by
  have law := run_keeps_work select descend fuel stack
  simpa [completed_has_no_work select descend fuel stack completed, referenceStack] using law

theorem excluded_prunes (select descend : α → Bool) (value : α) (children : Forest α)
    (excluded : select value = false) : referenceNode select descend (.directory value children) = [] := by
  simp [referenceNode, excluded]

theorem declined_descent (select descend : α → Bool) (value : α) (children : Forest α)
    (selected : select value = true) (declined : descend value = false) :
    referenceNode select descend (.directory value children) = [value] := by
  simp [referenceNode, selected, declined]

/-- Execute finite windows from the retained report, without retaining a
recursive caller for each transition. A completed pass remains latched. -/
def runBatches (select descend : α → Bool) (budgets : List Nat)
    (stack : List (Forest α)) : Report α :=
  budgets.foldl (fun earlier budget => resume select descend budget earlier)
    (run select descend 0 stack)

theorem fold_resume_from_run (select descend : α → Bool) (budgets : List Nat)
    (spent : Nat) (stack : List (Forest α)) :
    budgets.foldl (fun earlier budget => resume select descend budget earlier)
      (run select descend spent stack) =
      run select descend (spent + budgets.sum) stack := by
  induction budgets generalizing spent with
  | nil => simp
  | cons budget rest ih =>
    simp only [List.foldl_cons, List.sum_cons]
    rw [← run_add select descend spent budget stack, ih]
    simp [Nat.add_assoc]

/-- Batching preserves the exact prefix, residual stack and completion bit,
not merely the set of delivered payloads. -/
theorem runBatches_eq_run_sum (select descend : α → Bool) (budgets : List Nat)
    (stack : List (Forest α)) :
    runBatches select descend budgets stack =
      run select descend budgets.sum stack := by
  simpa [runBatches] using fold_resume_from_run select descend budgets 0 stack

theorem runBatches_keeps_work (select descend : α → Bool) (budgets : List Nat)
    (stack : List (Forest α)) :
    (runBatches select descend budgets stack).values ++
      referenceStack select descend (runBatches select descend budgets stack).remaining =
      referenceStack select descend stack := by
  rw [runBatches_eq_run_sum]
  exact run_keeps_work select descend budgets.sum stack

theorem runBatches_completed_agrees (select descend : α → Bool) (budgets : List Nat)
    (stack : List (Forest α))
    (completed : (runBatches select descend budgets stack).completed = true) :
    (runBatches select descend budgets stack).values = referenceStack select descend stack := by
  rw [runBatches_eq_run_sum] at completed ⊢
  exact completed_agrees select descend budgets.sum stack completed

example : (runBatches (fun _ : Nat => true) (fun _ => true) [1, 1, 2, 3]
    [.cons (.leaf 7) (.cons (.leaf 7) .nil)]).values = [7, 7] := rfl

example : (runBatches (fun _ : Nat => true) (fun _ => true) [0, 0] []).completed = false := rfl

example : (run (fun _ : Nat => true) (fun _ => true) 4
    [.cons (.leaf 7) (.cons (.leaf 7) .nil)]).values = [7, 7] := rfl

example : (run (fun _ : Nat => true) (fun _ => true) 0 []).completed = false := rfl

example : (run (fun _ : Nat => true) (fun _ => false) 3
    [.cons (.directory 1 (.cons (.leaf 2) .nil)) .nil]).values = [1] := rfl

end Mettapedia.Machines.RunContracts.FilesystemWalking
