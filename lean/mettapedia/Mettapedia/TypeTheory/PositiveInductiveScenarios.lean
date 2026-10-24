import Mettapedia.TypeTheory.PositiveInductiveBlock

/-!
# Agent-facing scenarios for staged positive-inductive admission

Two source blocks exercise the generic four-stage pipeline.

* `SearchTree` stores either a solved answer or a `List` of recursive search
  branches.  This is a genuine registered-nested occurrence.
* `Workflow` and `Action` are one mutually recursive family selected by a
  Boolean index.

The examples model useful cognitive data independently of surface syntax.
The shared `.module`-data lowering now reaches the search-tree block exactly;
the mutual-family surface join and guest typing remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PositiveInductiveScenarios

open IndexedContainer
open IndexedPolynomial
open IndexedPolynomial.Description
open PositiveInductiveBlock

/-! ## A nested search tree -/

namespace Search

inductive DataSort where
  | answer
  deriving DecidableEq

def value : DataSort → Type
  | .answer => Bool

def interface : Interface where
  SortCode := DataSort
  Value := value
  Index := Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun _ _ => ()

def registry : Registry where
  lookup name := if name = "List" then some IndexedContainer.Examples.list else none

def finitaryRegistry : registry.Finitary where
  containerFinitary := by
    intro name container found
    by_cases same : name = "List"
    · subst name
      simp [registry] at found
      subst container
      exact IndexedContainer.Examples.listFinitary
    · simp [registry, same] at found

abbrev Raw := RawCode registry interface 1 []
abbrev Checked := Code registry interface 1 []

def solvedRaw : Raw :=
  .data .answer (.result ())

def branchRaw : Raw :=
  .nested "List" [0] () (.result ())

def solvedCode : Checked :=
  .data .answer (.result ())

def branchCode : Checked :=
  .nested "List" IndexedContainer.Examples.list () (.result ())

theorem branchCode_registered : RawCode.WellRegistered branchCode := by
  exact ⟨by simp [registry], trivial⟩

def source : List (RawConstructor registry interface 1 []) :=
  [⟨"solved", solvedRaw⟩, ⟨"branch", branchRaw⟩]

def admitted : Admitted registry interface 1 [] :=
  ⟨[⟨"solved", solvedCode⟩, ⟨"branch", branchCode⟩], by decide⟩

theorem source_recognized : recognize? source = some admitted := by
  rfl

theorem source_positive :
    ∀ raw ∈ source, RawCode.Positive raw.body :=
  recognize_positive source admitted source_recognized

def environment : Env interface.Value [] := PUnit.unit
def rootIndex : interface.Index := ()

@[instance_reducible] noncomputable def branchPositionFintype
    (shape : Code.Shape branchCode environment rootIndex) :
    Fintype (Code.Position branchCode shape) :=
  Code.positionFintype finitaryRegistry branchCode branchCode_registered shape

abbrev SearchTree := admitted.Family environment rootIndex

def solvedLayer (answer : Bool) :
    admitted.polynomial.Extension admitted.Family environment rootIndex := by
  refine ⟨⟨⟨0, by decide⟩, ?_⟩, ?_⟩
  · change Σ _answer : Bool, ULift (PLift (() = ()))
    exact ⟨answer, ⟨⟨rfl⟩⟩⟩
  · intro position
    change PEmpty at position
    exact PEmpty.elim position

def solved (answer : Bool) : SearchTree :=
  admitted.construct (solvedLayer answer)

def branchLayer (children : List SearchTree) :
    admitted.polynomial.Extension admitted.Family environment rootIndex := by
  refine ⟨⟨⟨1, by decide⟩, ?_⟩, ?_⟩
  · change Σ _shape : Nat, ULift (PLift (() = ()))
    exact ⟨children.length, ⟨⟨rfl⟩⟩⟩
  · intro position
    change Sum (Fin children.length) PEmpty at position
    cases position with
    | inl child => exact children.get child
    | inr impossible => exact PEmpty.elim impossible

def branch (children : List SearchTree) : SearchTree :=
  admitted.construct (branchLayer children)

/-- One generated recursion algebra collects every solved answer in source
order across a nested list of branches. -/
def answerAlgebra : Algebra admitted.polynomial (fun _ _ => List Bool) where
  act := by
    intro _environment _index layer
    rcases layer with ⟨⟨occurrence, shape⟩, children⟩
    refine Fin.cases ?_ (fun remaining => ?_) occurrence shape children
    · intro shape _children
      exact [shape.1]
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) remaining
      intro shape children
      exact (List.ofFn fun position => children (.inl position)).flatten

noncomputable def answers (tree : SearchTree) : List Bool :=
  admitted.recursor answerAlgebra environment rootIndex tree

@[simp] theorem answers_solved (answer : Bool) :
    answers (solved answer) = [answer] := by
  rw [answers, solved, Admitted.recursor_construct]
  rfl

@[simp] theorem answers_branch (children : List SearchTree) :
    answers (branch children) =
      (List.ofFn fun position : Fin children.length =>
        answers (children.get position)).flatten := by
  rw [answers, branch, Admitted.recursor_construct]
  rfl

/-- The example uses a real nested position family: two children give two
distinct recursive positions inside the registered list container. -/
def twoBranchShape : admitted.polynomial.Shape environment rootIndex :=
  (branchLayer [solved false, solved true]).1

def firstNestedPosition : admitted.polynomial.Position twoBranchShape := by
  change Sum (Fin 2) PEmpty
  exact .inl ⟨0, by decide⟩

def secondNestedPosition : admitted.polynomial.Position twoBranchShape := by
  change Sum (Fin 2) PEmpty
  exact .inl ⟨1, by decide⟩

theorem nested_positions_distinct :
    firstNestedPosition ≠ secondNestedPosition := by
  intro equal
  change (Sum.inl (⟨0, by decide⟩ : Fin 2) : Sum (Fin 2) PEmpty) =
    Sum.inl ⟨1, by decide⟩ at equal
  exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj equal)

end Search

/-! ## A mutual workflow/action family -/

namespace Workflow

inductive DataSort where
  | action
  deriving DecidableEq

def value : DataSort → Type
  | .action => Bool

def interface : Interface where
  SortCode := DataSort
  Value := value
  Index := Bool
  IndexExpr := fun _ => Bool
  evalIndex := fun expression _ => expression

def registry : Registry where
  lookup _ := none

abbrev Raw := RawCode registry interface 0 []
abbrev Checked := Code registry interface 0 []

def doneRaw : Raw := .result false
def scheduleRaw : Raw := .recursive [] true (.result false)
def actionRaw : Raw := .data .action (.result true)
def subworkflowRaw : Raw := .recursive [] false (.result true)

def doneCode : Checked := .result false
def scheduleCode : Checked := .recursive true (.result false)
def actionCode : Checked := .data .action (.result true)
def subworkflowCode : Checked := .recursive false (.result true)

def source : List (RawConstructor registry interface 0 []) :=
  [⟨"done", doneRaw⟩, ⟨"schedule", scheduleRaw⟩,
   ⟨"action", actionRaw⟩, ⟨"subworkflow", subworkflowRaw⟩]

def admitted : Admitted registry interface 0 [] :=
  ⟨[⟨"done", doneCode⟩, ⟨"schedule", scheduleCode⟩,
    ⟨"action", actionCode⟩, ⟨"subworkflow", subworkflowCode⟩], by decide⟩

theorem source_recognized : recognize? source = some admitted := by
  rfl

theorem source_positive :
    ∀ raw ∈ source, RawCode.Positive raw.body :=
  recognize_positive source admitted source_recognized

def environment : Env interface.Value [] := PUnit.unit
def planIndex : interface.Index := false
def actionIndex : interface.Index := true

abbrev Family (isAction : interface.Index) := admitted.Family environment isAction
abbrev Plan := Family planIndex
abbrev Action := Family actionIndex

def doneLayer : admitted.polynomial.Extension admitted.Family environment planIndex := by
  refine ⟨⟨⟨0, by decide⟩, ?_⟩, ?_⟩
  · change ULift (PLift (false = false))
    exact ⟨⟨rfl⟩⟩
  · intro position
    change PEmpty at position
    exact PEmpty.elim position

def done : Plan := admitted.construct doneLayer

def scheduleLayer (next : Action) :
    admitted.polynomial.Extension admitted.Family environment planIndex := by
  refine ⟨⟨⟨1, by decide⟩, ?_⟩, ?_⟩
  · change ULift (PLift (false = false))
    exact ⟨⟨rfl⟩⟩
  · intro position
    change Option PEmpty at position
    cases position with
    | none => exact next
    | some impossible => exact PEmpty.elim impossible

def schedule (next : Action) : Plan := admitted.construct (scheduleLayer next)

def actionLayer (permitted : Bool) :
    admitted.polynomial.Extension admitted.Family environment actionIndex := by
  refine ⟨⟨⟨2, by decide⟩, ?_⟩, ?_⟩
  · change Σ _action : Bool, ULift (PLift (true = true))
    exact ⟨permitted, ⟨⟨rfl⟩⟩⟩
  · intro position
    change PEmpty at position
    exact PEmpty.elim position

def action (permitted : Bool) : Action := admitted.construct (actionLayer permitted)

def subworkflowLayer (plan : Plan) :
    admitted.polynomial.Extension admitted.Family environment actionIndex := by
  refine ⟨⟨⟨3, by decide⟩, ?_⟩, ?_⟩
  · change ULift (PLift (true = true))
    exact ⟨⟨rfl⟩⟩
  · intro position
    change Option PEmpty at position
    cases position with
    | none => exact plan
    | some impossible => exact PEmpty.elim impossible

def subworkflow (plan : Plan) : Action :=
  admitted.construct (subworkflowLayer plan)

/-- The generated mutual recursor counts action nodes while following both
directions of the workflow/action dependency. -/
def actionCountAlgebra : Algebra admitted.polynomial (fun _ _ => Nat) where
  act := by
    intro _environment _index layer
    rcases layer with ⟨⟨occurrence, shape⟩, children⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape children
    · intro _shape _children
      exact 0
    · refine Fin.cases ?_ (fun occurrence => ?_) occurrence
      · intro _shape children
        exact children none
      · refine Fin.cases ?_ (fun occurrence => ?_) occurrence
        · intro _shape _children
          exact 1
        · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
          intro _shape children
          exact children none

noncomputable def actionCount {tag : interface.Index} (workflow : Family tag) : Nat :=
  admitted.recursor actionCountAlgebra environment tag workflow

@[simp] theorem actionCount_done : actionCount done = 0 := by
  rw [actionCount, done, Admitted.recursor_construct]
  rfl

@[simp] theorem actionCount_schedule (next : Action) :
    actionCount (schedule next) = actionCount next := by
  rw [actionCount, schedule, Admitted.recursor_construct]
  rfl

@[simp] theorem actionCount_action (permitted : Bool) :
    actionCount (action permitted) = 1 := by
  rw [actionCount, action, Admitted.recursor_construct]
  rfl

@[simp] theorem actionCount_subworkflow (plan : Plan) :
    actionCount (subworkflow plan) = actionCount plan := by
  rw [actionCount, subworkflow, Admitted.recursor_construct]
  rfl

end Workflow

/-! ## Refusal controls -/

namespace Refusals

def changedParameters : Search.Raw :=
  .nested "List" [1] () (.result ())

theorem changedParameters_refused :
    RawCode.decode changedParameters = none := by
  rfl

def unknownContainer : Search.Raw :=
  .nested "UnregisteredBag" [0] () (.result ())

theorem unknownContainer_refused :
    RawCode.decode unknownContainer = none := by
  rfl

def negativeFunction : Search.Raw :=
  .functionField (.family ()) (.ground .answer) (.result ())

theorem negativeFunction_refused :
    RawCode.decode negativeFunction = none := rfl

theorem duplicateConstructor_refused :
    recognize? [⟨"same", Search.solvedRaw⟩, ⟨"same", Search.branchRaw⟩] = none := by
  rfl

def verdicts : List (String × Bool) :=
  [("registered nested search tree admitted", (recognize? Search.source).isSome),
   ("mutual workflow/action block admitted", (recognize? Workflow.source).isSome),
   ("changed recursive parameters refused", decide (RawCode.decode changedParameters = none)),
   ("unknown positive container refused", decide (RawCode.decode unknownContainer = none)),
   ("negative function field refused", decide (RawCode.decode negativeFunction = none)),
   ("duplicate constructor name refused",
      decide (recognize? [⟨"same", Search.solvedRaw⟩, ⟨"same", Search.branchRaw⟩] = none))]

end Refusals

section AxiomAudit

#print axioms Search.source_positive
#print axioms Search.branchPositionFintype
#print axioms Search.answers_solved
#print axioms Search.answers_branch
#print axioms Search.nested_positions_distinct
#print axioms Workflow.source_positive
#print axioms Workflow.actionCount_done
#print axioms Workflow.actionCount_schedule
#print axioms Workflow.actionCount_action
#print axioms Workflow.actionCount_subworkflow
#print axioms Refusals.changedParameters_refused
#print axioms Refusals.unknownContainer_refused
#print axioms Refusals.negativeFunction_refused
#print axioms Refusals.duplicateConstructor_refused

end AxiomAudit

end Mettapedia.TypeTheory.PositiveInductiveScenarios
