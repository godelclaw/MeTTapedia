import Mettapedia.Logic.LP.RuntimeTerm
import Mettapedia.Logic.LP.StandardizeApart

/-!
# Materializing LP clauses in the executable Prolog heap

The canonical runtime keeps source syntax in `Logic.LP` and materializes a
standardized-apart clause only when clause selection enters it.  This is the
Lean-native counterpart of SWI-Prolog V10.1.9 allocating a fresh clause frame
and global-stack cells before executing the head.  The relevant pinned source
anchors are `src/pl-wam.c` (`PL_open_query`, frame marks and `Undo`) and
`src/pl-copyterm.c` (`copy_term`, `duplicate_term`).

Materialization is not a second evaluator.  It is a checked constructor for
the one graph heap used by `RuntimeUnification`: repeated variables share an
address, existing heap cells remain stable, and allocation never changes the
trail.  Clause activation freshness comes from `Clause.atScope` in
`StandardizeApart`.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeMaterialize

open RuntimeTerm

/-- Executable atom: its arguments are roots in the shared runtime heap. -/
structure RuntimeAtom (σ : LPSignature) where
  symbol : σ.relationSymbols
  args : Array Addr


/-- The runtime atom has the signature arity and every argument is allocated. -/
def RuntimeAtom.WellFormed {σ : LPSignature}
    (heap : Heap σ) (atom : RuntimeAtom σ) : Prop :=
  atom.args.size = σ.relationArity atom.symbol ∧
    ∀ address ∈ atom.args.toList, address < heap.size

/-- Executable checker for `RuntimeAtom.WellFormed`. -/
def RuntimeAtom.checkWellFormed {σ : LPSignature}
    (heap : Heap σ) (atom : RuntimeAtom σ) : Bool :=
  atom.args.size == σ.relationArity atom.symbol &&
    atom.args.toList.all fun address => address < heap.size

theorem RuntimeAtom.wellFormed_of_check {σ : LPSignature}
    {heap : Heap σ} {atom : RuntimeAtom σ}
    (h : atom.checkWellFormed heap = true) : atom.WellFormed heap := by
  simp only [RuntimeAtom.checkWellFormed, Bool.and_eq_true] at h
  refine ⟨beq_iff_eq.mp h.1, ?_⟩
  intro address hAddress
  exact of_decide_eq_true (List.all_eq_true.mp h.2 address hAddress)

/-- A copied clause whose head and body all point into one shared heap. -/
structure RuntimeClause (σ : LPSignature) where
  head : RuntimeAtom σ
  body : List (RuntimeAtom σ)


def RuntimeClause.WellFormed {σ : LPSignature}
    (heap : Heap σ) (clause : RuntimeClause σ) : Prop :=
  clause.head.WellFormed heap ∧
    ∀ atom ∈ clause.body, atom.WellFormed heap

def RuntimeClause.checkWellFormed {σ : LPSignature}
    (heap : Heap σ) (clause : RuntimeClause σ) : Bool :=
  clause.head.checkWellFormed heap &&
    clause.body.all fun atom => atom.checkWellFormed heap

theorem RuntimeClause.wellFormed_of_check {σ : LPSignature}
    {heap : Heap σ} {clause : RuntimeClause σ}
    (h : clause.checkWellFormed heap = true) : clause.WellFormed heap := by
  simp only [RuntimeClause.checkWellFormed, Bool.and_eq_true] at h
  refine ⟨RuntimeAtom.wellFormed_of_check h.1, ?_⟩
  intro atom hAtom
  exact RuntimeAtom.wellFormed_of_check
    (List.all_eq_true.mp h.2 atom hAtom)

/-- State local to one materialization.  `varMap` is reset for every clause
activation but shared by that clause's head and body.

The trail is intentionally absent.  Materialization allocates fresh heap cells
but performs no variable binding, so it is structurally unable to add, remove,
or rewrite a caller's trail. -/
structure BuilderState (σ : LPSignature) where
  heap : Heap σ
  varMap : List (σ.vars × Addr)


/-- The materializer's deliberately small state-and-error effect.

This is defined directly, rather than through a generic transformer stack, so
its transition equations remain visible to both the kernel and mechanism
proofs.  It is local construction machinery, not a second evaluator. -/
structure BuilderM (σ : LPSignature) (α : Type*) where
  run : BuilderState σ → Except MemoryError (α × BuilderState σ)

namespace BuilderM

@[inline] protected def pure (value : α) : BuilderM σ α where
  run state := .ok (value, state)

@[inline] protected def bind (action : BuilderM σ α)
    (next : α → BuilderM σ β) : BuilderM σ β where
  run state :=
    match action.run state with
    | .error error => .error error
    | .ok (value, nextState) => (next value).run nextState

instance : Monad (BuilderM σ) where
  pure := BuilderM.pure
  bind := BuilderM.bind

/-- The clause builder is an ordinary lawful state-and-error monad.  Recording
the laws lets structural materializers reason with the standard `List.mapM`
equations rather than depending on its tail-recursive implementation. -/
instance : LawfulMonad (BuilderM σ) := LawfulMonad.mk' _
  (by
    intro α action
    cases action with
    | mk run =>
        apply congrArg BuilderM.mk
        funext state
        change (BuilderM.bind { run := run }
          (fun value => BuilderM.pure (id value))).run state = run state
        cases hRun : run state <;>
          simp [BuilderM.bind, BuilderM.pure, hRun])
  (by
    intro α β value next
    rfl)
  (by
    intro α β γ action next later
    cases action with
    | mk run =>
        apply congrArg BuilderM.mk
        funext state
        change (BuilderM.bind (BuilderM.bind { run := run } next) later).run state =
          (BuilderM.bind { run := run }
            (fun value => BuilderM.bind (next value) later)).run state
        cases hAction : run state with
        | error error => simp [BuilderM.bind, hAction]
        | ok result =>
            rcases result with ⟨value, nextState⟩
            cases hNext : (next value).run nextState <;>
              simp [BuilderM.bind, hAction, hNext])

@[simp]
theorem map_run (action : BuilderM σ α) (transform : α → β)
    (state : BuilderState σ) :
    (transform <$> action).run state =
      match action.run state with
      | .error error => .error error
      | .ok (value, nextState) => .ok (transform value, nextState) := by
  change (BuilderM.bind action
    (fun value => BuilderM.pure (transform value))).run state = _
  rfl

@[inline] def get : BuilderM σ (BuilderState σ) where
  run state := .ok (state, state)

@[inline] def set (state : BuilderState σ) : BuilderM σ Unit where
  run _ := .ok ((), state)

@[inline] def throw (error : MemoryError) : BuilderM σ α where
  run _ := .error error

end BuilderM

namespace BuilderState

def start {σ : LPSignature} (heap : Heap σ) : BuilderState σ :=
  { heap, varMap := [] }

def lookup {σ : LPSignature} [DecidableEq σ.vars]
    (varMap : List (σ.vars × Addr)) (identity : σ.vars) : Option Addr :=
  (varMap.find? fun entry => decide (entry.1 = identity)).map Prod.snd

end BuilderState

/-- Internal builder allocation.  It is exposed for local mechanism proofs;
runtime callers use the checked materialization entry points below. -/
def allocate {σ : LPSignature} (cell : Cell σ) : BuilderM σ Addr := do
  let state ← BuilderM.get
  let scratch : Memory σ := { heap := state.heap, trail := #[] }
  match scratch.allocate cell with
  | .error error => BuilderM.throw error
  | .ok (address, memory) =>
      BuilderM.set { state with heap := memory.heap }
      pure address

/-- Materialize one finite LP term into the current heap. -/
def materializeTermAux {σ : LPSignature} [DecidableEq σ.vars] :
    Term σ → BuilderM σ Addr
  | .var identity => do
      let state ← BuilderM.get
      match state.varMap.lookup identity with
      | some address => pure address
      | none =>
          let address ← allocate (.var identity none)
          let next ← BuilderM.get
          BuilderM.set
            { next with varMap := (identity, address) :: next.varMap }
          pure address
  | .const symbol => allocate (.const symbol)
  | .app symbol args => do
      let addresses ← (List.finRange (σ.functionArity symbol)).mapM fun index =>
        materializeTermAux (args index)
      allocate (.app symbol addresses.toArray)
termination_by term => term.size
decreasing_by
  exact Term.size_subterm _

/-- Materialize one atom while retaining the current clause's variable map. -/
def materializeAtomAux {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) : BuilderM σ (RuntimeAtom σ) := do
  let args ← (List.finRange (σ.relationArity atom.symbol)).mapM fun index =>
    materializeTermAux (atom.args index)
  pure { symbol := atom.symbol, args := args.toArray }

/-- Materialize a whole clause under one shared variable map. -/
def materializeClauseAux {σ : LPSignature} [DecidableEq σ.vars]
    (clause : Clause σ) : BuilderM σ (RuntimeClause σ) := do
  let head ← materializeAtomAux clause.head
  let body ← clause.body.mapM materializeAtomAux
  pure { head, body }

/-- Materialize a query goal list under one shared query-variable map. -/
def materializeGoalsAux {σ : LPSignature} [DecidableEq σ.vars]
    (goals : List (Atom σ)) : BuilderM σ (List (RuntimeAtom σ)) :=
  goals.mapM materializeAtomAux

/-- Output of a checked term materialization. -/
structure MaterializedTerm (σ : LPSignature) where
  memory : Memory σ
  root : Addr
  varMap : List (σ.vars × Addr)


/-- Output of checked goal materialization. -/
structure MaterializedGoals (σ : LPSignature) where
  memory : Memory σ
  goals : List (RuntimeAtom σ)
  varMap : List (σ.vars × Addr)


/-- Output of checked clause materialization. -/
structure MaterializedClause (σ : LPSignature) where
  memory : Memory σ
  clause : RuntimeClause σ
  varMap : List (σ.vars × Addr)


private def RuntimeAtom.decisionCode {σ : LPSignature}
    (atom : RuntimeAtom σ) : σ.relationSymbols × Array Addr :=
  (atom.symbol, atom.args)

private theorem RuntimeAtom.decisionCode_injective {σ : LPSignature} :
    Function.Injective (RuntimeAtom.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [RuntimeAtom.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.relationSymbols] :
    DecidableEq (RuntimeAtom σ) :=
  RuntimeAtom.decisionCode_injective.decidableEq

private def RuntimeClause.decisionCode {σ : LPSignature}
    (clause : RuntimeClause σ) : RuntimeAtom σ × List (RuntimeAtom σ) :=
  (clause.head, clause.body)

private theorem RuntimeClause.decisionCode_injective {σ : LPSignature} :
    Function.Injective (RuntimeClause.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [RuntimeClause.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.relationSymbols] :
    DecidableEq (RuntimeClause σ) :=
  RuntimeClause.decisionCode_injective.decidableEq

private def BuilderState.decisionCode {σ : LPSignature}
    (state : BuilderState σ) : Heap σ × List (σ.vars × Addr) :=
  (state.heap, state.varMap)

private theorem BuilderState.decisionCode_injective {σ : LPSignature} :
    Function.Injective (BuilderState.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [BuilderState.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (BuilderState σ) :=
  BuilderState.decisionCode_injective.decidableEq

private def MaterializedTerm.decisionCode {σ : LPSignature}
    (result : MaterializedTerm σ) : Memory σ × Addr × List (σ.vars × Addr) :=
  (result.memory, result.root, result.varMap)

private theorem MaterializedTerm.decisionCode_injective {σ : LPSignature} :
    Function.Injective (MaterializedTerm.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [MaterializedTerm.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (MaterializedTerm σ) :=
  MaterializedTerm.decisionCode_injective.decidableEq

private def MaterializedGoals.decisionCode {σ : LPSignature}
    (result : MaterializedGoals σ) :
    Memory σ × List (RuntimeAtom σ) × List (σ.vars × Addr) :=
  (result.memory, result.goals, result.varMap)

private theorem MaterializedGoals.decisionCode_injective {σ : LPSignature} :
    Function.Injective (MaterializedGoals.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [MaterializedGoals.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] :
    DecidableEq (MaterializedGoals σ) :=
  MaterializedGoals.decisionCode_injective.decidableEq

private def MaterializedClause.decisionCode {σ : LPSignature}
    (result : MaterializedClause σ) :
    Memory σ × RuntimeClause σ × List (σ.vars × Addr) :=
  (result.memory, result.clause, result.varMap)

private theorem MaterializedClause.decisionCode_injective {σ : LPSignature} :
    Function.Injective (MaterializedClause.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [MaterializedClause.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] :
    DecidableEq (MaterializedClause σ) :=
  MaterializedClause.decisionCode_injective.decidableEq

/-- Execute one builder action only across well-formed, well-shaped heaps. -/
def runChecked {σ : LPSignature} (action : BuilderM σ α)
    (heap : Heap σ) : Except MemoryError (α × BuilderState σ) :=
  if heap.checkWellFormed then
    if heap.checkWellShaped then
      match action.run (BuilderState.start heap) with
      | .error error => .error error
      | .ok result =>
          if result.2.heap.checkWellFormed then
            if result.2.heap.checkWellShaped then
              .ok result
            else
              .error .illFormedHeap
          else
            .error .illFormedHeap
    else
      .error .illFormedHeap
  else
    .error .illFormedHeap

/-- Mapping the value built by a checked action changes no heap validation or
builder state. -/
theorem runChecked_map {σ : LPSignature} (action : BuilderM σ α)
    (transform : α → β) (heap : Heap σ) :
    runChecked (transform <$> action) heap =
      (fun result => (transform result.1, result.2)) <$>
        runChecked action heap := by
  unfold runChecked
  by_cases hWellFormed : heap.checkWellFormed = true
  · simp only [hWellFormed, if_true]
    by_cases hWellShaped : heap.checkWellShaped = true
    · simp only [hWellShaped, if_true]
      cases hRun : action.run (BuilderState.start heap) with
      | error error =>
          simp [BuilderM.map_run, hRun]
      | ok result =>
          rcases result with ⟨value, state⟩
          by_cases hResultFormed : state.heap.checkWellFormed = true
          · simp only [hResultFormed, if_true]
            by_cases hResultShaped : state.heap.checkWellShaped = true
            · simp [BuilderM.map_run, hRun, hResultShaped]
              exact hResultFormed
            · simp [BuilderM.map_run, hRun, hResultShaped]
          · simp [BuilderM.map_run, hRun, hResultFormed]
    · simp [hWellShaped]
  · simp [hWellFormed]

/-- Append one finite term to an existing valid runtime memory. -/
def materializeTerm {σ : LPSignature} [DecidableEq σ.vars]
    (memory : Memory σ) (term : Term σ) :
    Except MemoryError (MaterializedTerm σ) :=
  match runChecked (materializeTermAux term) memory.heap with
  | .error error => .error error
  | .ok (root, state) =>
      if root < state.heap.size then
        .ok {
          memory := { heap := state.heap, trail := memory.trail }
          root
          varMap := state.varMap
        }
      else
        .error (.invalidAddress root)

/-- Materialize a query while preserving variable sharing across its goals. -/
def materializeGoals {σ : LPSignature} [DecidableEq σ.vars]
    (memory : Memory σ) (goals : List (Atom σ)) :
    Except MemoryError (MaterializedGoals σ) :=
  match runChecked (materializeGoalsAux goals) memory.heap with
  | .error error => .error error
  | .ok (runtimeGoals, state) =>
      if runtimeGoals.all fun atom => atom.checkWellFormed state.heap then
        .ok {
          memory := { heap := state.heap, trail := memory.trail }
          goals := runtimeGoals
          varMap := state.varMap
        }
      else
        .error .illFormedHeap

/-- Materialize one already-standardized clause.  A query engine calls this on
`clause.atScope activation`, so two live activations cannot share variables. -/
def materializeClause {σ : LPSignature} [DecidableEq σ.vars]
    (memory : Memory σ) (clause : Clause σ) :
    Except MemoryError (MaterializedClause σ) :=
  match runChecked (materializeClauseAux clause) memory.heap with
  | .error error => .error error
  | .ok (runtimeClause, state) =>
      if runtimeClause.checkWellFormed state.heap then
        .ok {
          memory := { heap := state.heap, trail := memory.trail }
          clause := runtimeClause
          varMap := state.varMap
        }
      else
        .error .illFormedHeap

theorem materializeTerm_root_valid {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {term : Term σ} {result : MaterializedTerm σ}
    (h : materializeTerm memory term = .ok result) :
    result.root < result.memory.heap.size := by
  simp only [materializeTerm] at h
  split at h
  · contradiction
  · split at h
    next hRoot =>
      cases h
      exact hRoot
    next _ => contradiction

theorem materializeGoals_wellFormed {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {goals : List (Atom σ)} {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result) :
    ∀ atom ∈ result.goals, atom.WellFormed result.memory.heap := by
  simp only [materializeGoals] at h
  split at h
  · contradiction
  · split at h
    next hGoals =>
      cases h
      intro atom hAtom
      exact RuntimeAtom.wellFormed_of_check
        (List.all_eq_true.mp hGoals atom hAtom)
    next _ => contradiction

theorem materializeClause_wellFormed {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {clause : Clause σ} {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result) :
    result.clause.WellFormed result.memory.heap := by
  simp only [materializeClause] at h
  split at h
  · contradiction
  · split at h
    next hClause =>
      cases h
      exact RuntimeClause.wellFormed_of_check hClause
    next _ => contradiction

/-- Term materialization cannot modify the caller's unification trail. -/
theorem materializeTerm_trail_exact {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {term : Term σ} {result : MaterializedTerm σ}
    (h : materializeTerm memory term = .ok result) :
    result.memory.trail = memory.trail := by
  simp only [materializeTerm] at h
  split at h
  · contradiction
  · split at h
    · cases h
      rfl
    · contradiction

/-- Query materialization cannot modify the caller's unification trail. -/
theorem materializeGoals_trail_exact {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result) :
    result.memory.trail = memory.trail := by
  simp only [materializeGoals] at h
  split at h
  · contradiction
  · split at h
    · cases h
      rfl
    · contradiction

/-- Clause activation cannot modify the caller's unification trail. -/
theorem materializeClause_trail_exact {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result) :
    result.memory.trail = memory.trail := by
  simp only [materializeClause] at h
  split at h
  · contradiction
  · split at h
    · cases h
      rfl
    · contradiction

end RuntimeMaterialize
end Mettapedia.Logic.LP
