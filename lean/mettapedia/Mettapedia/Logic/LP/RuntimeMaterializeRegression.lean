import Mettapedia.Logic.LP.RuntimeMaterialize

/-!
# Runtime clause-materialization regressions

The fixtures exercise the seam needed by clause selection: one standardized
clause is appended to a nonempty query heap, repeated variables share an
address across head and body, and another activation receives disjoint
addresses without changing the trail.
-/

namespace Mettapedia.Logic.LP.RuntimeMaterializeRegression

open RuntimeTerm RuntimeMaterialize

inductive MConst where
  | a
deriving DecidableEq, Repr

inductive MVar where
  | x
deriving DecidableEq, Repr

inductive MRel where
  | p
  | q
deriving DecidableEq, Repr

inductive MFun where
  | pair
deriving DecidableEq, Repr

def mSig : LPSignature where
  constants := MConst
  vars := MVar
  relationSymbols := MRel
  relationArity
    | .p => 1
    | .q => 1
  functionSymbols := MFun
  functionArity
    | .pair => 2

instance : DecidableEq mSig.vars := inferInstanceAs (DecidableEq MVar)
instance : DecidableEq mSig.scoped.vars :=
  inferInstanceAs (DecidableEq (ScopedVar MVar))
instance : DecidableEq mSig.scoped.constants :=
  inferInstanceAs (DecidableEq MConst)
instance : DecidableEq mSig.scoped.functionSymbols :=
  inferInstanceAs (DecidableEq MFun)
instance : DecidableEq mSig.scoped.relationSymbols :=
  inferInstanceAs (DecidableEq MRel)

def sourceClause : Clause mSig where
  head := { symbol := .p, args := fun _ => .var .x }
  body := [{ symbol := .q, args := fun _ => .var .x }]

def queryMemory : Memory mSig.scoped := {
  heap := #[.const .a]
  trail := #[{ address := 0, previous := .const .a }]
}

def firstActivation : Clause mSig.scoped := sourceClause.atScope 1
def secondActivation : Clause mSig.scoped := sourceClause.atScope 2

def firstRuntimeClause : RuntimeClause mSig.scoped := {
  head := { symbol := .p, args := #[1] }
  body := [{ symbol := .q, args := #[1] }]
}

def firstBuilderState : BuilderState mSig.scoped := {
  heap := #[.const .a, .var ⟨1, .x⟩ none]
  varMap := [(⟨1, .x⟩, 1)]
}

theorem first_builder_run_exact :
    (materializeClauseAux firstActivation).run
        (BuilderState.start queryMemory.heap) =
      .ok (firstRuntimeClause, firstBuilderState) := by
  simp [materializeClauseAux, materializeAtomAux, materializeTermAux,
    RuntimeMaterialize.allocate, BuilderM.bind, BuilderM.pure, BuilderM.get,
    BuilderM.set, Bind.bind, Pure.pure,
    Memory.allocate, Heap.append, BuilderState.start, ScopedVar.at,
    firstActivation, sourceClause, Clause.atScope,
    Clause.renameVars, Atom.renameVars, Term.renameVars, mSig,
    Cell.checkShape, Cell.references, List.finRange, List.mapM,
    List.mapM.loop,
    queryMemory, firstRuntimeClause,
    firstBuilderState]

def afterFirst : MaterializedClause mSig.scoped := {
  memory := { heap := firstBuilderState.heap, trail := queryMemory.trail }
  clause := firstRuntimeClause
  varMap := [(⟨1, .x⟩, 1)]
}

theorem first_activation_exact :
    materializeClause queryMemory firstActivation = .ok afterFirst := by
  have inputWellFormed : queryMemory.heap.checkWellFormed := by
    simp [queryMemory, Heap.checkWellFormed, Cell.references]
  have inputWellShaped : queryMemory.heap.checkWellShaped := by
    simp [queryMemory, Heap.checkWellShaped, Cell.checkShape]
  have outputWellFormed : firstBuilderState.heap.checkWellFormed := by
    simp [firstBuilderState, Heap.checkWellFormed, Cell.references]
  have outputWellShaped : firstBuilderState.heap.checkWellShaped := by
    simp [firstBuilderState, Heap.checkWellShaped, Cell.checkShape]
  have clauseWellFormed :
      firstRuntimeClause.checkWellFormed firstBuilderState.heap := by
    simp [firstRuntimeClause, firstBuilderState,
      RuntimeClause.checkWellFormed, RuntimeAtom.checkWellFormed, mSig]
  have checkedRun :
      runChecked (materializeClauseAux firstActivation) queryMemory.heap =
        .ok (firstRuntimeClause, firstBuilderState) := by
    simp only [runChecked, if_pos inputWellFormed, if_pos inputWellShaped,
      first_builder_run_exact, if_pos outputWellFormed,
      if_pos outputWellShaped]
  simp only [materializeClause, checkedRun, if_pos clauseWellFormed]
  rfl

/-- Head and body share the same freshly allocated variable cell. -/
theorem repeated_clause_variable_shares_address :
    afterFirst.clause.head.args = #[1] ∧
      afterFirst.clause.body.map (·.args) = [#[1]] := by
  decide

def afterSecond : MaterializedClause mSig.scoped := {
  memory := {
    heap := #[.const .a, .var ⟨1, .x⟩ none, .var ⟨2, .x⟩ none]
    trail := #[{ address := 0, previous := .const .a }]
  }
  clause := {
    head := { symbol := .p, args := #[2] }
    body := [{ symbol := .q, args := #[2] }]
  }
  varMap := [(⟨2, .x⟩, 2)]
}

theorem second_builder_run_exact :
    (materializeClauseAux secondActivation).run
        (BuilderState.start afterFirst.memory.heap) =
      .ok (afterSecond.clause,
        { heap := afterSecond.memory.heap, varMap := afterSecond.varMap }) := by
  simp [materializeClauseAux, materializeAtomAux, materializeTermAux,
    RuntimeMaterialize.allocate, BuilderM.bind, BuilderM.pure, BuilderM.get,
    BuilderM.set, Bind.bind, Pure.pure,
    Memory.allocate, Heap.append, BuilderState.start, ScopedVar.at,
    secondActivation, sourceClause, Clause.atScope,
    Clause.renameVars, Atom.renameVars, Term.renameVars, mSig,
    Cell.checkShape, Cell.references, List.finRange, List.mapM,
    List.mapM.loop, afterFirst, firstBuilderState, firstRuntimeClause,
    afterSecond]

theorem second_activation_exact :
    materializeClause afterFirst.memory secondActivation = .ok afterSecond := by
  let secondState : BuilderState mSig.scoped :=
    { heap := afterSecond.memory.heap, varMap := afterSecond.varMap }
  have inputWellFormed : afterFirst.memory.heap.checkWellFormed := by
    simp [afterFirst, firstBuilderState, Heap.checkWellFormed, Cell.references]
  have inputWellShaped : afterFirst.memory.heap.checkWellShaped := by
    simp [afterFirst, firstBuilderState, Heap.checkWellShaped, Cell.checkShape]
  have outputWellFormed : secondState.heap.checkWellFormed := by
    simp [secondState, afterSecond, Heap.checkWellFormed, Cell.references]
  have outputWellShaped : secondState.heap.checkWellShaped := by
    simp [secondState, afterSecond, Heap.checkWellShaped, Cell.checkShape]
  have clauseWellFormed :
      afterSecond.clause.checkWellFormed secondState.heap := by
    simp [secondState, afterSecond, RuntimeClause.checkWellFormed,
      RuntimeAtom.checkWellFormed, mSig]
  have checkedRun :
      runChecked (materializeClauseAux secondActivation) afterFirst.memory.heap =
        .ok (afterSecond.clause, secondState) := by
    simp only [runChecked, if_pos inputWellFormed, if_pos inputWellShaped,
      second_builder_run_exact, secondState, if_pos outputWellFormed,
      if_pos outputWellShaped]
  simp only [materializeClause, checkedRun, if_pos clauseWellFormed,
    secondState]
  rfl

/-- The second live activation gets a distinct cell and allocation never
touches the trail. -/
theorem live_activations_are_disjoint_and_untrailed :
    afterFirst.varMap = [(⟨1, .x⟩, 1)] ∧
      afterSecond.varMap = [(⟨2, .x⟩, 2)] ∧
      afterSecond.memory.trail = queryMemory.trail := by
  constructor
  · rfl
  constructor <;> rfl

def sharedCompound : Term mSig.scoped :=
  .app .pair fun _ => .var ⟨7, .x⟩

def afterCompound : MaterializedTerm mSig.scoped := {
  memory := {
    heap := #[
      .const .a,
      .var ⟨7, .x⟩ none,
      .app .pair #[1, 1]
    ]
    trail := #[{ address := 0, previous := .const .a }]
  }
  root := 2
  varMap := [(⟨7, .x⟩, 1)]
}

/-- Recursive materialization shares a repeated variable within a compound,
appends its parent after both children, and preserves a nonempty trail. -/
theorem shared_compound_materializes_exactly :
    materializeTerm queryMemory sharedCompound = .ok afterCompound := by
  simp [materializeTerm, runChecked, materializeTermAux,
    RuntimeMaterialize.allocate, BuilderM.bind, BuilderM.pure, BuilderM.get,
    BuilderM.set, Bind.bind, Pure.pure, Memory.allocate, Heap.append,
    BuilderState.start, sharedCompound, afterCompound,
    queryMemory, mSig, Cell.checkShape, Cell.references,
    Heap.checkWellFormed, Heap.checkWellShaped, List.finRange, List.mapM,
    List.mapM.loop]

/-- The nonempty-trail witness makes the structural preservation theorem
observable rather than vacuous. -/
theorem shared_compound_retains_nonempty_trail :
    afterCompound.memory.trail = queryMemory.trail ∧
      afterCompound.memory.trail.size = 1 := by
  constructor <;> rfl

end Mettapedia.Logic.LP.RuntimeMaterializeRegression
