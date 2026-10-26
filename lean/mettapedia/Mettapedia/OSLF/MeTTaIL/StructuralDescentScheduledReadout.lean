import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledCoverage

/-!
# Public resumable readout for structurally admitted scoped execution

The environment fixes the original language, provider rows, free-variable
sorts, authored occurrence specifications and binder operation. A snapshot
retains individual matcher/query continuations, ordered complete receipts,
unresolved obligations and spent work. Its initial recursion depth is derived
from the source, and its declaration frontier is the original declaration list.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax GeneralPremise PatternTreeSize

/-- The shared scheduler uses the depth earned by the selected source measure. -/
def sourceGoalWith (measure : Pattern → Nat) (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) : Goal :=
  .steps (measure source) bound type source environment.language.rewrites.length

def readReceiptWith {matcher : MatchingExecution} (measure : Pattern → Nat)
    {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (result : Interpreted.Result matcher environment (sourceGoalWith measure environment bound type source)) :
    Execution.RootAnswer environment bound type source matcher :=
  match result with
  | .steps index trace captured completed history target _ valid =>
      ⟨index,trace,captured,completed,history,target,valid⟩

def receiptsWith {matcher : MatchingExecution} (measure : Pattern → Nat)
    {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (snapshot : State environment (sourceGoalWith measure environment bound type source) matcher) :
    List (Execution.RootAnswer environment bound type source matcher) :=
  snapshot.answers.map (readReceiptWith measure)

def finishSourceWith {matcher : MatchingExecution} (cost : matcher.CursorCost)
    (measure : Pattern → Nat) (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) :
    State environment (sourceGoalWith measure environment bound type source) matcher :=
  finishWith cost environment (sourceGoalWith measure environment bound type source)

theorem finishSourceWith_is_run {matcher : MatchingExecution} (cost : matcher.CursorCost)
    (measure : Pattern → Nat) (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) :
    finishSourceWith cost measure environment bound type source =
      run environment (sourceGoalWith measure environment bound type source)
        (treeStart cost environment (sourceGoalWith measure environment bound type source)).cost
        (start environment (sourceGoalWith measure environment bound type source) matcher) := rfl

private theorem root_index_boundWith {matcher : MatchingExecution} {environment : Environment}
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (answer : Execution.RootAnswer environment bound type source matcher) :
    answer.index < environment.language.rewrites.length := by
  cases answer.valid with
  | fire declared _ _ _ _ _ _ _ _ => exact (List.getElem?_eq_some_iff.mp declared).1

theorem drained_receiptsWith_complete {matcher : MatchingExecution} (laws : matcher.CursorLaws)
    (represented : Represents matcher) {measure : Pattern → Nat} {environment : Environment}
    (certificate : SourceMeasureCertificate matcher environment measure)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (fuel : Nat)
    (drained : (run environment (sourceGoalWith measure environment bound type source) fuel
      (start environment (sourceGoalWith measure environment bound type source) matcher)).agenda = [])
    (answer : Execution.RootAnswer environment bound type source matcher) :
    answer ∈ receiptsWith measure
      (run environment (sourceGoalWith measure environment bound type source) fuel
        (start environment (sourceGoalWith measure environment bound type source) matcher)) := by
  let wanted : Interpreted.Result matcher environment (sourceGoalWith measure environment bound type source) :=
    .steps answer.index answer.trace answer.captured answer.completed answer.history answer.target
      (root_index_boundWith answer) answer.valid
  have ordered : wanted.ordered = true := by
    have bounded := Measured.firing_depth_bound certificate source bound type answer
    simpa [wanted,Interpreted.Result.ordered,Execution.RootAnswer.requiredDepth,sourceGoalWith] using bounded
  have covered := answers_complete_of_drained laws represented environment _ fuel wanted ordered drained
  exact List.mem_map.mpr ⟨wanted,covered,rfl⟩

theorem finishSourceWith_receipts_complete {matcher : MatchingExecution} (cost : matcher.CursorCost)
    (laws : matcher.CursorLaws) (represented : Represents matcher)
    {measure : Pattern → Nat} {environment : Environment}
    (certificate : SourceMeasureCertificate matcher environment measure)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer environment bound type source matcher) :
    answer ∈ receiptsWith measure (finishSourceWith cost measure environment bound type source) := by
  rw [finishSourceWith_is_run]
  exact drained_receiptsWith_complete laws represented certificate bound type source _
    (finishWith_settled cost environment (sourceGoalWith measure environment bound type source)) answer

/-- The source-bound join preserves the entire selected-interpreter receipt. -/
theorem finishSourceWith_occurrences {matcher : MatchingExecution} (cost : matcher.CursorCost)
    (laws : matcher.CursorLaws) (represented : Represents matcher)
    {measure : Pattern → Nat} {environment : Environment}
    (certificate : SourceMeasureCertificate matcher environment measure)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (trace : List matcher.Choice) (captured completed : ScopedRuleMatching.Assignment)
    (history : List (Event matcher.Choice)) (target : Pattern) :
    (∃ answer ∈ receiptsWith measure (finishSourceWith cost measure environment bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    GeneralPremise.Interpreted.RootFiring matcher.meaning environment bound type source index trace
      captured completed history target := by
  constructor
  · rintro ⟨answer,_,rfl,rfl,rfl,rfl,rfl,rfl⟩
    exact answer.valid
  · intro valid
    exact ⟨⟨index,trace,captured,completed,history,target,valid⟩,
      finishSourceWith_receipts_complete cost laws represented certificate bound type source _,
      rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms finishSourceWith_is_run
#print axioms root_index_boundWith
#print axioms drained_receiptsWith_complete
#print axioms finishSourceWith_receipts_complete
#print axioms finishSourceWith_occurrences

/-- All declaration positions are searched. The caller supplies neither a
complete child oracle nor an admissibility predicate. -/
def sourceGoal (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) : Goal :=
  sourceGoalWith nodes environment bound type source

abbrev Snapshot (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) :=
  State environment (sourceGoal environment bound type source)

def begin (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) : Snapshot environment bound type source :=
  start environment (sourceGoal environment bound type source)

def resume (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (fuel : Nat)
    (snapshot : Snapshot environment bound type source) : Snapshot environment bound type source :=
  run environment (sourceGoal environment bound type source) fuel snapshot

def readReceipt {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (result : Result environment (sourceGoal environment bound type source)) :
    Execution.RootAnswer environment bound type source :=
  readReceiptWith nodes result

def receipts {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (snapshot : Snapshot environment bound type source) :
    List (Execution.RootAnswer environment bound type source) :=
  receiptsWith nodes snapshot

def finishSource (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) : Snapshot environment bound type source :=
  finishSourceWith MatchingExecution.ordinaryCursorCost nodes environment bound type source

/-- This computes the actual retained transition-tree work, not a term-domain
enumeration or a one-tick call to the eager reference interpreter. -/
def completeBudget (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) : Nat :=
  (treeStart _root_.Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinaryCursorCost environment (sourceGoal environment bound type source)).cost

theorem finishSource_is_run (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) :
    finishSource environment bound type source =
      resume environment bound type source (completeBudget environment bound type source)
        (begin environment bound type source) := rfl

theorem resume_add (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (first second : Nat)
    (snapshot : Snapshot environment bound type source) :
    resume environment bound type source (first + second) snapshot =
      resume environment bound type source second
        (resume environment bound type source first snapshot) :=
  run_add environment _ first second snapshot

theorem receipts_preserved (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (fuel : Nat)
    (snapshot : Snapshot environment bound type source) :
    Scheduler.Prefix (receipts snapshot)
      (receipts (resume environment bound type source fuel snapshot)) := by
  obtain ⟨suffix, ordered⟩ := receipts_prefix environment _ fuel snapshot
  refine ⟨suffix.map (readReceiptWith nodes), ?_⟩
  change (run environment (sourceGoal environment bound type source) fuel snapshot).answers.map
    (readReceiptWith nodes) = snapshot.answers.map (readReceiptWith nodes) ++ suffix.map (readReceiptWith nodes)
  rw [ordered]
  exact List.map_append

theorem root_index_bound {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source : Pattern}
    (answer : Execution.RootAnswer environment bound type source) :
    answer.index < environment.language.rewrites.length := by
  cases answer.valid with
  | fire declared _ _ _ _ _ _ _ _ => exact (List.getElem?_eq_some_iff.mp declared).1

/-- Any finite independent firing is retained once all actual pending work
has drained. This statement does not assume scheduler completeness as an
interface field; coverage comes from transition preservation and structural
source descent. Unresolved diagnostics remain separately visible. -/
theorem drained_receipts_complete (environment : Environment)
    (admitted : checkEnvironment environment = true) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (fuel : Nat)
    (drained : (resume environment bound type source fuel
      (begin environment bound type source)).agenda = [])
    (answer : Execution.RootAnswer environment bound type source) :
    answer ∈ receipts (resume environment bound type source fuel
      (begin environment bound type source)) := by
  let wanted : Result environment (sourceGoal environment bound type source) :=
    .steps answer.index answer.trace answer.captured answer.completed answer.history
      answer.target (root_index_bound answer) answer.valid
  have bounded : Interpreted.Result.ordered wanted = true := by
    have earned := firing_depth_bound environment admitted source bound type answer
    simpa [wanted, Interpreted.Result.ordered, Execution.RootAnswer.requiredDepth, sourceGoal, sourceGoalWith] using earned
  have initial : StateAccepts MatchingExecution.ordinaryCursorLaws
      (begin environment bound type source) wanted := by
    right
    exact ⟨_, List.mem_cons_self, wanted, bounded, rfl⟩
  have covered := run_covers MatchingExecution.ordinaryCursorLaws
    MatchingExecution.ordinary_answer_representation fuel initial
  rcases covered with emitted | ⟨task, member, _⟩
  · exact List.mem_map.mpr ⟨wanted, emitted, rfl⟩
  · change task ∈ (resume environment bound type source fuel
      (begin environment bound type source)).agenda at member
    rw [drained] at member
    exact False.elim (List.not_mem_nil member)

theorem finishSource_receipts_complete (environment : Environment)
    (admitted : checkEnvironment environment = true) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern)
    (answer : Execution.RootAnswer environment bound type source) :
    answer ∈ receipts (finishSource environment bound type source) := by
  rw [finishSource_is_run]
  exact drained_receipts_complete environment admitted bound type source _
    (finish_settled environment (sourceGoal environment bound type source)) answer

/-- Coverage retains the complete occurrence receipt: declaration, matching
trace, both assignments, ordered premise origins and actual target. -/
theorem finishSource_occurrences (environment : Environment)
    (admitted : checkEnvironment environment = true) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment) (history : List Event) (target : Pattern) :
    (∃ answer ∈ receipts (finishSource environment bound type source),
      answer.index = index ∧ answer.trace = trace ∧ answer.captured = captured ∧
      answer.completed = completed ∧ answer.history = history ∧ answer.target = target) ↔
    RootFiring environment bound type source index trace captured completed history target := by
  constructor
  · rintro ⟨answer, _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact answer.valid
  · intro valid
    exact ⟨⟨index, trace, captured, completed, history, target, valid⟩,
      finishSource_receipts_complete environment admitted bound type source _,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
