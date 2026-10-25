import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFrames
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQuery
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFiniteWork
import Mettapedia.Coalgebra.CoherentPrefixTower

/-!
# Fine-grained recursive scoped execution

Each tick advances one scheduler frame or one embedded matcher/query tick.
Every child search visits the original declaration list. Recursive calls use
a smaller semantic depth rather than a declaration-index restriction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

def delivered {matcher : MatchingExecution} (environment : Environment) (outer : Goal) {goal : Goal}
    (result : Interpreted.Result matcher environment goal) (continuation : Interpreted.Continuation matcher environment goal outer) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match continuation with
  | .done _ => { answers := [result] }
  | .nextPremise depth context premise premises initial tail =>
      match result with
      | .premise assignment event valid =>
          { tasks := [.evaluate (.premises depth context.next premises assignment)
              (.prepend depth context premise premises initial assignment event valid tail)] }
  | .prepend depth _ _ _ _ _ event head tail =>
      match result with
      | .premises assignment events valid =>
          { tasks := [.deliver (.premises assignment (event :: events) (.cons head valid)) tail] }
  | .quantifier depth context _ _ _ _ kind _ read tail =>
      match result with
      | .quantified assignment events valid =>
          { tasks := [.deliver (.premise assignment
              (.quantified context.premiseIndex context.quantifierDepth kind events)
              (.quantified read valid)) tail] }
  | .element depth context parameter body index element elements initial localTyped tail =>
      match result with
      | .premise assignment event valid =>
          { tasks := [.evaluate
              (.quantified depth context parameter body (index + 1) elements
                initial)
              (.prependElement depth context parameter body index element elements initial assignment
                event localTyped valid tail)] }
  | .prependElement depth _ _ _ index element _ _ _ event localTyped head tail =>
      match result with
      | .quantified assignment events valid =>
          { tasks := [.deliver
              (.quantified assignment ((index, element, [event]) :: events) (.cons localTyped head valid)) tail] }
  | .rootBody depth bound type _ index rule spec declared specified admitted sorted trace captured
      matched capturedTyped tail =>
      match result with
      | .premises completed events valid =>
          match converted : reductWith? (ScopedReflectiveExecution.binderOperation
              environment.reflection rule) rule spec bound.length completed with
          | none => { unresolved := [.targetProjection index] }
          | some target =>
              if checked : checkOpenPatternWellSorted environment.language environment.free
                  bound type target then
                { tasks := [.deliver (.root trace captured completed events target
                    (.fire declared specified admitted sorted matched capturedTyped valid
                      converted (checkOpenPatternWellSorted_sound checked))) tail] }
              else {}
  | .searchedRoot depth _ _ _ index _ earlier tail =>
      match result with
      | .root trace captured completed events target valid =>
          { tasks := [.deliver (.steps index trace captured completed events target earlier valid) tail] }
  | .stepped depth call tail =>
      match result with
      | .steps index trace captured completed events target _ valid =>
          let request : GeneralScopedMatchMachine.Request :=
            ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
              [], call.binders.length, call.initial, call.targetSchema, target⟩
          { tasks := [.targetMatch {
              depth := depth
              call := call
              index := index
              trace := trace
              captured := captured
              completed := completed
              history := events
              target := target
              valid := valid
              state := matcher.start request
              reachable := matcher.start_reachable request
              cursor := 0
              tail := tail }] }

def evaluatePremise {matcher : MatchingExecution} (environment : Environment) (outer : Goal) (depth : Nat) (context : Context)
    (premise : Premise) (initial : Assignment)
    (tail : Interpreted.Continuation matcher environment (.premise depth context premise initial) outer) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match premise with
  | .relationQuery relation arguments =>
      let request : Query.Request := ⟨context, relation, arguments, initial⟩
      { tasks := [.query depth request (Query.start environment request matcher) 0 tail] }
  | .freshness condition =>
      match read : freshnessSubject? context.rule context.spec context.bound context.premiseIndex
          context.quantifierDepth initial condition with
      | none => { unresolved := [.freshnessProjection context.premiseIndex context.quantifierDepth] }
      | some (atom, subject) =>
          if checked : Substitution.isFresh atom subject then
            { tasks := [.deliver (.premise initial
                (.freshness context.premiseIndex context.quantifierDepth atom subject)
                (.freshness read ((syntactic_freshness_iff atom subject).mp checked))) tail] }
          else {}
  | .forAll collection parameter body =>
      match read : finiteCollection? context.bound.length initial collection with
      | none => { unresolved := [.collectionProjection context.premiseIndex context.quantifierDepth collection] }
      | some (kind, elements) =>
          { tasks := [.evaluate (.quantified depth context parameter body 0 elements initial)
              (.quantifier depth context collection parameter body initial kind elements read tail)] }
  | .congruence source target =>
      match typed : sourceType? environment.language context.rule source with
      | none => { unresolved := [.stepSort context.premiseIndex context.quantifierDepth] }
      | some type =>
          match interpreted : instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial source with
          | none => { unresolved := [.stepProjection context.premiseIndex context.quantifierDepth] }
          | some actualSource =>
              let call : StepCall environment matcher := {
                context := context
                premise := .congruence source target
                initial := initial
                binders := []
                type := type
                source := actualSource
                targetSchema := target
                conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped =>
                  .step typed interpreted child matching finalTyped }
              { tasks := [.evaluate (.steps depth context.bound type actualSource environment.language.rewrites.length)
                  (.stepped depth call tail)] }
  | .scopedStep step =>
      match interpreted : instantiateAt? context.rule context.spec context.bound.length
          (context.site 0) [] step.binders.length initial step.source with
      | none => { unresolved := [.stepProjection context.premiseIndex context.quantifierDepth] }
      | some actualSource =>
          let call : StepCall environment matcher := {
            context := context
            premise := .scopedStep step
            initial := initial
            binders := step.binders
            type := step.resultType
            source := actualSource
            targetSchema := step.target
            conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped =>
              .scopedStep interpreted child matching finalTyped }
          { tasks := [.evaluate
              (.steps depth (step.binders ++ context.bound) step.resultType actualSource environment.language.rewrites.length)
              (.stepped depth call tail)] }

def evaluateRoot {matcher : MatchingExecution} (environment : Environment) (outer : Goal) (depth : Nat) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Interpreted.Continuation matcher environment (.root depth bound type source index) outer) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match depth with
  | 0 => { unresolved := [.depthExhausted index] }
  | depth + 1 =>
      match declared : environment.language.rewrites[index]? with
      | none => { unresolved := [.ruleUnavailable index] }
      | some rule =>
          match specified : specification? environment index with
          | none => { unresolved := [.bindingUnavailable index] }
          | some spec =>
              if admitted : admittedFor rule spec then
                if checked : checkOpenPatternWellSorted environment.language environment.free bound type source then
                  let request : GeneralScopedMatchMachine.Request :=
                    ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
                  { tasks := [.rootMatch {
                      depth := depth
                      bound := bound
                      type := type
                      source := source
                      index := index
                      rule := rule
                      spec := spec
                      declared := declared
                      specified := specified
                      admitted := admitted
                      sorted := checkOpenPatternWellSorted_sound checked
                      state := matcher.start request
                      reachable := matcher.start_reachable request
                      cursor := 0
                      tail := tail }] }
                else { unresolved := [.sourceRejected index] }
              else { unresolved := [.bindingRejected index] }

def evaluate {matcher : MatchingExecution} (environment : Environment) (outer : Goal) (goal : Goal)
    (tail : Interpreted.Continuation matcher environment goal outer) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match goal with
  | .premise depth context premise initial => evaluatePremise environment outer depth context premise initial tail
  | .premises depth context premises initial =>
      match premises with
      | [] => { tasks := [.deliver (.premises initial [] .nil) tail] }
      | premise :: premises =>
          { tasks := [.evaluate (.premise depth context premise initial)
              (.nextPremise depth context premise premises initial tail)] }
  | .quantified depth context parameter body index elements initial =>
      match elements with
      | [] => { tasks := [.deliver (.quantified initial [] .nil) tail] }
      | element :: elements =>
          let assignment := bindParameter parameter (localValue context.bound element) initial
          if checked : checkTypedAssignment environment context.quantified assignment then
            { tasks := [.evaluate (.premise depth context.quantified body assignment)
                (.element depth context parameter body index element elements initial
                  (checkTypedAssignment_sound checked) tail)] }
          else { unresolved := [.quantifiedAssignment context.premiseIndex context.quantifierDepth index] }
  | .root depth bound type source index => evaluateRoot environment outer depth bound type source index tail
  | .steps depth bound type source limit => { tasks := [.scanChildren depth bound type source limit 0 tail] }

def expandQuery {matcher : MatchingExecution} (environment : Environment) (outer : Goal) (depth : Nat) (request : Query.Request)
    (state : Query.State environment request matcher) (cursor : Nat)
    (tail : Interpreted.Continuation matcher environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match _found : state.answers[cursor]? with
  | some answer =>
      { tasks := [
          .deliver (.premise answer.assignment
            (.query request.context.premiseIndex request.context.quantifierDepth
              answer.rowIndex answer.origins) (.query answer.valid)) tail,
          .query depth request state (cursor + 1) tail] }
  | none =>
      if state.agenda.isEmpty then { unresolved := state.unresolved.map Obligation.query }
      else { tasks := [.query depth request (Query.tick environment request state) cursor tail] }

/-- The shared scheduled continuation after any root matcher backend returns a
checked answer. The backend supplies only matching evidence; this continuation
owns typed captures, premises and the final reduct. -/
def continueRootAnswer {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answer : matcher.Answer)
    (valid : matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer))
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  let context : Context := ⟨index, rule, spec, bound, 0, 0⟩
  if checked : checkTypedAssignment environment context (matcher.assignment answer) then
    { tasks :=
        .evaluate (.premises depth context rule.premises (matcher.assignment answer))
          (.rootBody depth bound type source index rule spec declared specified admitted sorted
            (matcher.trace answer) (matcher.assignment answer) valid (checkTypedAssignment_sound checked) tail) :: next }
  else { tasks := next }

@[simp] theorem continueRootAnswer_answers {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answer : matcher.Answer)
    (valid : matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer))
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    (continueRootAnswer environment outer depth bound type source index rule spec declared
      specified admitted sorted answer valid tail next).answers = [] := by
  unfold continueRootAnswer
  dsimp only
  split <;> rfl

@[simp] theorem continueRootAnswer_unresolved {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answer : matcher.Answer)
    (valid : matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer))
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    (continueRootAnswer environment outer depth bound type source index rule spec declared
      specified admitted sorted answer valid tail next).unresolved = [] := by
  unfold continueRootAnswer
  dsimp only
  split <;> rfl

/-- Fold a finite certified matcher frontier through the shared root
continuation.  Backends may enumerate answers differently, while typing,
premises, reducts and publication remain identical. -/
def continueRootAnswers {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answers : List {answer : matcher.Answer //
      matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer)})
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match answers with
  | [] => { tasks := next }
  | answer :: rest =>
      let later := continueRootAnswers environment outer depth bound type source index
        rule spec declared specified admitted sorted rest tail next
      continueRootAnswer environment outer depth bound type source index rule spec
        declared specified admitted sorted answer.val answer.property tail later.tasks

@[simp] theorem continueRootAnswers_nil {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    continueRootAnswers environment outer depth bound type source index rule spec
      declared specified admitted sorted [] tail next = { tasks := next } := rfl

@[simp] theorem continueRootAnswers_answers {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answers : List {answer : matcher.Answer //
      matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer)})
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    (continueRootAnswers environment outer depth bound type source index rule spec declared
      specified admitted sorted answers tail next).answers = [] := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      simp only [continueRootAnswers, continueRootAnswer_answers]

@[simp] theorem continueRootAnswers_unresolved {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (depth : Nat) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    (answers : List {answer : matcher.Answer //
      matcher.meaning.Matches ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
      (matcher.trace answer) (matcher.assignment answer)})
    (tail : Interpreted.Continuation matcher environment (.root (depth + 1) bound type source index) outer)
    (next : List (Interpreted.Task matcher environment outer)) :
    (continueRootAnswers environment outer depth bound type source index rule spec declared
      specified admitted sorted answers tail next).unresolved = [] := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      simp only [continueRootAnswers, continueRootAnswer_unresolved]

def expandRootMatch {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer matcher) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match found : (matcher.answers frame.state)[frame.cursor]? with
  | some answer =>
      let tail := Interpreted.Task.rootMatch { frame with cursor := frame.cursor + 1 }
      continueRootAnswer environment outer frame.depth frame.bound frame.type frame.source
        frame.index frame.rule frame.spec frame.declared frame.specified frame.admitted frame.sorted
        answer (matcher.answers_sound frame.reachable
          (List.mem_of_getElem? found)) frame.tail [tail]
  | none =>
      if matcher.complete frame.state then {}
      else
        let request : GeneralScopedMatchMachine.Request :=
          ⟨frame.rule, frame.spec, frame.bound.length, .left, [], 0, [], frame.rule.left, frame.source⟩
        { tasks := [.rootMatch { frame with
            state := matcher.tick request frame.state
            reachable := matcher.tick_reachable frame.reachable }] }

def expandTargetMatch {matcher : MatchingExecution} (environment : Environment) (outer : Goal)
    (frame : TargetMatchFrame environment outer matcher) :
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation :=
  match found : (matcher.answers frame.state)[frame.cursor]? with
  | some answer =>
      let tail := Interpreted.Task.targetMatch { frame with cursor := frame.cursor + 1 }
      if checked : checkTypedAssignment environment frame.call.context (matcher.assignment answer) then
        have valid := matcher.answers_sound frame.reachable
          (List.mem_of_getElem? found)
        { tasks := [
            .deliver (.premise (matcher.assignment answer)
              (.child frame.call.context.premiseIndex frame.call.context.quantifierDepth frame.index
                (frame.call.binders ++ frame.call.context.bound) frame.call.source frame.target
                frame.trace (matcher.trace answer) frame.captured frame.completed frame.history)
              (frame.call.conclude _ _ _ _ _ _ _ _ frame.valid valid
                (checkTypedAssignment_sound checked))) frame.tail, tail] }
      else { tasks := [tail] }
  | none =>
      if matcher.complete frame.state then {}
      else
        let request : GeneralScopedMatchMachine.Request :=
          ⟨frame.call.context.rule, frame.call.context.spec, frame.call.context.bound.length,
            frame.call.context.site 1, [], frame.call.binders.length, frame.call.initial,
            frame.call.targetSchema, frame.target⟩
        { tasks := [.targetMatch { frame with
            state := matcher.tick request frame.state
            reachable := matcher.tick_reachable frame.reachable }] }

def expand {matcher : MatchingExecution} (environment : Environment) (outer : Goal) : Interpreted.Task matcher environment outer →
    Scheduler.Expansion (Interpreted.Task matcher environment outer) (Interpreted.Result matcher environment outer) Obligation
  | .evaluate goal tail => evaluate environment outer goal tail
  | .deliver result tail => delivered environment outer result tail
  | .query depth request state cursor tail => expandQuery environment outer depth request state cursor tail
  | .rootMatch frame => expandRootMatch environment outer frame
  | .targetMatch frame => expandTargetMatch environment outer frame
  | .scanChildren depth bound type source limit cursor tail =>
      if earlier : cursor < limit then
        { tasks := [
            .evaluate (.root depth bound type source cursor)
              (.searchedRoot depth bound type source cursor limit earlier tail),
            .scanChildren depth bound type source limit (cursor + 1) tail] }
      else {}

def start (environment : Environment) (goal : Goal)
    (matcher : MatchingExecution := MatchingExecution.ordinary) : State environment goal matcher :=
  { agenda := [.evaluate goal (.done goal)] }

def tick {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (state : State environment goal matcher) :
    State environment goal matcher := Scheduler.tick (expand environment goal) state

def run {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (fuel : Nat) (state : State environment goal matcher) :
    State environment goal matcher := Scheduler.run (expand environment goal) fuel state

def complete {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (state : State environment goal matcher) : Bool :=
  Scheduler.complete state

theorem run_add {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (first second : Nat)
    (state : State environment goal matcher) :
    run environment goal (first + second) state =
      run environment goal second (run environment goal first state) :=
  Scheduler.run_add _ _ _ _

theorem receipts_prefix {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (fuel : Nat)
    (state : State environment goal matcher) :
    Scheduler.Prefix state.answers (run environment goal fuel state).answers :=
  Scheduler.run_answers_prefix _ _ _

theorem work_add {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (first second : Nat)
    (state : State environment goal matcher) :
    Scheduler.spent (expand environment goal) (first + second) state =
      Scheduler.spent (expand environment goal) first state +
      Scheduler.spent (expand environment goal) second (run environment goal first state) :=
  Scheduler.spent_add _ _ _ _

/-- The real scheduled frames instantiate the shared continuation law.
Observations retain obligations and the entire agenda, not just endpoints. -/
def trajectory {matcher : MatchingExecution} (environment : Environment) (goal : Goal) (state : State environment goal matcher) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory (run environment goal) state :=
  Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory.canonical
    (run environment goal) state (fun _ => rfl) (run_add environment goal)

theorem trajectory_answers_prefix {matcher : MatchingExecution} (environment : Environment) (goal : Goal)
    (state : State environment goal matcher) (first extra : Nat) :
    ((trajectory environment goal state).observation first).answers <+:
      ((trajectory environment goal state).observation (first + extra)).answers := by
  apply (trajectory environment goal state).observer_prefix_after_resume (·.answers)
  intro fuel current
  obtain ⟨tail, appended⟩ := receipts_prefix environment goal fuel current
  exact ⟨tail, appended.symm⟩

theorem trajectory_obligations_prefix {matcher : MatchingExecution} (environment : Environment) (goal : Goal)
    (state : State environment goal matcher) (first extra : Nat) :
    ((trajectory environment goal state).observation first).unresolved <+:
      ((trajectory environment goal state).observation (first + extra)).unresolved := by
  apply (trajectory environment goal state).observer_prefix_after_resume (·.unresolved)
  intro fuel current
  obtain ⟨tail, appended⟩ := Scheduler.run_obligations_prefix (expand environment goal) fuel current
  exact ⟨tail, appended.symm⟩

/-- A drained agenda stays fixed even when unresolved obligations block
completion. Budget exhaustion alone is not this settlement condition. -/
theorem trajectory_settled {matcher : MatchingExecution} (environment : Environment) (goal : Goal)
    (state : State environment goal matcher) (first extra : Nat)
    (settled : ((trajectory environment goal state).observation first).agenda = []) :
    (trajectory environment goal state).observation (first + extra) =
      (trajectory environment goal state).observation first := by
  apply (trajectory environment goal state).observation_constant_after_settlement
    (fun current => current.agenda = [])
  · intro current idle fuel
    exact Scheduler.run_idle (expand environment goal) fuel current idle
  · exact settled

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
