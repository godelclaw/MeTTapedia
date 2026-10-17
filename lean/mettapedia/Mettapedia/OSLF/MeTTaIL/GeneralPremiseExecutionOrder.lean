import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryOrder

/-!
# The order in which premise execution delivers its results

`Execution.results` evaluates a premise goal in direct style. Premises run from
left to right, matcher answers and provider rows are read in emission order,
and child searches visit declarations in declaration order. It is defined
without reference to the machine.

The execution machine is its continuation-passing form. A retained
continuation denotes the function that completes a delivered result
(`Kdenote`), and every task denotes the ordered list of results it will still
deliver (`denote`). Every machine transition satisfies the scheduler's
expansion law for this denotation (`expand_law`). So every finite expansion
tree reads out the denotation of its task (`tree_answers`), and the drained
machine delivers exactly `results`, in order (`finish_results`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

variable {Task Answer Obligation : Type}

mutual
  /-- A task denotation that satisfies the expansion law is the readout of
  every finite expansion tree. -/
  theorem TaskTree.answers_eq_of_law {expand : Task → Expansion Task Answer Obligation}
      {denote : Task → List Answer}
      (law : ∀ task, denote task = (expand task).answers ++ (expand task).tasks.flatMap denote) :
      ∀ {task : Task} (tree : TaskTree expand task), tree.answers = denote task
    | _, .branch children => by
      rw [TaskTree.answers, law, TaskForest.answers_eq_of_law law children]

  theorem TaskForest.answers_eq_of_law {expand : Task → Expansion Task Answer Obligation}
      {denote : Task → List Answer}
      (law : ∀ task, denote task = (expand task).answers ++ (expand task).tasks.flatMap denote) :
      ∀ {tasks : List Task} (forest : TaskForest expand tasks), forest.answers = tasks.flatMap denote
    | _, .nil => rfl
    | _, .cons head tail => by
      rw [TaskForest.answers, TaskTree.answers_eq_of_law law head,
        TaskForest.answers_eq_of_law law tail, List.flatMap_cons]
end

/-- Every finite run retains the unexpanded actual forest. Both successful
answers and unresolved obligations keep their original ordered suffixes. -/
theorem TaskForest.run_conservation (expand : Task → Expansion Task Answer Obligation)
    (fuel : Nat) (state : State Task Answer Obligation) (forest : TaskForest expand state.agenda) :
    ∃ remaining : TaskForest expand (run expand fuel state).agenda,
      (run expand fuel state).answers ++ remaining.answers = state.answers ++ forest.answers ∧
      (run expand fuel state).unresolved ++ remaining.obligations = state.unresolved ++ forest.obligations := by
  induction fuel generalizing state with
  | zero => exact ⟨forest, rfl, rfl⟩
  | succ fuel ih =>
    obtain ⟨remaining, answers, obligations⟩ := ih (tick expand state) (forest.advance state)
    exact ⟨remaining, answers.trans (forest.advance_answers state),
      obligations.trans (forest.advance_obligations state)⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection (FirstOrder)

/-! ## Draining a matcher -/

/-- The matcher state reached by ticking until the agenda is empty. -/
def drain (request : Request) (state : State) : State :=
  if _finished : complete state = true then state else drain request (tick request state)
termination_by agendaCost request state.agenda
decreasing_by exact tick_cost (Bool.eq_false_iff.mpr _finished)

theorem drain_of_complete {request : Request} {state : State} (finished : complete state = true) :
    drain request state = state := by
  rw [drain, dif_pos finished]

theorem drain_tick {request : Request} {state : State} (pending : complete state = false) :
    drain request (tick request state) = drain request state := by
  conv => rhs; rw [drain]
  rw [dif_neg (by simp [pending])]

theorem reachable_drain {request : Request} {state : State} (reached : Reachable request state) :
    Reachable request (drain request state) := by
  revert reached
  fun_induction drain request state with
  | case1 => exact id
  | case2 _ _ ih => exact fun reached => ih (.tick reached)

theorem drain_complete (request : Request) (state : State) :
    complete (drain request state) = true := by
  fun_induction drain request state with
  | case1 _ finished => exact finished
  | case2 _ _ ih => exact ih

theorem drain_deterministic (request : Request) {state : State} (deterministic : Deterministic state) :
    Deterministic (drain request state) := by
  revert deterministic
  fun_induction drain request state with
  | case1 => exact id
  | case2 state _ ih => exact fun deterministic => ih (tick_deterministic request deterministic)

theorem tick_answers_prefix (request : Request) (state : State) :
    state.answers <+: (tick request state).answers := by
  unfold tick
  split
  · exact List.prefix_refl _
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

theorem drain_answers_prefix (request : Request) (state : State) :
    state.answers <+: (drain request state).answers := by
  fun_induction drain request state with
  | case1 => exact List.prefix_refl _
  | case2 state _ ih => exact (tick_answers_prefix request state).trans ih

theorem drain_answer {request : Request} {state : State} {cursor : Nat} {answer : Answer}
    (found : state.answers[cursor]? = some answer) :
    (drain request state).answers[cursor]? = some answer := by
  obtain ⟨suffix, appended⟩ := drain_answers_prefix request state
  rw [← appended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1, found]

/-- The answers a consumer at `cursor` still reads, each with its certificate:
the drained answers from the cursor on. -/
def emits (request : Request) (state : State) (reached : Reachable request state) (cursor : Nat) :
    List {answer : Answer // answer.Valid request} :=
  ((drain request state).answers.drop cursor).attach.map fun item =>
    ⟨item.val, answers_sound (reachable_drain reached) (List.mem_of_mem_drop item.property)⟩

theorem emits_val (request : Request) (state : State) (reached : Reachable request state)
    (cursor : Nat) :
    (emits request state reached cursor).map Subtype.val = (drain request state).answers.drop cursor := by
  simp only [emits, List.map_map, Function.comp_def, List.attach_map_subtype_val]

theorem emits_eq_of_val {request : Request} {first second : List {answer : Answer // answer.Valid request}}
    (same : first.map Subtype.val = second.map Subtype.val) : first = second :=
  List.map_injective_iff.mpr Subtype.val_injective same

theorem emits_found {request : Request} {state : State} (reached : Reachable request state)
    {cursor : Nat} {answer : Answer} (found : state.answers[cursor]? = some answer)
    (valid : answer.Valid request) :
    emits request state reached cursor = ⟨answer, valid⟩ :: emits request state reached (cursor + 1) := by
  apply emits_eq_of_val
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp (drain_answer (request := request) found)
  rw [List.map_cons, emits_val, emits_val, List.drop_eq_getElem_cons bound, same]

/-- A drained matcher holds exactly the valid answers. -/
theorem mem_emits_start {request : Request} {answer : Answer} (valid : answer.Valid request) :
    answer ∈ (emits request (start request) .start 0).map Subtype.val := by
  rw [emits_val, List.drop_zero]
  exact (complete_answers_iff (reachable_drain .start) (drain_complete request _) answer).mpr valid

/-- A first-order schema has at most one match. -/
theorem emits_start_length_le_one {request : Request} (shape : FirstOrder request.schema) :
    (emits request (start request) .start 0).length ≤ 1 := by
  have few := (drain_deterministic request (start_deterministic shape)).1
  have lengths := congrArg List.length (emits_val request (start request) .start 0)
  simp only [List.length_map, List.drop_zero] at lengths
  omega

theorem emits_tick {request : Request} {state : State} (reached : Reachable request state)
    (pending : complete state = false) (cursor : Nat) :
    emits request (tick request state) (reachable_tick reached) cursor =
      emits request state reached cursor := by
  apply emits_eq_of_val
  rw [emits_val, emits_val, drain_tick pending]

theorem emits_finished {request : Request} {state : State} (reached : Reachable request state)
    (finished : complete state = true) {cursor : Nat} (missing : state.answers[cursor]? = none) :
    emits request state reached cursor = [] := by
  apply emits_eq_of_val
  rw [emits_val, drain_of_complete finished, List.map_nil]
  exact List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp missing)

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

/-! ## Every answer of a query state -/

/-- Every answer a query state has emitted or will still emit, in order. -/
def pending (environment : Environment) (request : Request) (state : State environment request) :
    List (Answer environment request) :=
  state.answers ++ state.agenda.flatMap (eventual environment request)

theorem pending_tick (environment : Environment) (request : Request)
    (state : State environment request) :
    pending environment request (tick environment request state) =
      pending environment request state := by
  cases state with
  | mk agenda answers unresolved work =>
    cases agenda with
    | nil => rfl
    | cons task tasks =>
      simp only [pending, tick, Scheduler.tick, List.flatMap_cons, List.flatMap_append,
        List.append_assoc]
      rw [eventual_eq environment request task, List.append_assoc]

theorem pending_found {environment : Environment} {request : Request}
    {state : State environment request} {cursor : Nat} {answer : Answer environment request}
    (found : state.answers[cursor]? = some answer) :
    (pending environment request state).drop cursor =
      answer :: (pending environment request state).drop (cursor + 1) := by
  have located : (pending environment request state)[cursor]? = some answer := by
    rw [pending, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1, found]
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp located
  rw [List.drop_eq_getElem_cons bound, same]

theorem pending_finished {environment : Environment} {request : Request}
    {state : State environment request} (idle : state.agenda = []) {cursor : Nat}
    (missing : state.answers[cursor]? = none) :
    (pending environment request state).drop cursor = [] := by
  rw [pending, idle, List.flatMap_nil, List.append_nil]
  exact List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp missing)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## Assembling results -/

/-- The assignment with which a result continues. -/
def Result.continues {environment : Environment} {goal : Goal} :
    Result environment goal → Assignment
  | .premise assignment _ _ => assignment
  | .premises assignment _ _ => assignment
  | .quantified assignment _ _ => assignment
  | .root _ _ completed _ _ _ => completed
  | .steps _ _ _ completed _ _ _ _ => completed

/-- A premise result followed by the results of the premises after it. -/
def Result.prepend {environment : Environment} {context : Context} {premise : Premise}
    {premises : List Premise} {initial : Assignment} :
    (head : Result environment (.premise context premise initial)) →
    Result environment (.premises context.next premises head.continues) →
    Result environment (.premises context (premise :: premises) initial)
  | .premise _ event head, .premises final events rest =>
      .premises final (event :: events) (.cons head rest)

@[simp] theorem Result.prepend_continues {environment : Environment} {context : Context}
    {premise : Premise} {premises : List Premise} {initial : Assignment}
    (head : Result environment (.premise context premise initial))
    (rest : Result environment (.premises context.next premises head.continues)) :
    (head.prepend rest).continues = rest.continues := by
  cases head
  cases rest
  rfl

/-- A quantified element's result followed by the results of the elements after it. -/
def Result.prependElement {environment : Environment} {context : Context} {parameter : String}
    {body : Premise} {index : Nat} {element : Pattern} {elements : List Pattern}
    {initial : Assignment}
    (localTyped : TypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) initial)) :
    (head : Result environment (.premise context.quantified body
      (bindParameter parameter (localValue context.bound element) initial))) →
    Result environment (.quantified context parameter body (index + 1) elements
      (restoreParameter parameter initial head.continues)) →
    Result environment (.quantified context parameter body index (element :: elements) initial)
  | .premise _ event head, .quantified final events rest =>
      .quantified final ((index, element, [event]) :: events) (.cons localTyped head rest)

/-- The premise result of a completed quantifier. -/
def Result.quantifier {environment : Environment} {context : Context}
    {collection parameter : String} {body : Premise} {initial : Assignment} {kind : CollType}
    {elements : List Pattern}
    (read : finiteCollection? context.bound.length initial collection = some (kind, elements)) :
    Result environment (.quantified context parameter body 0 elements initial) →
    Result environment (.premise context (.forAll collection parameter body) initial)
  | .quantified final events held =>
      .premise final (.quantified context.premiseIndex context.quantifierDepth kind events)
        (.quantified read held)

/-- The reduct of a root firing. -/
def Result.target {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} : Result environment (.root bound type source index) → Pattern
  | .root _ _ _ _ target _ => target

/-- A firing found among the declarations before the caller's. -/
def Result.searched {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index limit : Nat} (earlier : index < limit) :
    Result environment (.root bound type source index) →
    Result environment (.steps bound type source limit)
  | .root trace captured completed events target valid =>
      .steps index trace captured completed events target earlier valid

/-- The firing a root match completes once its premises hold: the converted
reduct, when it has the requested sort. -/
def rootFinish (environment : Environment) {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (sorted : OpenPatternWellSorted environment.language environment.free bound type source)
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured : Assignment}
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 []
      rule.left source trace captured)
    (capturedTyped : TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured) :
    Result environment (.premises ⟨index, rule, spec, bound, 0, 0⟩ rule.premises captured) →
    List (Result environment (.root bound type source index))
  | .premises completed events held =>
      match converted : reductWith? (ScopedReflectiveExecution.binderOperation
          environment.reflection rule) rule spec bound.length completed with
      | none => []
      | some target =>
          if checked : checkOpenPatternWellSorted environment.language environment.free
              bound type target then
            [.root trace captured completed events target
              (.fire declared specified admitted sorted matched capturedTyped held converted
                (checkOpenPatternWellSorted_sound checked))]
          else []

/-- The premise results of a child firing: the typed matches of the call's
target schema against the child's reduct. -/
def childResults (environment : Environment) (call : StepCall environment) :
    Result environment (.steps (call.binders ++ call.context.bound) call.type call.source
      call.context.ruleIndex) →
    List (Result environment (.premise call.context call.premise call.initial))
  | .steps index trace captured completed events target _ valid =>
      (GeneralScopedMatchMachine.emits
          ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
            [], call.binders.length, call.initial, call.targetSchema, target⟩
          (GeneralScopedMatchMachine.start
            ⟨call.context.rule, call.context.spec, call.context.bound.length, call.context.site 1,
              [], call.binders.length, call.initial, call.targetSchema, target⟩)
          .start 0).flatMap fun answer =>
        if typed : checkTypedAssignment environment call.context answer.val.assignment then
          [.premise answer.val.assignment
            (.child call.context.premiseIndex call.context.quantifierDepth index
              (call.binders ++ call.context.bound) call.source target trace answer.val.trace
              captured completed events)
            (call.conclude _ _ _ _ _ _ _ _ valid answer.property (checkTypedAssignment_sound typed))]
        else []

/-! ## Direct-style evaluation -/

/-- **Direct-style evaluation of a premise goal**, in delivery order. -/
def results (environment : Environment) : (goal : Goal) → List (Result environment goal)
  | .premise context (.relationQuery relation arguments) initial =>
      (Query.pending environment ⟨context, relation, arguments, initial⟩
          (Query.start environment ⟨context, relation, arguments, initial⟩)).map fun answer =>
        .premise answer.assignment
          (.query context.premiseIndex context.quantifierDepth answer.rowIndex answer.origins)
          (.query answer.valid)
  | .premise context (.freshness condition) initial =>
      match read : freshnessSubject? context.rule context.spec context.bound context.premiseIndex
          context.quantifierDepth initial condition with
      | none => []
      | some (atom, subject) =>
          if checked : Substitution.isFresh atom subject then
            [.premise initial (.freshness context.premiseIndex context.quantifierDepth atom subject)
              (.freshness read ((syntactic_freshness_iff atom subject).mp checked))]
          else []
  | .premise context (.forAll collection parameter body) initial =>
      match read : finiteCollection? context.bound.length initial collection with
      | none => []
      | some (kind, elements) =>
          (results environment (.quantified context parameter body 0 elements initial)).map
            (Result.quantifier read)
  | .premise context (.congruence source target) initial =>
      match typed : sourceType? environment.language context.rule source with
      | none => []
      | some type =>
          match interpreted : instantiateAt? context.rule context.spec context.bound.length
              (context.site 0) [] 0 initial source with
          | none => []
          | some actualSource =>
              (results environment (.steps context.bound type actualSource context.ruleIndex)).flatMap
                (childResults environment
                  { context := context
                    premise := .congruence source target
                    initial := initial
                    binders := []
                    type := type
                    source := actualSource
                    targetSchema := target
                    conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped =>
                      .step typed interpreted child matching finalTyped })
  | .premise context (.scopedStep step) initial =>
      match interpreted : instantiateAt? context.rule context.spec context.bound.length
          (context.site 0) [] step.binders.length initial step.source with
      | none => []
      | some actualSource =>
          (results environment (.steps (step.binders ++ context.bound) step.resultType actualSource
              context.ruleIndex)).flatMap
            (childResults environment
              { context := context
                premise := .scopedStep step
                initial := initial
                binders := step.binders
                type := step.resultType
                source := actualSource
                targetSchema := step.target
                conclude := fun _ _ _ _ _ _ _ _ child matching finalTyped =>
                  .scopedStep interpreted child matching finalTyped })
  | .premises _ [] initial => [.premises initial [] .nil]
  | .premises context (premise :: premises) initial =>
      (results environment (.premise context premise initial)).flatMap fun head =>
        (results environment (.premises context.next premises head.continues)).map head.prepend
  | .quantified _ _ _ _ [] initial => [.quantified initial [] .nil]
  | .quantified context parameter body index (element :: elements) initial =>
      if checked : checkTypedAssignment environment context.quantified
          (bindParameter parameter (localValue context.bound element) initial) then
        (results environment (.premise context.quantified body
            (bindParameter parameter (localValue context.bound element) initial))).flatMap fun head =>
          (results environment (.quantified context parameter body (index + 1) elements
              (restoreParameter parameter initial head.continues))).map
            (Result.prependElement (checkTypedAssignment_sound checked) head)
      else []
  | .root bound type source index =>
      match declared : environment.language.rewrites[index]? with
      | none => []
      | some rule =>
          match specified : specification? environment index with
          | none => []
          | some spec =>
              if admitted : admittedFor rule spec then
                if checked : checkOpenPatternWellSorted environment.language environment.free
                    bound type source then
                  (GeneralScopedMatchMachine.emits
                      ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩
                      (GeneralScopedMatchMachine.start
                        ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, source⟩)
                      .start 0).flatMap fun answer =>
                    if typed : checkTypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩
                        answer.val.assignment then
                      (results environment (.premises ⟨index, rule, spec, bound, 0, 0⟩ rule.premises
                          answer.val.assignment)).flatMap
                        (rootFinish environment declared specified admitted
                          (checkOpenPatternWellSorted_sound checked)
                          (trace := answer.val.trace) (captured := answer.val.assignment)
                          answer.property (checkTypedAssignment_sound typed))
                    else []
                else []
              else []
  | .steps bound type source limit =>
      (List.finRange limit).flatMap fun (child : Fin limit) =>
        (results environment (.root bound type source child.val)).map (Result.searched child.isLt)
termination_by goal => goal.rank
decreasing_by
  all_goals dsimp only [Goal.rank, premiseWorkWeight, Context.next, Context.quantified]
  all_goals simp only [Prod.lex_def]
  all_goals simp

/-! ## The meaning of retained continuations and tasks -/

/-- **The meaning of a retained continuation**: the ordered results it
completes from a delivered result. -/
def Kdenote {environment : Environment} {goal outer : Goal} :
    Continuation environment goal outer → Result environment goal →
      List (Result environment outer)
  | .done _, result => [result]
  | .nextPremise context _ premises _ tail, head =>
      (results environment (.premises context.next premises head.continues)).flatMap fun rest =>
        Kdenote tail (head.prepend rest)
  | .prepend _ _ _ _ _ event head tail, .premises final events rest =>
      Kdenote tail (.premises final (event :: events) (.cons head rest))
  | .quantifier _ _ _ _ _ _ _ read tail, result => Kdenote tail (Result.quantifier read result)
  | .element context parameter body index _ elements initial localTyped tail, head =>
      (results environment (.quantified context parameter body (index + 1) elements
          (restoreParameter parameter initial head.continues))).flatMap fun rest =>
        Kdenote tail (Result.prependElement localTyped head rest)
  | .prependElement _ _ _ index element _ _ _ event localTyped head tail,
      .quantified final events rest =>
      Kdenote tail (.quantified final ((index, element, [event]) :: events)
        (.cons localTyped head rest))
  | .rootBody _ _ _ _ _ _ declared specified admitted sorted _ _ matched capturedTyped tail,
      result =>
      (rootFinish environment declared specified admitted sorted matched capturedTyped result).flatMap
        (Kdenote tail)
  | .searchedRoot _ _ _ _ _ earlier tail, result => Kdenote tail (Result.searched earlier result)
  | .stepped call tail, result => (childResults environment call result).flatMap (Kdenote tail)

/-- The results a root match frame still delivers. -/
def rootDenote {environment : Environment} {outer : Goal}
    (frame : RootMatchFrame environment outer) : List (Result environment outer) :=
  (GeneralScopedMatchMachine.emits (rootRequest frame) frame.state frame.reachable
      frame.cursor).flatMap fun answer =>
    if typed : checkTypedAssignment environment
        ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.val.assignment then
      (results environment (.premises ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩
          frame.rule.premises answer.val.assignment)).flatMap
        (Kdenote (.rootBody frame.bound frame.type frame.source frame.index frame.rule frame.spec
          frame.declared frame.specified frame.admitted frame.sorted answer.val.trace
          answer.val.assignment answer.property (checkTypedAssignment_sound typed) frame.tail))
    else []

/-- The results a target match frame still delivers. -/
def targetDenote {environment : Environment} {outer : Goal}
    (frame : TargetMatchFrame environment outer) : List (Result environment outer) :=
  (GeneralScopedMatchMachine.emits (targetRequest frame) frame.state frame.reachable
      frame.cursor).flatMap fun answer =>
    if typed : checkTypedAssignment environment frame.call.context answer.val.assignment then
      Kdenote frame.tail (.premise answer.val.assignment
        (.child frame.call.context.premiseIndex frame.call.context.quantifierDepth frame.index
          (frame.call.binders ++ frame.call.context.bound) frame.call.source frame.target
          frame.trace answer.val.trace frame.captured frame.completed frame.history)
        (frame.call.conclude _ _ _ _ _ _ _ _ frame.valid answer.property
          (checkTypedAssignment_sound typed)))
    else []

/-- **The denotation of a task**: the ordered results it still delivers. -/
def denote {environment : Environment} {outer : Goal} :
    Task environment outer → List (Result environment outer)
  | .evaluate goal tail => (results environment goal).flatMap (Kdenote tail)
  | .deliver result tail => Kdenote tail result
  | .query request state cursor tail =>
      ((Query.pending environment request state).drop cursor).flatMap fun answer =>
        Kdenote tail (.premise answer.assignment
          (.query request.context.premiseIndex request.context.quantifierDepth answer.rowIndex
            answer.origins)
          (.query answer.valid))
  | .rootMatch frame => rootDenote frame
  | .targetMatch frame => targetDenote frame
  | .scanChildren bound type source limit cursor tail =>
      ((List.finRange limit).drop cursor).flatMap fun (child : Fin limit) =>
        (results environment (.root bound type source child.val)).flatMap
          (Kdenote (.searchedRoot bound type source child.val limit child.isLt tail))

/-! ## The expansion law -/

theorem Kdenote_prepend {environment : Environment} {outer : Goal} {context : Context}
    {premise : Premise} {premises : List Premise} {initial middle : Assignment} {event : Event}
    {head : PremiseHolds environment context premise initial middle event}
    {tail : Continuation environment (.premises context (premise :: premises) initial) outer}
    (rest : Result environment (.premises context.next premises middle)) :
    Kdenote (.prepend context premise premises initial middle event head tail) rest =
      Kdenote tail ((Result.premise middle event head).prepend rest) := by
  cases rest
  rfl

theorem Kdenote_prependElement {environment : Environment} {outer : Goal} {context : Context}
    {parameter : String} {body : Premise} {index : Nat} {element : Pattern}
    {elements : List Pattern} {initial middle : Assignment} {event : Event}
    {localTyped : TypedAssignment environment context.quantified
      (bindParameter parameter (localValue context.bound element) initial)}
    {head : PremiseHolds environment context.quantified body
      (bindParameter parameter (localValue context.bound element) initial) middle event}
    {tail : Continuation environment
      (.quantified context parameter body index (element :: elements) initial) outer}
    (rest : Result environment (.quantified context parameter body (index + 1) elements
      (restoreParameter parameter initial middle))) :
    Kdenote (.prependElement context parameter body index element elements initial middle event
        localTyped head tail) rest =
      Kdenote tail (Result.prependElement localTyped (.premise middle event head) rest) := by
  cases rest
  rfl

/-- Split the expansion-side match whose discriminant `h` has already fixed on
the result side. The other branch contradicts `h`. -/
local macro "align_with " h:ident : tactic =>
  `(tactic| (split <;> (rename_i other; cases ($h).symm.trans other)))

theorem evaluate_law (environment : Environment) (outer goal : Goal)
    (tail : Continuation environment goal outer) :
    (results environment goal).flatMap (Kdenote tail) =
      (evaluate environment outer goal tail).answers ++
        (evaluate environment outer goal tail).tasks.flatMap denote := by
  cases goal with
  | premise context premise initial =>
    cases premise with
    | relationQuery relation arguments =>
      rw [results]
      simp only [evaluate, evaluatePremise, denote, List.flatMap_map, List.drop_zero,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
    | freshness condition =>
      rw [results]
      simp only [evaluate, evaluatePremise]
      split
      next missing => align_with missing; simp
      next atom subject found =>
        split
        next fresh =>
          align_with found
          rw [dif_pos fresh]
          simp [denote]
        next stale =>
          align_with found
          rw [dif_neg stale]
          simp
    | forAll collection parameter body =>
      rw [results]
      simp only [evaluate, evaluatePremise]
      split
      next missing => align_with missing; simp
      next kind elements found =>
        align_with found
        simp only [denote, List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append]
        rfl
    | congruence source target =>
      rw [results]
      simp only [evaluate, evaluatePremise]
      split
      next missing => align_with missing; simp
      next type found =>
        split
        next missing => align_with found; align_with missing; simp
        next actualSource instantiated =>
          align_with found
          align_with instantiated
          simp only [denote, List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.nil_append]
          rfl
    | scopedStep step =>
      rw [results]
      simp only [evaluate, evaluatePremise]
      split
      next missing => align_with missing; simp
      next actualSource instantiated =>
        align_with instantiated
        simp only [denote, List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.nil_append]
        rfl
  | premises context premises initial =>
    cases premises with
    | nil =>
      rw [results]
      simp [evaluate, denote]
    | cons premise premises =>
      rw [results]
      simp only [evaluate, denote, List.flatMap_assoc, List.flatMap_map, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.nil_append]
      apply List.flatMap_congr
      intro head _
      cases head
      rfl
  | quantified context parameter body index elements initial =>
    cases elements with
    | nil =>
      rw [results]
      simp [evaluate, denote]
    | cons element elements =>
      rw [results]
      simp only [evaluate]
      split
      next =>
        simp only [denote, List.flatMap_assoc, List.flatMap_map, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.nil_append]
        apply List.flatMap_congr
        intro head _
        cases head
        rfl
      next => simp
  | root bound type source index =>
    rw [results]
    simp only [evaluate, evaluateRoot]
    split
    next missing => align_with missing; simp
    next rule declared =>
      split
      next missing => align_with declared; align_with missing; simp
      next spec specified =>
        split
        next admitted =>
          split
          next =>
            align_with declared
            align_with specified
            rw [dif_pos admitted]
            simp only [denote, rootDenote, List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.nil_append]
            apply List.flatMap_congr
            intro answer _
            split
            · simp only [List.flatMap_assoc]
              rfl
            · rfl
          next =>
            align_with declared
            align_with specified
            rw [dif_pos admitted]
            simp
        next rejected =>
          align_with declared
          align_with specified
          rw [dif_neg rejected]
          simp
  | steps bound type source limit =>
    rw [results]
    simp only [evaluate, denote, List.drop_zero, List.flatMap_assoc, List.flatMap_map,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
    rfl


/-- The readout of an expansion that schedules one task and answers nothing. -/
theorem single_task {environment : Environment} {outer : Goal}
    {expansion : Scheduler.Expansion (Task environment outer) (Result environment outer) Obligation}
    {task : Task environment outer} (scheduled : expansion.tasks = [task])
    (silent : expansion.answers = []) :
    expansion.answers ++ expansion.tasks.flatMap denote = denote task := by
  rw [silent, scheduled]
  simp

theorem deliver_law (environment : Environment) (outer : Goal) {goal : Goal}
    (result : Result environment goal) (tail : Continuation environment goal outer) :
    Kdenote tail result =
      (delivered environment outer result tail).answers ++
        (delivered environment outer result tail).tasks.flatMap denote := by
  cases tail with
  | done => simp [Kdenote, delivered]
  | nextPremise context premise premises initial tail =>
    cases result with
    | premise middle event head =>
      simp only [Kdenote, delivered, denote, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append]
      apply List.flatMap_congr
      intro rest _
      exact (Kdenote_prepend rest).symm
  | prepend context premise premises initial middle event head tail =>
    cases result with
    | premises final events rest =>
      refine Eq.trans ?_ (single_task rfl rfl).symm
      rfl
  | quantifier context collection parameter body initial kind elements read tail =>
    cases result with
    | quantified final events held => simp [Kdenote, delivered, denote, Result.quantifier]
  | element context parameter body index element elements initial localTyped tail =>
    cases result with
    | premise middle event head =>
      refine Eq.trans ?_ (single_task rfl rfl).symm
      simp only [Kdenote, denote]
      apply List.flatMap_congr
      intro rest _
      exact (Kdenote_prependElement rest).symm
  | prependElement context parameter body index element elements initial middle event localTyped
      head tail =>
    cases result with
    | quantified final events rest =>
      refine Eq.trans ?_ (single_task rfl rfl).symm
      rfl
  | rootBody bound type source index rule spec declared specified admitted sorted trace captured
      matched capturedTyped tail =>
    cases result with
    | premises completed events held =>
      simp only [Kdenote, rootFinish, delivered]
      split
      next missing => align_with missing; simp
      next target converted =>
        split
        next checked =>
          align_with converted
          rw [dif_pos checked]
          simp [denote]
        next unchecked =>
          align_with converted
          rw [dif_neg unchecked]
          simp
  | searchedRoot bound type source index limit earlier tail =>
    cases result with
    | root trace captured completed events target held =>
      simp [Kdenote, delivered, denote, Result.searched]
  | stepped call tail =>
    cases result with
    | steps index trace captured completed events target earlier held =>
      simp only [Kdenote, childResults, delivered, denote, targetDenote, targetRequest,
        List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      apply List.flatMap_congr
      intro answer _
      split <;> simp

theorem query_law (environment : Environment) (outer : Goal) (request : Query.Request)
    (state : Query.State environment request) (cursor : Nat)
    (tail : Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments)
        request.initial) outer) :
    denote (.query request state cursor tail) =
      (expandQuery environment outer request state cursor tail).answers ++
        (expandQuery environment outer request state cursor tail).tasks.flatMap denote := by
  simp only [denote, expandQuery]
  split
  next answer found =>
    rw [Query.pending_found found]
    simp [denote]
  next missing =>
    split
    next idle =>
      rw [Query.pending_finished (List.isEmpty_iff.mp idle) missing]
      simp
    next =>
      simp only [denote, Query.pending_tick, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append]

theorem rootMatch_law (environment : Environment) (outer : Goal)
    (frame : RootMatchFrame environment outer) :
    rootDenote frame =
      (expandRootMatch environment outer frame).answers ++
        (expandRootMatch environment outer frame).tasks.flatMap denote := by
  unfold expandRootMatch
  split
  next answer found =>
    have valid := GeneralScopedMatchMachine.answers_sound frame.reachable
      (List.mem_of_getElem? found)
    rw [rootDenote, GeneralScopedMatchMachine.emits_found (request := rootRequest frame)
      frame.reachable found valid, List.flatMap_cons]
    dsimp only
    split
    next =>
      simp only [denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      rfl
    next =>
      simp only [denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      rfl
  next missing =>
    split
    next finished =>
      rw [rootDenote, GeneralScopedMatchMachine.emits_finished (request := rootRequest frame)
        frame.reachable finished missing]
      simp
    next pending =>
      simp only [denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      dsimp only [rootDenote, rootRequest]
      rw [GeneralScopedMatchMachine.emits_tick frame.reachable (Bool.eq_false_iff.mpr pending)]

theorem targetMatch_law (environment : Environment) (outer : Goal)
    (frame : TargetMatchFrame environment outer) :
    targetDenote frame =
      (expandTargetMatch environment outer frame).answers ++
        (expandTargetMatch environment outer frame).tasks.flatMap denote := by
  unfold expandTargetMatch
  split
  next answer found =>
    have valid := GeneralScopedMatchMachine.answers_sound frame.reachable
      (List.mem_of_getElem? found)
    rw [targetDenote, GeneralScopedMatchMachine.emits_found (request := targetRequest frame)
      frame.reachable found valid, List.flatMap_cons]
    dsimp only
    split
    next =>
      simp only [denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      rfl
    next =>
      simp only [denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      rfl
  next missing =>
    split
    next finished =>
      rw [targetDenote, GeneralScopedMatchMachine.emits_finished (request := targetRequest frame)
        frame.reachable finished missing]
      simp
    next pending =>
      simp only [denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
      dsimp only [targetDenote, targetRequest]
      rw [GeneralScopedMatchMachine.emits_tick frame.reachable (Bool.eq_false_iff.mpr pending)]

theorem finRange_drop {limit cursor : Nat} (earlier : cursor < limit) :
    (List.finRange limit).drop cursor =
      ⟨cursor, earlier⟩ :: (List.finRange limit).drop (cursor + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using earlier)]
  simp

theorem scan_law (environment : Environment) (outer : Goal) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (limit cursor : Nat)
    (tail : Continuation environment (.steps bound type source limit) outer) :
    denote (.scanChildren bound type source limit cursor tail) =
      (expand environment outer (.scanChildren bound type source limit cursor tail)).answers ++
        (expand environment outer (.scanChildren bound type source limit cursor tail)).tasks.flatMap
          denote := by
  simp only [denote, expand]
  split
  next earlier =>
    rw [finRange_drop earlier]
    simp [denote]
  next later =>
    rw [List.drop_eq_nil_of_le (by simp only [List.length_finRange]; omega)]
    simp

/-- **The expansion law.** Every machine transition delivers the denotation of
its task: its own answers, then the denotations of its children, in order. -/
theorem expand_law (environment : Environment) (outer : Goal) (task : Task environment outer) :
    denote task = (expand environment outer task).answers ++
      (expand environment outer task).tasks.flatMap denote := by
  cases task with
  | evaluate goal tail => exact evaluate_law environment outer goal tail
  | deliver result tail => exact deliver_law environment outer result tail
  | query request state cursor tail => exact query_law environment outer request state cursor tail
  | rootMatch frame => exact rootMatch_law environment outer frame
  | targetMatch frame => exact targetMatch_law environment outer frame
  | scanChildren bound type source limit cursor tail =>
    exact scan_law environment outer bound type source limit cursor tail

/-- Every finite expansion tree reads out the denotation of its task. -/
theorem tree_answers {environment : Environment} {outer : Goal} {task : Task environment outer}
    (tree : Tree environment outer task) : tree.answers = denote task :=
  Scheduler.TaskTree.answers_eq_of_law (expand_law environment outer) tree

theorem treeStart_answers (environment : Environment) (goal : Goal) :
    (treeStart environment goal).answers = results environment goal := by
  rw [tree_answers]
  simp [denote, Kdenote]

/-- **The drained machine delivers exactly the direct-style results, in order.** -/
theorem finish_results (environment : Environment) (goal : Goal) :
    (finish environment goal).answers = results environment goal :=
  (finish_answers environment goal).trans (treeStart_answers environment goal)

/-- The independent denotation of the actual retained agenda. This does not
supply an answer frontier to the evaluator. -/
def remaining {environment : Environment} {goal : Goal} (state : State environment goal) :
    List (Result environment goal) := state.agenda.flatMap denote

/-- A microstep preserves emitted answers followed by the retained agenda's
ordered denotation. Unresolved obligations remain in the actual state. -/
theorem tick_retained (environment : Environment) (goal : Goal) (state : State environment goal) :
    (tick environment goal state).answers ++ remaining (tick environment goal state) =
      state.answers ++ remaining state := by
  cases state with
  | mk agenda answers unresolved work =>
    cases agenda with
    | nil => rfl
    | cons task tasks =>
      simp only [tick, Scheduler.tick, remaining, List.flatMap_append, List.flatMap_cons,
        List.append_assoc]
      rw [expand_law environment goal task, List.append_assoc]

/-- Added budget transforms the retained frames, preserving the complete
ordered result list at every intermediate state. -/
theorem run_retained (environment : Environment) (goal : Goal) (fuel : Nat)
    (state : State environment goal) :
    (run environment goal fuel state).answers ++ remaining (run environment goal fuel state) =
      state.answers ++ remaining state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    exact (ih (tick environment goal state)).trans (tick_retained environment goal state)

/-- The actual finite-prefix state and its retained agenda account for every
original source result in order, equal occurrences included. -/
theorem run_start_retained (environment : Environment) (goal : Goal) (fuel : Nat) :
    (run environment goal fuel (start environment goal)).answers ++
        remaining (run environment goal fuel (start environment goal)) = results environment goal := by
  have kept := run_retained environment goal fuel (start environment goal)
  simpa only [start, remaining, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.nil_append, denote, Kdenote, List.flatMap_singleton'] using kept

/-- The same retained-state law conserves the complete unresolved-obligation
history, independently of any successful-answer observer. -/
theorem run_start_tree_conservation (environment : Environment) (goal : Goal) (fuel : Nat) :
    ∃ forest : Scheduler.TaskForest (expand environment goal)
        (run environment goal fuel (start environment goal)).agenda,
      (run environment goal fuel (start environment goal)).answers ++ forest.answers = results environment goal ∧
      (run environment goal fuel (start environment goal)).unresolved ++ forest.obligations =
        (treeStart environment goal).obligations := by
  obtain ⟨forest, answers, obligations⟩ := Scheduler.TaskForest.run_conservation
    (expand environment goal) fuel (start environment goal) (.cons (treeStart environment goal) .nil)
  refine ⟨forest, ?_, ?_⟩
  · simpa only [run, start, Scheduler.TaskForest.answers, List.append_nil, List.nil_append,
      treeStart_answers] using answers
  · simpa only [run, start, Scheduler.TaskForest.obligations, List.append_nil, List.nil_append] using obligations

theorem run_unresolved_prefix_finish (environment : Environment) (goal : Goal) (fuel : Nat) :
    (run environment goal fuel (start environment goal)).unresolved <+:
      (finish environment goal).unresolved := by
  obtain ⟨forest, _, obligations⟩ := run_start_tree_conservation environment goal fuel
  exact ⟨forest.obligations, obligations.trans (finish_obligations environment goal).symm⟩

theorem run_resolved_of_finish_resolved (environment : Environment) (goal : Goal) (fuel : Nat)
    (resolved : (finish environment goal).unresolved = []) :
    (run environment goal fuel (start environment goal)).unresolved = [] := by
  obtain ⟨future, kept⟩ := run_unresolved_prefix_finish environment goal fuel
  rw [resolved] at kept
  exact (List.append_eq_nil_iff.mp kept).1

/-- Only delivery to the outer goal's terminal continuation commits a result.
Matching, querying and delivery through an inner continuation remain work. -/
def Task.commits {environment : Environment} {outer : Goal} : Task environment outer → Bool
  | .deliver _ (.done _) => true
  | _ => false

@[simp] theorem Task.commits_deliver_done {environment : Environment} {goal : Goal}
    (result : Result environment goal) :
    (Task.deliver result (.done goal)).commits = true := rfl

theorem Task.commits_iff {environment : Environment} {outer : Goal}
    (task : Task environment outer) :
    task.commits = true ↔
      ∃ result : Result environment outer, task = .deliver result (.done outer) := by
  constructor
  · intro committing
    cases task with
    | deliver result tail =>
        cases tail <;> simp [Task.commits] at committing
        exact ⟨result, rfl⟩
    | _ => cases committing
  · rintro ⟨result, rfl⟩
    rfl

private theorem evaluatePremise_answers (environment : Environment) (outer : Goal)
    (context : Context) (premise : Premise) (initial : Assignment)
    (tail : Continuation environment (.premise context premise initial) outer) :
    (evaluatePremise environment outer context premise initial tail).answers = [] := by
  cases premise <;> simp only [evaluatePremise]
  all_goals repeat first | rfl | split

private theorem evaluateRoot_answers (environment : Environment) (outer : Goal)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Continuation environment (.root bound type source index) outer) :
    (evaluateRoot environment outer bound type source index tail).answers = [] := by
  simp only [evaluateRoot]
  repeat first | rfl | split

private theorem evaluate_answers (environment : Environment) (outer goal : Goal)
    (tail : Continuation environment goal outer) :
    (evaluate environment outer goal tail).answers = [] := by
  cases goal with
  | premise context premise initial => exact evaluatePremise_answers _ _ _ _ _ _
  | premises context premises initial => cases premises <;> rfl
  | quantified context parameter body index elements initial =>
      cases elements <;> simp only [evaluate]
      all_goals repeat first | rfl | split
  | root bound type source index => exact evaluateRoot_answers _ _ _ _ _ _ _
  | steps => rfl

/-- Every noncommitting task emits no result. Its unresolved obligations and
remaining tasks are left in the actual expansion; silence does not erase them. -/
theorem expand_answers_eq_nil_of_not_committing (environment : Environment) (outer : Goal)
    (task : Task environment outer) (noncommitting : task.commits = false) :
    (expand environment outer task).answers = [] := by
  cases task with
  | evaluate goal tail => exact evaluate_answers _ _ _ _
  | deliver result tail =>
      cases tail <;> cases result <;> simp [Task.commits] at noncommitting
      all_goals simp only [expand, delivered]
      all_goals repeat first | contradiction | rfl | split
  | query request state cursor tail =>
      simp only [expand, expandQuery]
      repeat first | rfl | split
  | rootMatch frame =>
      simp only [expand, expandRootMatch]
      repeat first | rfl | split
  | targetMatch frame =>
      simp only [expand, expandTargetMatch]
      repeat first | rfl | split
  | scanChildren =>
      simp only [expand]
      split <;> rfl

/-- A committing expansion emits exactly its terminal result, once. -/
theorem expand_answers_of_committing (environment : Environment) (outer : Goal)
    (task : Task environment outer) (committing : task.commits = true) :
    ∃ result : Result environment outer,
      task = .deliver result (.done outer) ∧
        expand environment outer task = { answers := [result] } := by
  obtain ⟨result, rfl⟩ := (task.commits_iff).mp committing
  exact ⟨result, rfl, rfl⟩

/-- An idle tick or a tick whose actual head is noncommitting preserves the
whole result history. It may still retain or add unresolved obligations. -/
theorem tick_answers_of_noncommitting (environment : Environment) (goal : Goal)
    (state : State environment goal)
    (noncommitting : ∀ task ∈ state.agenda.head?, task.commits = false) :
    (tick environment goal state).answers = state.answers := by
  cases agenda : state.agenda with
  | nil => simp [tick, Scheduler.tick, agenda]
  | cons task rest =>
      have silent := expand_answers_eq_nil_of_not_committing environment goal task
        (noncommitting task (by simp [agenda]))
      simp [tick, Scheduler.tick, agenda, silent]

/-- The terminal delivery tick appends its one result and consumes that task,
without changing the unresolved-obligation history. -/
theorem tick_terminal_delivery (environment : Environment) (goal : Goal)
    (state : State environment goal) (result : Result environment goal)
    (rest : List (Task environment goal))
    (agenda : state.agenda = .deliver result (.done goal) :: rest) :
    (tick environment goal state).answers = state.answers ++ [result] ∧
      (tick environment goal state).agenda = rest ∧
      (tick environment goal state).unresolved = state.unresolved := by
  simp [tick, Scheduler.tick, agenda, expand, delivered]

/-- A missing declaration is a noncommitting task with an explicit unresolved
obligation, not an erased failed candidate. -/
theorem unavailable_rule_noncommitting (environment : Environment)
    (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (unavailable : environment.language.rewrites[index]? = none) :
    let goal := Goal.root bound type source index
    let task : Task environment goal := .evaluate goal (.done goal)
    task.commits = false ∧ (expand environment goal task).answers = [] ∧
      (expand environment goal task).unresolved = [.ruleUnavailable index] := by
  dsimp only
  refine ⟨rfl, evaluateRoot_answers _ _ _ _ _ _ _, ?_⟩
  simp only [expand, evaluate, evaluateRoot]
  split
  · rfl
  · rename_i rule declared
    rw [unavailable] at declared
    cases declared

#print axioms Task.commits_iff
#print axioms expand_answers_eq_nil_of_not_committing
#print axioms expand_answers_of_committing
#print axioms tick_answers_of_noncommitting
#print axioms tick_terminal_delivery
#print axioms unavailable_rule_noncommitting

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
