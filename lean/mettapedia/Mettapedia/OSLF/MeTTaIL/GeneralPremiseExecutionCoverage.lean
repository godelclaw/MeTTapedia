import Mettapedia.OSLF.MeTTaIL.GeneralPremiseContinuationSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionTermination
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCursor

/-!
# Semantic coverage of actual suspended premise execution

The denotation of a suspended task retains unread alternatives and the
independent meaning of its continuation. Every actual transition preserves
each denoted answer. Finite drainage therefore yields semantic completeness
for declaration-stratified premise derivations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def TaskAccepts {environment : Environment} {outer : Goal}
    (task : Task environment outer) (wanted : Result environment outer) : Prop :=
  match task with
  | .evaluate _ tail => EvaluatesTo tail wanted
  | .deliver result tail => Concludes tail result wanted
  | .query request state cursor tail =>
      Query.StateWellFormed environment request state ∧ cursor ≤ state.answers.length ∧
      ∃ answer : Query.Answer environment request,
        Query.UnreadAccepts environment request state cursor answer ∧
        Concludes tail (.premise answer.assignment
          (.query request.context.premiseIndex request.context.quantifierDepth
            answer.rowIndex answer.origins) (.query answer.valid)) wanted
  | .rootMatch frame =>
      frame.cursor ≤ frame.state.answers.length ∧
      ∃ answer : GeneralScopedMatchMachine.Answer,
        GeneralScopedMatchMachine.MatcherUnread (rootRequest frame)
          frame.state frame.cursor answer ∧
        ∃ (matched : answer.Valid (rootRequest frame))
            (typed : TypedAssignment environment
              ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ answer.assignment),
          EvaluatesTo (.rootBody frame.bound frame.type frame.source frame.index frame.rule frame.spec
            frame.declared frame.specified frame.admitted frame.sorted answer.trace answer.assignment
            matched typed frame.tail) wanted
  | .targetMatch frame =>
      frame.cursor ≤ frame.state.answers.length ∧
      ∃ answer : GeneralScopedMatchMachine.Answer,
        GeneralScopedMatchMachine.MatcherUnread (targetRequest frame)
          frame.state frame.cursor answer ∧
        ∃ (matched : answer.Valid (targetRequest frame))
            (typed : TypedAssignment environment frame.call.context answer.assignment),
          Concludes frame.tail (.premise answer.assignment
            (.child frame.call.context.premiseIndex frame.call.context.quantifierDepth frame.index
              (frame.call.binders ++ frame.call.context.bound) frame.call.source frame.target
              frame.trace answer.trace frame.captured frame.completed frame.history)
            (frame.call.conclude _ _ _ _ _ _ _ _ frame.valid matched typed)) wanted
  | .scanChildren bound type source limit cursor tail =>
      ∃ (index : Nat) (earlier : index < limit), cursor ≤ index ∧
        EvaluatesTo (.searchedRoot bound type source index limit earlier tail) wanted

def StateAccepts {environment : Environment} {goal : Goal}
    (state : State environment goal) (wanted : Result environment goal) : Prop :=
  wanted ∈ state.answers ∨ ∃ task ∈ state.agenda, TaskAccepts task wanted

def ExpansionAccepts {environment : Environment} {goal : Goal}
    (expansion : Scheduler.Expansion (Task environment goal) (Result environment goal) Obligation)
    (wanted : Result environment goal) : Prop :=
  wanted ∈ expansion.answers ∨ ∃ task ∈ expansion.tasks, TaskAccepts task wanted

theorem delivered_covers {environment : Environment} {goal outer : Goal}
    {result : Result environment goal} {tail : Continuation environment goal outer}
    {wanted : Result environment outer} (meaning : Concludes tail result wanted) :
    ExpansionAccepts (delivered environment outer result tail) wanted := by
  cases tail with
  | done =>
      simpa [ExpansionAccepts, delivered, Concludes] using meaning.symm
  | nextPremise context premise premises initial tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, ordered, concludes⟩ := meaning
          simp only [ExpansionAccepts, delivered, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨.premises final events rest, ordered, concludes⟩
  | prepend context premise premises initial middle event head tail =>
      cases result with
      | premises final events rest =>
          change ExpansionAccepts
            {tasks := [.deliver (.premises final (event :: events) (.cons head rest)) tail]} wanted
          simp only [ExpansionAccepts, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          change Concludes tail (.premises final (event :: events) (.cons head rest)) wanted at meaning
          exact meaning
  | quantifier context collection parameter body initial kind elements read tail =>
      cases result
      simpa only [ExpansionAccepts, delivered.eq_4, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, TaskAccepts, Concludes.eq_4] using meaning
  | element context parameter body index element elements initial localTyped tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, ordered, concludes⟩ := meaning
          change ExpansionAccepts
            { tasks := [.evaluate
                (.quantified context parameter body (index + 1) elements
                  (restoreParameter parameter initial middle))
                (.prependElement context parameter body index element elements initial middle
                  event localTyped head tail)] } wanted
          simp only [ExpansionAccepts, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨.quantified final events rest, ordered, concludes⟩
  | prependElement context parameter body index element elements initial middle event localTyped head tail =>
      cases result with
      | quantified final events rest =>
          change ExpansionAccepts
            {tasks := [.deliver (.quantified final ((index, element, [event]) :: events)
              (.cons localTyped head rest)) tail]} wanted
          simp only [ExpansionAccepts, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          change Concludes tail (.quantified final ((index, element, [event]) :: events)
            (.cons localTyped head rest)) wanted at meaning
          exact meaning
  | rootBody bound type source index rule spec declared specified admitted sorted trace captured
      matched capturedTyped tail =>
      cases result with
      | premises completed events held =>
          obtain ⟨target, converted, typed, concludes⟩ := meaning
          have checked := checkOpenPatternWellSorted_complete typed
          rw [delivered.eq_7]
          split
          · rename_i unavailable
            simp [converted] at unavailable
          · rename_i actual actualRead
            have same : actual = target := Option.some.inj (actualRead.symm.trans converted)
            subst actual
            simpa [ExpansionAccepts, checked, TaskAccepts] using concludes
  | searchedRoot bound type source index limit earlier tail =>
      cases result
      simpa only [ExpansionAccepts, delivered.eq_8, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, TaskAccepts, Concludes.eq_8] using meaning
  | stepped call tail =>
      cases result with
      | steps index trace captured completed events target earlier valid =>
          obtain ⟨final, targetTrace, matched, typed, concludes⟩ := meaning
          simp only [ExpansionAccepts, delivered, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨Nat.zero_le _, ⟨final, targetTrace⟩,
            (GeneralScopedMatchMachine.start_unread_iff _ _).mpr matched,
            matched, typed, concludes⟩

theorem evaluate_covers {environment : Environment} {goal outer : Goal}
    {tail : Continuation environment goal outer} {wanted : Result environment outer}
    (meaning : EvaluatesTo tail wanted) :
    ExpansionAccepts (evaluate environment outer goal tail) wanted := by
  obtain ⟨result, ordered, concludes⟩ := meaning
  cases goal with
  | premises context premises initial =>
      cases result with
      | premises final events held =>
          cases held with
          | nil =>
              simpa only [ExpansionAccepts, evaluate.eq_2, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts] using concludes
          | @cons context premise premises initial middle final event events head rest =>
              have parts : eventOrdered context.ruleIndex event = true ∧
                  eventsOrdered context.ruleIndex events = true := by
                simpa [Result.ordered, eventsOrdered] using ordered
              simp only [ExpansionAccepts, evaluate.eq_3, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨.premise middle event head, parts.1,
                final, events, rest, parts.2, concludes⟩
  | quantified context parameter body index elements initial =>
      cases result with
      | quantified final events held =>
          cases held with
          | nil => simpa only [ExpansionAccepts, evaluate.eq_4, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts] using concludes
          | @cons context parameter body index element elements initial middle final event events localTyped head rest =>
              have checked := checkTypedAssignment_complete localTyped
              have parts : eventOrdered context.ruleIndex event = true ∧
                  quantifiedOrdered context.ruleIndex events = true := by
                simpa [Result.ordered, quantifiedOrdered, eventsOrdered] using ordered
              simp only [ExpansionAccepts, evaluate.eq_5, checked, dite_true, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨.premise middle event head, parts.1,
                final, events, rest, parts.2, concludes⟩
  | premise context premise initial =>
      cases result with
      | premise final event held =>
          cases held with
          | @query context relation arguments initial final rowIndex origins query =>
              simp only [ExpansionAccepts, evaluate.eq_1, evaluatePremise.eq_1, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨Query.start_wellFormed _ _, by simp [Query.start],
                ⟨rowIndex, final, origins, query⟩, Query.unread_start_of_valid _ _ _, concludes⟩
          | @freshness context condition initial atom subject read fresh =>
              have checked := (syntactic_freshness_iff atom subject).mpr fresh
              rw [evaluate.eq_1]
              rw [evaluatePremise.eq_2]
              split
              · rename_i unavailable
                simp [read] at unavailable
              · rename_i actualAtom actualSubject actualRead
                have same := Option.some.inj (actualRead.symm.trans read)
                cases same
                simpa [ExpansionAccepts, checked, TaskAccepts] using concludes
          | @step context source target actualSource actualTarget type initial final captured completed
              childIndex trace targetTrace history typed interpreted child matched finalTyped =>
              have parts : childIndex < context.ruleIndex ∧
                  eventsOrdered childIndex history = true := by
                simpa [Result.ordered, eventOrdered] using ordered
              rw [evaluate.eq_1]
              rw [evaluatePremise.eq_4]
              split
              · rename_i unavailable
                simp [typed] at unavailable
              · rename_i actualType actualTyped
                have same : actualType = type := Option.some.inj (actualTyped.symm.trans typed)
                subst actualType
                split
                · rename_i unavailable
                  simp [interpreted] at unavailable
                · rename_i actual actualRead
                  have same : actual = actualSource := Option.some.inj (actualRead.symm.trans interpreted)
                  subst actual
                  simp only [ExpansionAccepts, List.not_mem_nil, false_or,
                    List.mem_singleton, exists_eq_left, TaskAccepts]
                  exact ⟨.steps childIndex trace captured completed history actualTarget parts.1 child,
                    parts.2, final, targetTrace, matched, finalTyped, concludes⟩
          | @scopedStep context step actualSource actualTarget initial final captured completed childIndex
              trace targetTrace history interpreted child matched finalTyped =>
              have parts : childIndex < context.ruleIndex ∧
                  eventsOrdered childIndex history = true := by
                simpa [Result.ordered, eventOrdered] using ordered
              rw [evaluate.eq_1]
              rw [evaluatePremise.eq_5]
              split
              · rename_i unavailable
                simp [interpreted] at unavailable
              · rename_i actual actualRead
                have same : actual = actualSource := Option.some.inj (actualRead.symm.trans interpreted)
                subst actual
                simp only [ExpansionAccepts, List.not_mem_nil, false_or,
                  List.mem_singleton, exists_eq_left, TaskAccepts]
                exact ⟨.steps childIndex trace captured completed history actualTarget parts.1 child,
                  parts.2, final, targetTrace, matched, finalTyped, concludes⟩
          | @quantified context collection parameter body initial final kind elements history read quantified =>
              rw [evaluate.eq_1]
              rw [evaluatePremise.eq_3]
              split
              · rename_i unavailable
                simp [read] at unavailable
              · rename_i actualKind actualElements actualRead
                have same := Option.some.inj (actualRead.symm.trans read)
                cases same
                simp only [ExpansionAccepts, List.not_mem_nil, false_or,
                  List.mem_singleton, exists_eq_left, TaskAccepts]
                exact ⟨.quantified final history quantified,
                  by simpa [Result.ordered, eventOrdered] using ordered, concludes⟩
  | root bound type source index =>
      cases result with
      | root trace captured completed history target held =>
          cases held with
          | @fire bound type source target index rule spec captured completed trace history
              declared specified admitted sorted matched capturedTyped premises converted targetTyped =>
              have checked := checkOpenPatternWellSorted_complete sorted
              rw [evaluate.eq_6, evaluateRoot.eq_1]
              split
              · rename_i unavailable
                simp [declared] at unavailable
              · rename_i actualRule actualDeclared
                have same : actualRule = rule := Option.some.inj (actualDeclared.symm.trans declared)
                subst actualRule
                split
                · rename_i unavailable
                  simp [specified] at unavailable
                · rename_i actualSpec actualSpecified
                  have same : actualSpec = spec := Option.some.inj (actualSpecified.symm.trans specified)
                  subst actualSpec
                  simp only [admitted, checked, dite_true, ExpansionAccepts, List.not_mem_nil,
                    false_or, List.mem_singleton, exists_eq_left, TaskAccepts]
                  refine ⟨Nat.zero_le _, ⟨captured, trace⟩,
                    (GeneralScopedMatchMachine.start_unread_iff _ _).mpr matched,
                    matched, capturedTyped, ?_⟩
                  exact ⟨.premises completed history premises, ordered,
                    target, converted, targetTyped, concludes⟩
  | steps bound type source limit =>
      cases result with
      | steps index trace captured completed history target earlier held =>
          simp only [ExpansionAccepts, evaluate.eq_7, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          refine ⟨index, earlier, Nat.zero_le _, ?_⟩
          exact ⟨.root trace captured completed history target held, ordered, concludes⟩


private theorem matcher_answers_grow (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) :
    state.answers.length ≤ (GeneralScopedMatchMachine.tick request state).answers.length := by
  cases state with
  | mk agenda answers =>
      cases agenda with
      | nil => simp [GeneralScopedMatchMachine.tick]
      | cons work agenda =>
          cases work with
          | mk assignment tasks trace =>
              cases tasks <;> simp [GeneralScopedMatchMachine.tick]

private theorem matcher_unread_settled {request : GeneralScopedMatchMachine.Request}
    {state : GeneralScopedMatchMachine.State} {cursor : Nat}
    {answer : GeneralScopedMatchMachine.Answer}
    (settled : state.agenda = []) (unavailable : state.answers[cursor]? = none) :
    ¬ GeneralScopedMatchMachine.MatcherUnread request state cursor answer := by
  have consumed : state.answers.drop cursor = [] :=
    List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp unavailable)
  simp [GeneralScopedMatchMachine.MatcherUnread, consumed, settled]

private theorem query_answers_grow (environment : Environment) (request : Query.Request)
    (state : Query.State environment request) :
    state.answers.length ≤ (Query.tick environment request state).answers.length := by
  obtain ⟨suffix, same⟩ := Scheduler.tick_answers_prefix (Query.expand environment request) state
  change state.answers.length ≤
    (Scheduler.tick (Query.expand environment request) state).answers.length
  rw [same]
  simp

theorem query_covers {environment : Environment} {outer : Goal}
    {request : Query.Request} {state : Query.State environment request} {cursor : Nat}
    {tail : Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer}
    {wanted : Result environment outer}
    (meaning : TaskAccepts (.query request state cursor tail) wanted) :
    ExpansionAccepts (expandQuery environment outer request state cursor tail) wanted := by
  obtain ⟨wellFormed, bounded, answer, unread, concludes⟩ := meaning
  unfold expandQuery
  split
  · rename_i seen found
    obtain same | remaining := (Query.unread_get environment request state cursor answer).mp unread
    · have equal : seen = answer := Option.some.inj (found.symm.trans same)
      subst seen
      right
      exact ⟨_, List.mem_cons_self, concludes⟩
    · have newBound : cursor + 1 ≤ state.answers.length := by
        obtain ⟨before, _⟩ := List.getElem?_eq_some_iff.mp found
        omega
      right
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
        wellFormed, newBound, answer, remaining, concludes⟩
  · rename_i unavailable
    split
    · rename_i settled
      have empty : state.agenda = [] := List.isEmpty_iff.mp settled
      exact False.elim (Query.unread_empty_of_settled environment request state cursor answer
        empty unavailable unread)
    · right
      refine ⟨_, List.mem_cons_self, Query.tick_wellFormed _ _ wellFormed, ?_, answer, ?_, concludes⟩
      · exact bounded.trans (query_answers_grow environment request state)
      · exact (Query.unread_tick_of_no_answer environment request state cursor answer
          wellFormed bounded unavailable).mpr unread

theorem rootMatch_covers {environment : Environment} {outer : Goal}
    {frame : RootMatchFrame environment outer} {wanted : Result environment outer}
    (meaning : TaskAccepts (.rootMatch frame) wanted) :
    ExpansionAccepts (expandRootMatch environment outer frame) wanted := by
  obtain ⟨bounded, answer, unread, matched, typed, continued⟩ := meaning
  unfold expandRootMatch
  split
  · rename_i seen found
    obtain same | remaining :=
      (GeneralScopedMatchMachine.unread_cursor_split (rootRequest frame) frame.state frame.cursor answer).mp unread
    · have equal : seen = answer := Option.some.inj (found.symm.trans same)
      subst seen
      have checked := checkTypedAssignment_complete typed
      simp only [checked, dite_true]
      right
      exact ⟨_, List.mem_cons_self, continued⟩
    · have newBound : frame.cursor + 1 ≤ frame.state.answers.length := by
        obtain ⟨before, _⟩ := List.getElem?_eq_some_iff.mp found
        omega
      dsimp only
      split
      · right
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          newBound, answer, remaining, matched, typed, continued⟩
      · right
        exact ⟨_, List.mem_cons_self, newBound, answer, remaining, matched, typed, continued⟩
  · rename_i unavailable
    split
    · rename_i completed
      have empty := (GeneralScopedMatchMachine.complete_eq_true_iff _).mp completed
      exact False.elim (matcher_unread_settled empty unavailable unread)
    · right
      refine ⟨_, List.mem_cons_self, ?_, answer, ?_, matched, typed, continued⟩
      · exact bounded.trans (matcher_answers_grow (rootRequest frame) frame.state)
      · exact (GeneralScopedMatchMachine.unread_tick_of_no_answer (rootRequest frame)
          frame.state frame.cursor answer bounded unavailable).mpr unread

theorem targetMatch_covers {environment : Environment} {outer : Goal}
    {frame : TargetMatchFrame environment outer} {wanted : Result environment outer}
    (meaning : TaskAccepts (.targetMatch frame) wanted) :
    ExpansionAccepts (expandTargetMatch environment outer frame) wanted := by
  obtain ⟨bounded, answer, unread, matched, typed, continued⟩ := meaning
  unfold expandTargetMatch
  split
  · rename_i seen found
    obtain same | remaining :=
      (GeneralScopedMatchMachine.unread_cursor_split (targetRequest frame) frame.state frame.cursor answer).mp unread
    · have equal : seen = answer := Option.some.inj (found.symm.trans same)
      subst seen
      have checked := checkTypedAssignment_complete typed
      simp only [checked, dite_true]
      right
      exact ⟨_, List.mem_cons_self, continued⟩
    · have newBound : frame.cursor + 1 ≤ frame.state.answers.length := by
        obtain ⟨before, _⟩ := List.getElem?_eq_some_iff.mp found
        omega
      dsimp only
      split
      · right
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          newBound, answer, remaining, matched, typed, continued⟩
      · right
        exact ⟨_, List.mem_cons_self, newBound, answer, remaining, matched, typed, continued⟩
  · rename_i unavailable
    split
    · rename_i completed
      have empty := (GeneralScopedMatchMachine.complete_eq_true_iff _).mp completed
      exact False.elim (matcher_unread_settled empty unavailable unread)
    · right
      refine ⟨_, List.mem_cons_self, ?_, answer, ?_, matched, typed, continued⟩
      · exact bounded.trans (matcher_answers_grow (targetRequest frame) frame.state)
      · exact (GeneralScopedMatchMachine.unread_tick_of_no_answer (targetRequest frame)
          frame.state frame.cursor answer bounded unavailable).mpr unread

theorem expand_covers {environment : Environment} {goal : Goal}
    {task : Task environment goal} {wanted : Result environment goal}
    (meaning : TaskAccepts task wanted) :
    ExpansionAccepts (expand environment goal task) wanted := by
  cases task with
  | evaluate current tail => exact evaluate_covers meaning
  | deliver result tail => exact delivered_covers meaning
  | query request state cursor tail => exact query_covers meaning
  | rootMatch frame => exact rootMatch_covers meaning
  | targetMatch frame => exact targetMatch_covers meaning
  | scanChildren bound type source limit cursor tail =>
      obtain ⟨index, earlier, following, continued⟩ := meaning
      have before : cursor < limit := lt_of_le_of_lt following earlier
      simp only [expand, before, dite_true]
      by_cases same : cursor = index
      · subst index
        right
        exact ⟨_, List.mem_cons_self, continued⟩
      · right
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          index, earlier, by omega, continued⟩

theorem tick_covers {environment : Environment} {goal : Goal}
    {state : State environment goal} {wanted : Result environment goal}
    (meaning : StateAccepts state wanted) :
    StateAccepts (tick environment goal state) wanted := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, Scheduler.tick, agenda] using meaning
  | cons head rest =>
      unfold tick Scheduler.tick
      rw [agenda]
      rcases meaning with emitted | ⟨task, member, pending⟩
      · exact Or.inl (List.mem_append_left _ emitted)
      · rcases List.mem_cons.mp (agenda ▸ member) with same | later
        · subst task
          rcases expand_covers pending with emitted | ⟨child, childMember, childMeaning⟩
          · exact Or.inl (List.mem_append_right _ emitted)
          · exact Or.inr ⟨child, List.mem_append_left _ childMember, childMeaning⟩
        · exact Or.inr ⟨task, List.mem_append_right _ later, pending⟩

theorem run_covers {environment : Environment} {goal : Goal}
    (fuel : Nat) {state : State environment goal} {wanted : Result environment goal}
    (meaning : StateAccepts state wanted) :
    StateAccepts (run environment goal fuel state) wanted := by
  induction fuel generalizing state with
  | zero => exact meaning
  | succ fuel ih => exact ih (tick_covers meaning)

/-- Every ordered independent semantic answer occurs in the actual finite
completed execution, retaining its assignment and full history. -/
theorem finish_contains (environment : Environment) (goal : Goal)
    (wanted : Result environment goal) (ordered : wanted.ordered = true) :
    wanted ∈ (finish environment goal).answers := by
  have initial : StateAccepts (start environment goal) wanted := by
    right
    exact ⟨_, List.mem_cons_self, wanted, ordered, rfl⟩
  have final := run_covers (treeStart environment goal).cost initial
  rcases final with emitted | ⟨task, member, _⟩
  · exact emitted
  · have empty := finish_settled environment goal
    rw [show (run environment goal (treeStart environment goal).cost
      (start environment goal)).agenda = [] from empty] at member
    exact False.elim (List.not_mem_nil member)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The original root continuation constructs the firing only after the
ordered premise result, actual scoped reduct and target typing all succeed.
Its emitted task keeps exactly those captures, traces and guard events. -/
theorem delivered_root_body_retains_guarded_firing
    (environment : GeneralPremise.Environment) (bound : List TypeExpr) (sort : TypeExpr) (source : Pattern)
    (index : Nat) (rule : RewriteRule) (spec : RuleBindingSpec)
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : RuleBinding.admittedFor rule spec = true)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound sort source)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : ScopedRuleMatching.Assignment)
    (matched : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 [] rule.left source trace captured)
    (captureTyped : GeneralPremise.TypedAssignment environment ⟨index, rule, spec, bound, 0, 0⟩ captured)
    (history : List GeneralPremise.Event)
    (premises : GeneralPremise.PremisesHold environment ⟨index, rule, spec, bound, 0, 0⟩
      rule.premises captured completed history)
    (target : Pattern)
    (converted : ScopedRuleMatching.reductWith? (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      rule spec bound.length completed = some target)
    (checked : checkOpenPatternWellSorted environment.language environment.free bound sort target = true) :
    ∃ firing : GeneralPremise.RootFiring environment bound sort source index trace captured completed history target,
      (GeneralPremise.Execution.delivered environment (.root bound sort source index)
        (.premises completed history premises)
        (.rootBody bound sort source index rule spec declared specified admitted sourceTyped trace captured matched captureTyped
          (.done (.root bound sort source index)))).tasks =
      [.deliver (.root trace captured completed history target firing) (.done (.root bound sort source index))] := by
  refine ⟨.fire declared specified admitted sourceTyped matched captureTyped premises converted
    (checkOpenPatternWellSorted_sound checked), ?_⟩
  rw [GeneralPremise.Execution.delivered.eq_7]
  split
  · rename_i unavailable
    simp [converted] at unavailable
  · rename_i actual actualRead
    have same : actual = target := Option.some.inj (actualRead.symm.trans converted)
    subst actual
    simp only [dif_pos checked]

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching
open ConditionalEquationExecution
open ScopedReflectiveExecution
open Substitution
open GeneralScopedMatchMachine
open Query

def goalFreeWithin (footprint : List String) : Execution.Goal → Prop
  | .premise context _ initial => admittedFor context.rule context.spec = true ∧
      assignmentFreeWithin footprint initial
  | .premises context _ initial => admittedFor context.rule context.spec = true ∧
      assignmentFreeWithin footprint initial
  | .quantified context _ _ _ elements initial => admittedFor context.rule context.spec = true ∧
      assignmentFreeWithin footprint initial ∧ patternsFreeWithin footprint elements
  | .root _ _ source _ => ∀ name ∈ source.freeFvarNames, name ∈ footprint
  | .steps _ _ source _ => ∀ name ∈ source.freeFvarNames, name ∈ footprint

def resultFreeWithin (footprint : List String) {environment : Environment} {goal : Execution.Goal}
    (result : Execution.Result environment goal) : Prop :=
  goalFreeWithin footprint goal ∧
  match result with
  | .premise assignment _ _ => assignmentFreeWithin footprint assignment
  | .premises assignment _ _ => assignmentFreeWithin footprint assignment
  | .quantified assignment _ _ => assignmentFreeWithin footprint assignment
  | .root _ captured completed _ target _ => assignmentFreeWithin footprint captured ∧
      assignmentFreeWithin footprint completed ∧
      (∀ name ∈ target.freeFvarNames, name ∈ footprint)
  | .steps _ _ captured completed _ target _ _ => assignmentFreeWithin footprint captured ∧
      assignmentFreeWithin footprint completed ∧
      (∀ name ∈ target.freeFvarNames, name ∈ footprint)

def stepCallFreeWithin (footprint : List String) {environment : Environment}
    (call : Execution.StepCall environment) : Prop :=
  admittedFor call.context.rule call.context.spec = true ∧
  assignmentFreeWithin footprint call.initial ∧
  (∀ name ∈ call.source.freeFvarNames, name ∈ footprint)

def continuationFreeWithin (footprint : List String) {environment : Environment} :
    {goal outer : Execution.Goal} → Execution.Continuation environment goal outer → Prop
  | _, _, .done goal => goalFreeWithin footprint goal
  | _, _, .nextPremise context premise premises initial tail =>
      goalFreeWithin footprint (.premises context (premise :: premises) initial) ∧
      continuationFreeWithin footprint tail
  | _, _, .prepend context premise premises initial middle _ _ tail =>
      goalFreeWithin footprint (.premises context (premise :: premises) initial) ∧
      assignmentFreeWithin footprint middle ∧ continuationFreeWithin footprint tail
  | _, _, .quantifier context collection parameter body initial _ elements _ tail =>
      goalFreeWithin footprint (.premise context (.forAll collection parameter body) initial) ∧
      patternsFreeWithin footprint elements ∧ continuationFreeWithin footprint tail
  | _, _, .element context parameter body index element elements initial _ tail =>
      goalFreeWithin footprint (.quantified context parameter body index (element :: elements) initial) ∧
      continuationFreeWithin footprint tail
  | _, _, .prependElement context parameter body index element elements initial middle _ _ _ tail =>
      goalFreeWithin footprint (.quantified context parameter body index (element :: elements) initial) ∧
      assignmentFreeWithin footprint middle ∧ continuationFreeWithin footprint tail
  | _, _, .rootBody bound type source index _ _ _ _ _ _ _ captured _ _ tail =>
      goalFreeWithin footprint (.root bound type source index) ∧
      assignmentFreeWithin footprint captured ∧ continuationFreeWithin footprint tail
  | _, _, .searchedRoot bound type source _ limit _ tail =>
      goalFreeWithin footprint (.steps bound type source limit) ∧ continuationFreeWithin footprint tail
  | _, _, .stepped call tail => stepCallFreeWithin footprint call ∧ continuationFreeWithin footprint tail

def taskFreeWithin (footprint : List String) {environment : Environment} {outer : Execution.Goal} :
    Execution.Task environment outer → Prop
  | .evaluate goal tail => goalFreeWithin footprint goal ∧ continuationFreeWithin footprint tail
  | .deliver result tail => resultFreeWithin footprint result ∧ continuationFreeWithin footprint tail
  | .query request state _ tail =>
      goalFreeWithin footprint (.premise request.context (.relationQuery request.relation request.arguments) request.initial) ∧
      Query.stateFreeWithin footprint environment request state ∧ continuationFreeWithin footprint tail
  | .rootMatch frame =>
      (∀ name ∈ frame.source.freeFvarNames, name ∈ footprint) ∧ continuationFreeWithin footprint frame.tail
  | .targetMatch frame => stepCallFreeWithin footprint frame.call ∧
      assignmentFreeWithin footprint frame.captured ∧ assignmentFreeWithin footprint frame.completed ∧
      (∀ name ∈ frame.target.freeFvarNames, name ∈ footprint) ∧ continuationFreeWithin footprint frame.tail
  | .scanChildren _ _ source _ _ tail =>
      (∀ name ∈ source.freeFvarNames, name ∈ footprint) ∧ continuationFreeWithin footprint tail

def stateFreeWithin (footprint : List String) (environment : Environment) (goal : Execution.Goal)
    (state : Execution.State environment goal) : Prop :=
  (∀ task ∈ state.agenda, taskFreeWithin footprint task) ∧
  (∀ result ∈ state.answers, resultFreeWithin footprint result)

theorem delivered_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal) {goal : Execution.Goal} (result : Execution.Result environment goal)
    (tail : Execution.Continuation environment goal outer)
    (produced : resultFreeWithin footprint result) (continued : continuationFreeWithin footprint tail) :
    (∀ task ∈ (Execution.delivered environment outer result tail).tasks, taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.delivered environment outer result tail).answers, resultFreeWithin footprint answer) := by
  cases tail with
  | done goal =>
      constructor
      · intro task member; cases member
      · intro answer member
        rcases List.mem_singleton.mp member with rfl
        exact produced
  | nextPremise context premise premises initial tail =>
      cases result with
      | premise assignment event valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨produced.1.1, produced.2⟩, continued.1, produced.2, continued.2⟩
          · intro answer member; cases member

  | prepend context premise premises initial middle event head tail =>
      cases result with
      | premises assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2.2⟩
          · intro answer member; cases member
  | quantifier context collection parameter body initial kind elements read tail =>
      cases result with
      | quantified assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2.2⟩
          · intro answer member; cases member
  | element context parameter body index element elements initial localTyped tail =>
      cases result with
      | premise assignment event valid =>
          have restored := restored_parameter_free_within footprint parameter initial assignment continued.1.2.1 produced.2
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            refine ⟨⟨continued.1.1, restored, ?_⟩, continued.1, produced.2, continued.2⟩
            intro pattern member name occurs
            exact continued.1.2.2 pattern (List.mem_cons_of_mem _ member) name occurs
          · intro answer member; cases member
  | prependElement context parameter body index element elements initial middle event localTyped head tail =>
      cases result with
      | quantified assignment events valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2.2⟩
          · intro answer member; cases member
  | rootBody bound type source index rule spec declared specified admitted sorted trace captured matched capturedTyped tail =>
      cases result with
      | premises assignment events valid =>
          simp only [Execution.delivered]
          split
          · constructor <;> intro item member <;> cases member
          · rename_i target converted
            split
            · have covered := selected_reduct_free_within footprint environment.reflection rule spec admitted
                bound.length assignment target produced.2 converted
              constructor
              · intro task member
                rcases List.mem_singleton.mp member with rfl
                exact ⟨⟨continued.1, continued.2.1, produced.2, covered⟩, continued.2.2⟩
              · intro answer member; cases member
            · constructor <;> intro item member <;> cases member
  | searchedRoot bound type source index limit earlier tail =>
      cases result with
      | root trace captured completed events target valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨continued.1, produced.2⟩, continued.2⟩
          · intro answer member; cases member
  | stepped call tail =>
      cases result with
      | steps index trace captured completed events target earlier valid =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨continued.1, produced.2.1, produced.2.2.1, produced.2.2.2, continued.2⟩
          · intro answer member; cases member


theorem evaluate_premise_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal) (context : Context) (premise : Premise) (initial : Assignment)
    (tail : Execution.Continuation environment (.premise context premise initial) outer)
    (admitted : admittedFor context.rule context.spec = true)
    (stored : assignmentFreeWithin footprint initial)
    (continued : continuationFreeWithin footprint tail) :
    (∀ task ∈ (Execution.evaluatePremise environment outer context premise initial tail).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.evaluatePremise environment outer context premise initial tail).answers,
      resultFreeWithin footprint answer) := by
  cases premise with
  | relationQuery relation arguments =>
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨⟨admitted, stored⟩, Query.start_free_within footprint environment _ stored, continued⟩
      · intro answer member; cases member
  | freshness condition =>
      simp only [Execution.evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨⟨admitted, stored⟩, stored⟩, continued⟩
          · intro answer member; cases member
        · constructor <;> intro item member <;> cases member
  | forAll collection parameter body =>
      simp only [Execution.evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i kind elements read
        have elementsCovered := finite_collection_free_within footprint context.bound.length initial collection kind elements stored read
        constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          exact ⟨⟨admitted, stored, elementsCovered⟩, ⟨admitted, stored⟩, elementsCovered, continued⟩
        · intro answer member; cases member
  | congruence source target =>
      simp only [Execution.evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor <;> intro item member <;> cases member
        · rename_i actual interpreted
          have actualCovered := admitted_instantiate_with_free_within footprint Substitution.instantiateBVar
            (instantiate_bvar_free_within footprint) context.rule context.spec admitted context.bound.length
            (context.site 0) [] 0 initial source actual stored interpreted
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨actualCovered, ⟨admitted, stored, actualCovered⟩, continued⟩
          · intro answer member; cases member
  | scopedStep step =>
      simp only [Execution.evaluatePremise]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i actual interpreted
        have actualCovered := admitted_instantiate_with_free_within footprint Substitution.instantiateBVar
          (instantiate_bvar_free_within footprint) context.rule context.spec admitted context.bound.length
          (context.site 0) [] step.binders.length initial step.source actual stored interpreted
        constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          exact ⟨actualCovered, ⟨admitted, stored, actualCovered⟩, continued⟩
        · intro answer member; cases member

theorem evaluate_root_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (index : Nat)
    (tail : Execution.Continuation environment (.root bound type source index) outer)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint)
    (continued : continuationFreeWithin footprint tail) :
    (∀ task ∈ (Execution.evaluateRoot environment outer bound type source index tail).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.evaluateRoot environment outer bound type source index tail).answers,
      resultFreeWithin footprint answer) := by
  unfold Execution.evaluateRoot
  split
  · constructor <;> intro item member <;> cases member
  · split
    · constructor <;> intro item member <;> cases member
    · split
      · split
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered, continued⟩
          · intro answer member; cases member
        · constructor <;> intro item member <;> cases member
      · constructor <;> intro item member <;> cases member

theorem evaluate_free_within (footprint : List String) (environment : Environment)
    (outer goal : Execution.Goal) (tail : Execution.Continuation environment goal outer)
    (covered : goalFreeWithin footprint goal) (continued : continuationFreeWithin footprint tail) :
    (∀ task ∈ (Execution.evaluate environment outer goal tail).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.evaluate environment outer goal tail).answers,
      resultFreeWithin footprint answer) := by
  cases goal with
  | premise context premise initial =>
      exact evaluate_premise_free_within footprint environment outer context premise initial tail covered.1 covered.2 continued
  | premises context premises initial =>
      cases premises with
      | nil =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨covered, covered.2⟩, continued⟩
          · intro answer member; cases member
      | cons premise premises =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered, covered, continued⟩
          · intro answer member; cases member
  | quantified context parameter body index elements initial =>
      cases elements with
      | nil =>
          constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨⟨covered, covered.2.1⟩, continued⟩
          · intro answer member; cases member
      | cons element elements =>
          simp only [Execution.evaluate]
          split
          · have boundCovered := bound_parameter_free_within footprint parameter (localValue context.bound element) initial covered.2.1
              (covered.2.2 element (by simp))
            constructor
            · intro task member
              rcases List.mem_singleton.mp member with rfl
              exact ⟨⟨covered.1, boundCovered⟩, covered, continued⟩
            · intro answer member; cases member
          · constructor <;> intro item member <;> cases member
  | root bound type source index => exact evaluate_root_free_within footprint environment outer bound type source index tail covered continued
  | steps bound type source limit =>
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨covered, continued⟩
      · intro answer member; cases member

theorem root_match_expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal) (frame : Execution.RootMatchFrame environment outer)
    (source : ∀ name ∈ frame.source.freeFvarNames, name ∈ footprint)
    (continued : continuationFreeWithin footprint frame.tail) :
    (∀ task ∈ (Execution.expandRootMatch environment outer frame).tasks, taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.expandRootMatch environment outer frame).answers, resultFreeWithin footprint answer) := by
  unfold Execution.expandRootMatch
  split
  · rename_i answer found
    dsimp only
    split
    · have captured := matcher_answer_free_within _ frame.state frame.reachable answer
        (List.mem_of_getElem? found) footprint (by intro entry member; cases member) source
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨⟨frame.admitted, captured⟩, source, captured, continued⟩
        · exact ⟨source, continued⟩
      · intro answer member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨source, continued⟩
      · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨source, continued⟩
      · intro answer member; cases member

theorem target_match_expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal) (frame : Execution.TargetMatchFrame environment outer)
    (call : stepCallFreeWithin footprint frame.call)
    (captured : assignmentFreeWithin footprint frame.captured)
    (completed : assignmentFreeWithin footprint frame.completed)
    (target : ∀ name ∈ frame.target.freeFvarNames, name ∈ footprint)
    (continued : continuationFreeWithin footprint frame.tail) :
    (∀ task ∈ (Execution.expandTargetMatch environment outer frame).tasks, taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.expandTargetMatch environment outer frame).answers, resultFreeWithin footprint answer) := by
  unfold Execution.expandTargetMatch
  split
  · rename_i answer found
    split
    · have final := matcher_answer_free_within _ frame.state frame.reachable answer
        (List.mem_of_getElem? found) footprint call.2.1 target
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨⟨⟨call.1, call.2.1⟩, final⟩, continued⟩
        · exact ⟨call, captured, completed, target, continued⟩
      · intro answer member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨call, captured, completed, target, continued⟩
      · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨call, captured, completed, target, continued⟩
      · intro answer member; cases member
theorem query_outer_expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal) (request : Query.Request) (state : Query.State environment request) (cursor : Nat)
    (tail : Execution.Continuation environment
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial) outer)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (initial : goalFreeWithin footprint
      (.premise request.context (.relationQuery request.relation request.arguments) request.initial))
    (query : Query.stateFreeWithin footprint environment request state)
    (continued : continuationFreeWithin footprint tail) :
    (∀ task ∈ (Execution.expandQuery environment outer request state cursor tail).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Execution.expandQuery environment outer request state cursor tail).answers,
      resultFreeWithin footprint answer) := by
  unfold Execution.expandQuery
  split
  · rename_i answer found
    have stored := query.2 answer (List.mem_of_getElem? found)
    constructor
    · intro task member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨⟨initial, stored⟩, continued⟩
      · exact ⟨initial, query, continued⟩
    · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨initial, Query.tick_free_within footprint environment request provider state query, continued⟩
      · intro answer member; cases member

theorem expansion_free_within (footprint : List String) (environment : Environment)
    (outer : Execution.Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (task : Execution.Task environment outer) (covered : taskFreeWithin footprint task) :
    (∀ next ∈ (Execution.expand environment outer task).tasks, taskFreeWithin footprint next) ∧
    (∀ answer ∈ (Execution.expand environment outer task).answers, resultFreeWithin footprint answer) := by
  cases task with
  | evaluate goal tail => exact evaluate_free_within footprint environment outer goal tail covered.1 covered.2
  | deliver result tail => exact delivered_free_within footprint environment outer result tail covered.1 covered.2
  | query request state cursor tail => exact query_outer_expansion_free_within footprint environment outer request state cursor tail provider covered.1 covered.2.1 covered.2.2
  | rootMatch frame => exact root_match_expansion_free_within footprint environment outer frame covered.1 covered.2
  | targetMatch frame => exact target_match_expansion_free_within footprint environment outer frame covered.1 covered.2.1 covered.2.2.1 covered.2.2.2.1 covered.2.2.2.2
  | scanChildren bound type source limit cursor tail =>
      simp only [Execution.expand]
      split
      · constructor
        · intro next member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨covered.1, covered.1, covered.2⟩
          · exact covered
        · intro answer member; cases member
      · constructor <;> intro item member <;> cases member

theorem tick_free_within (footprint : List String) (environment : Environment) (goal : Execution.Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (state : Execution.State environment goal) (covered : stateFreeWithin footprint environment goal state) :
    stateFreeWithin footprint environment goal (Execution.tick environment goal state) :=
  Scheduler.tick_preserves (taskFreeWithin footprint) (resultFreeWithin footprint)
    (Execution.expand environment goal) (expansion_free_within footprint environment goal provider) state covered

theorem run_free_within (footprint : List String) (environment : Environment) (goal : Execution.Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (fuel : Nat) (state : Execution.State environment goal) (covered : stateFreeWithin footprint environment goal state) :
    stateFreeWithin footprint environment goal (Execution.run environment goal fuel state) :=
  Scheduler.run_preserves (taskFreeWithin footprint) (resultFreeWithin footprint)
    (Execution.expand environment goal) (expansion_free_within footprint environment goal provider) fuel state covered

theorem start_free_within (footprint : List String) (environment : Environment) (goal : Execution.Goal)
    (initial : goalFreeWithin footprint goal) :
    stateFreeWithin footprint environment goal (Execution.start environment goal) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨initial, initial⟩
  · intro result member; cases member

theorem run_from_start_free_within (footprint : List String) (environment : Environment)
    (goal : Execution.Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (initial : goalFreeWithin footprint goal) (fuel : Nat) :
    stateFreeWithin footprint environment goal
      (Execution.run environment goal fuel (Execution.start environment goal)) :=
  run_free_within footprint environment goal provider fuel _ (start_free_within footprint environment goal initial)

theorem run_task_free_within (footprint : List String) (environment : Environment)
    (goal : Execution.Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (initial : goalFreeWithin footprint goal) (fuel : Nat)
    (task : Execution.Task environment goal)
    (member : task ∈ (Execution.run environment goal fuel (Execution.start environment goal)).agenda) :
    taskFreeWithin footprint task :=
  (run_from_start_free_within footprint environment goal provider initial fuel).1 task member

theorem run_result_free_within (footprint : List String) (environment : Environment)
    (goal : Execution.Goal)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (initial : goalFreeWithin footprint goal) (fuel : Nat)
    (result : Execution.Result environment goal)
    (member : result ∈ (Execution.run environment goal fuel (Execution.start environment goal)).answers) :
    resultFreeWithin footprint result :=
  (run_from_start_free_within footprint environment goal provider initial fuel).2 result member
theorem root_run_receipt_free_within (footprint : List String) (environment : Environment)
    (bound : List TypeExpr) (type : TypeExpr) (source target : Pattern) (index : Nat)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (covered : ∀ name ∈ source.freeFvarNames, name ∈ footprint) (fuel : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment) (history : List Event)
    (valid : RootFiring environment bound type source index trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run environment (.root bound type source index) fuel
        (Execution.start environment (.root bound type source index))).answers) :
    assignmentFreeWithin footprint captured ∧ assignmentFreeWithin footprint completed ∧
      (∀ name ∈ target.freeFvarNames, name ∈ footprint) :=
  (run_result_free_within footprint environment (.root bound type source index) provider covered fuel _ member).2

theorem premises_run_assignment_free_within (footprint : List String) (environment : Environment)
    (context : Context) (premises : List Premise) (initial completed : Assignment) (history : List Event)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (admitted : admittedFor context.rule context.spec = true)
    (stored : assignmentFreeWithin footprint initial) (fuel : Nat)
    (valid : PremisesHold environment context premises initial completed history)
    (member : Execution.Result.premises completed history valid ∈
      (Execution.run environment (.premises context premises initial) fuel
        (Execution.start environment (.premises context premises initial))).answers) :
    assignmentFreeWithin footprint completed :=
  (run_result_free_within footprint environment (.premises context premises initial) provider
    ⟨admitted, stored⟩ fuel _ member).2
theorem root_run_finite_free_within (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (index fuel : Nat) :
    stateFreeWithin (source.freeFvarNames ++ providerFreeNames environment.provider)
      environment (.root bound type source index)
      (Execution.run environment (.root bound type source index) fuel
        (Execution.start environment (.root bound type source index))) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · intro name member
    exact List.mem_append_left _ member

theorem steps_run_finite_free_within (environment : Environment) (bound : List TypeExpr)
    (type : TypeExpr) (source : Pattern) (limit fuel : Nat) :
    stateFreeWithin (source.freeFvarNames ++ providerFreeNames environment.provider)
      environment (.steps bound type source limit)
      (Execution.run environment (.steps bound type source limit) fuel
        (Execution.start environment (.steps bound type source limit))) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · intro name member
    exact List.mem_append_left _ member

theorem premises_run_finite_free_within (environment : Environment) (context : Context)
    (premises : List Premise) (initial : Assignment) (fuel : Nat)
    (admitted : admittedFor context.rule context.spec = true) :
    stateFreeWithin (ConditionalEquationExecution.assignmentFreeNames initial ++ providerFreeNames environment.provider)
      environment (.premises context premises initial)
      (Execution.run environment (.premises context premises initial) fuel
        (Execution.start environment (.premises context premises initial))) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · exact ⟨admitted, assignment_coverage_mono _ _ initial
      (fun name member => List.mem_append_left _ member) (assignment_covered_by_own_names initial)⟩

theorem premise_run_finite_free_within (environment : Environment) (context : Context)
    (premise : Premise) (initial : Assignment) (fuel : Nat)
    (admitted : admittedFor context.rule context.spec = true) :
    stateFreeWithin (ConditionalEquationExecution.assignmentFreeNames initial ++ providerFreeNames environment.provider)
      environment (.premise context premise initial)
      (Execution.run environment (.premise context premise initial) fuel
        (Execution.start environment (.premise context premise initial))) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · exact ⟨admitted, assignment_coverage_mono _ _ initial
      (fun name member => List.mem_append_left _ member) (assignment_covered_by_own_names initial)⟩

theorem quantified_run_finite_free_within (environment : Environment) (context : Context)
    (parameter : String) (body : Premise) (index : Nat) (elements : List Pattern)
    (initial : Assignment) (fuel : Nat)
    (admitted : admittedFor context.rule context.spec = true) :
    stateFreeWithin
      (ConditionalEquationExecution.assignmentFreeNames initial ++
        elements.flatMap Pattern.freeFvarNames ++ providerFreeNames environment.provider)
      environment (.quantified context parameter body index elements initial)
      (Execution.run environment (.quantified context parameter body index elements initial) fuel
        (Execution.start environment (.quantified context parameter body index elements initial))) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · refine ⟨admitted, ?_, ?_⟩
    · exact assignment_coverage_mono _ _ initial
        (fun name member => List.mem_append_left _ (List.mem_append_left _ member))
        (assignment_covered_by_own_names initial)
    · intro element member name occurs
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨element, member, occurs⟩))

theorem root_run_receipt_finite_free_within (environment : Environment)
    (bound : List TypeExpr) (type : TypeExpr) (source target : Pattern) (index fuel : Nat)
    (trace : List GeneralScopedMatchMachine.BagChoice) (captured completed : Assignment) (history : List Event)
    (valid : RootFiring environment bound type source index trace captured completed history target)
    (member : Execution.Result.root trace captured completed history target valid ∈
      (Execution.run environment (.root bound type source index) fuel
        (Execution.start environment (.root bound type source index))).answers) :
    assignmentFreeWithin (source.freeFvarNames ++ providerFreeNames environment.provider) captured ∧
    assignmentFreeWithin (source.freeFvarNames ++ providerFreeNames environment.provider) completed ∧
    (∀ name ∈ target.freeFvarNames, name ∈ source.freeFvarNames ++ providerFreeNames environment.provider) :=
  ((root_run_finite_free_within environment bound type source index fuel).2 _ member).2

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.goalFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.resultFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.stepCallFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.continuationFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.taskFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.stateFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.delivered_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.evaluate_premise_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.evaluate_root_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.evaluate_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.root_match_expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.target_match_expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.query_outer_expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.tick_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.run_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.start_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.run_from_start_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.run_task_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.run_result_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.root_run_receipt_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.premises_run_assignment_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.root_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.steps_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.premises_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.premise_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.quantified_run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution.root_run_receipt_finite_free_within

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
