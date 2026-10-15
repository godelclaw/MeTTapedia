import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledSemantics
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledTermination
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCursor

/-!
# Semantic coverage of actual suspended premise execution

The denotation of a suspended task retains unread alternatives and the
independent meaning of its continuation. Every actual transition preserves
each denoted answer. Finite drainage therefore yields semantic completeness
for structurally bounded premise derivations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

def TaskAccepts {environment : Environment} {outer : Goal}
    (task : Task environment outer) (wanted : Result environment outer) : Prop :=
  match task with
  | .evaluate _ tail => EvaluatesTo tail wanted
  | .deliver result tail => Concludes tail result wanted
  | .query _ request state cursor tail =>
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
          EvaluatesTo (.rootBody frame.depth frame.bound frame.type frame.source frame.index frame.rule frame.spec
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
  | .scanChildren depth bound type source limit cursor tail =>
      ∃ (index : Nat) (earlier : index < limit), cursor ≤ index ∧
        EvaluatesTo (.searchedRoot depth bound type source index limit earlier tail) wanted

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
  | nextPremise depth context premise premises initial tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, ordered, concludes⟩ := meaning
          simp only [ExpansionAccepts, delivered, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨.premises final events rest, by simpa [Result.ordered] using ordered, concludes⟩
  | prepend depth context premise premises initial middle event head tail =>
      cases result with
      | premises final events rest =>
          change ExpansionAccepts
            {tasks := [.deliver (.premises final (event :: events) (.cons head rest)) tail]} wanted
          simp only [ExpansionAccepts, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          change Concludes tail (.premises final (event :: events) (.cons head rest)) wanted at meaning
          exact meaning
  | quantifier depth context collection parameter body initial kind elements read tail =>
      cases result
      simpa only [ExpansionAccepts, delivered.eq_4, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, TaskAccepts, Concludes.eq_4] using meaning
  | element depth context parameter body index element elements initial localTyped tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, ordered, concludes⟩ := meaning
          change ExpansionAccepts
            { tasks := [.evaluate
                (.quantified depth context parameter body (index + 1) elements
                  (restoreParameter parameter initial middle))
                (.prependElement depth context parameter body index element elements initial middle
                  event localTyped head tail)] } wanted
          simp only [ExpansionAccepts, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨.quantified final events rest, by simpa [Result.ordered] using ordered, concludes⟩
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
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
  | rootBody depth bound type source index rule spec declared specified admitted sorted trace captured
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
  | searchedRoot depth bound type source index limit earlier tail =>
      cases result
      simpa only [ExpansionAccepts, delivered.eq_8, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, TaskAccepts, Concludes.eq_8] using meaning
  | stepped depth call tail =>
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
  | premises depth context premises initial =>
      cases result with
      | premises final events held =>
          cases held with
          | nil =>
              simpa only [ExpansionAccepts, evaluate.eq_2, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts] using concludes
          | @cons context premise premises initial middle final event events head rest =>
              have parts : eventDepth event ≤ depth ∧
                  eventsDepth events ≤ depth := by
                simpa [Result.ordered, eventsDepth, Nat.max_le] using ordered
              simp only [ExpansionAccepts, evaluate.eq_3, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨.premise middle event head, by simpa [Result.ordered] using parts.1,
                final, events, rest, parts.2, concludes⟩
  | quantified depth context parameter body index elements initial =>
      cases result with
      | quantified final events held =>
          cases held with
          | nil => simpa only [ExpansionAccepts, evaluate.eq_4, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts] using concludes
          | @cons context parameter body index element elements initial middle final event events localTyped head rest =>
              have checked := checkTypedAssignment_complete localTyped
              have parts : eventDepth event ≤ depth ∧
                  elementsDepth events ≤ depth := by
                simpa [Result.ordered, elementsDepth, eventsDepth, Nat.max_le] using ordered
              simp only [ExpansionAccepts, evaluate.eq_5, checked, dite_true, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨.premise middle event head, by simpa [Result.ordered] using parts.1,
                final, events, rest, parts.2, concludes⟩
  | premise depth context premise initial =>
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
              have earlier : childIndex < environment.language.rewrites.length := by
                cases child with
                | fire declared _ _ _ _ _ _ _ _ =>
                    exact (List.getElem?_eq_some_iff.mp declared).1
              have parts : childIndex < environment.language.rewrites.length ∧
                  decide (1 + eventsDepth history ≤ depth) = true := by
                exact ⟨earlier, by simpa [Result.ordered, eventDepth] using ordered⟩
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
              have earlier : childIndex < environment.language.rewrites.length := by
                cases child with
                | fire declared _ _ _ _ _ _ _ _ =>
                    exact (List.getElem?_eq_some_iff.mp declared).1
              have parts : childIndex < environment.language.rewrites.length ∧
                  decide (1 + eventsDepth history ≤ depth) = true := by
                exact ⟨earlier, by simpa [Result.ordered, eventDepth] using ordered⟩
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
                  by simpa [Result.ordered, eventDepth] using ordered, concludes⟩
  | root depth bound type source index =>
      cases depth with
      | zero =>
          cases result with
          | root _ _ _ _ _ _ => simp [Result.ordered] at ordered
      | succ depth =>
          cases result with
          | root trace captured completed history target held =>
              cases held with
              | @fire bound type source target index rule spec captured completed trace history
                  declared specified admitted sorted matched capturedTyped premises converted targetTyped =>
                  have checked := checkOpenPatternWellSorted_complete sorted
                  rw [evaluate.eq_6, evaluateRoot.eq_2]
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
                      have bounded : eventsDepth history ≤ depth := by
                        have h : 1 + eventsDepth history ≤ depth + 1 := by
                          simpa [Result.ordered] using ordered
                        omega
                      exact ⟨.premises completed history premises,
                        by simpa [Result.ordered] using bounded,
                        target, converted, targetTyped, concludes⟩
  | steps depth bound type source limit =>
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

theorem query_covers {environment : Environment} {outer : Goal} {depth : Nat}
    {request : Query.Request} {state : Query.State environment request} {cursor : Nat}
    {tail : Continuation environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer}
    {wanted : Result environment outer}
    (meaning : TaskAccepts (.query depth request state cursor tail) wanted) :
    ExpansionAccepts (expandQuery environment outer depth request state cursor tail) wanted := by
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
  | query depth request state cursor tail => exact query_covers meaning
  | rootMatch frame => exact rootMatch_covers meaning
  | targetMatch frame => exact targetMatch_covers meaning
  | scanChildren depth bound type source limit cursor tail =>
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

/-- Every depth-bounded independent semantic answer occurs in the actual finite
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

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
