import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledSemantics
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledTermination
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness

/-!
# Semantic coverage of retained premise execution

Unread alternatives and continuation meaning are independent of scheduling.
Coverage is proved for the selected matching interpretation over every premise
constructor. Actual drainage implies complete depth-bounded publication; the
ordinary finite-work execution is a specialization.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled

open Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {matcher : MatchingExecution}

abbrev Represents (matcher : MatchingExecution) :=
  ∀ query trace final, matcher.meaning.Matches query trace final →
    ∃ answer : matcher.Answer, matcher.trace answer = trace ∧ matcher.assignment answer = final

def TaskAccepts (laws : matcher.CursorLaws) {environment : Environment} {outer : Goal}
    (task : Interpreted.Task matcher environment outer) (wanted : Interpreted.Result matcher environment outer) : Prop :=
  match task with
  | .evaluate _ tail => EvaluatesTo tail wanted
  | .deliver result tail => Concludes tail result wanted
  | .query _ request state cursor tail =>
      Query.StateWellFormed environment request state ∧ cursor ≤ state.answers.length ∧
      ∃ answer : Query.Answer environment request matcher,
        Query.UnreadAccepts laws environment request state cursor answer ∧
        Concludes tail (.premise answer.assignment
          (.query request.context.premiseIndex request.context.quantifierDepth
            answer.rowIndex answer.origins) (.query answer.valid)) wanted
  | .rootMatch frame =>
      frame.cursor ≤ (matcher.answers frame.state).length ∧
      ∃ answer : matcher.Answer,
        laws.Unread (rootRequest frame)
          frame.state frame.cursor answer ∧
        ∃ (matched : matcher.meaning.Matches (rootRequest frame) (matcher.trace answer) (matcher.assignment answer))
            (typed : TypedAssignment environment
              ⟨frame.index, frame.rule, frame.spec, frame.bound, 0, 0⟩ (matcher.assignment answer)),
          EvaluatesTo (.rootBody frame.depth frame.bound frame.type frame.source frame.index frame.rule frame.spec
            frame.declared frame.specified frame.admitted frame.sorted (matcher.trace answer) (matcher.assignment answer)
            matched typed frame.tail) wanted
  | .targetMatch frame =>
      frame.cursor ≤ (matcher.answers frame.state).length ∧
      ∃ answer : matcher.Answer,
        laws.Unread (targetRequest frame)
          frame.state frame.cursor answer ∧
        ∃ (matched : matcher.meaning.Matches (targetRequest frame) (matcher.trace answer) (matcher.assignment answer))
            (typed : TypedAssignment environment frame.call.context (matcher.assignment answer)),
          Concludes frame.tail (.premise (matcher.assignment answer)
            (.child frame.call.context.premiseIndex frame.call.context.quantifierDepth frame.index
              (frame.call.binders ++ frame.call.context.bound) frame.call.source frame.target
              frame.trace (matcher.trace answer) frame.captured frame.completed frame.history)
            (frame.call.conclude _ _ _ _ _ _ _ _ frame.valid matched typed)) wanted
  | .scanChildren depth bound type source limit cursor tail =>
      ∃ (index : Nat) (earlier : index < limit), cursor ≤ index ∧
        EvaluatesTo (.searchedRoot depth bound type source index limit earlier tail) wanted

def StateAccepts (laws : matcher.CursorLaws) {environment : Environment} {goal : Goal}
    (state : State environment goal matcher) (wanted : Interpreted.Result matcher environment goal) : Prop :=
  wanted ∈ state.answers ∨ ∃ task ∈ state.agenda, TaskAccepts laws task wanted

def ExpansionAccepts (laws : matcher.CursorLaws) {environment : Environment} {goal : Goal}
    (expansion : Scheduler.Expansion (Interpreted.Task matcher environment goal) (Interpreted.Result matcher environment goal) Obligation)
    (wanted : Interpreted.Result matcher environment goal) : Prop :=
  wanted ∈ expansion.answers ∨ ∃ task ∈ expansion.tasks, TaskAccepts laws task wanted

theorem delivered_covers (laws : matcher.CursorLaws) (represented : Represents matcher) {environment : Environment} {goal outer : Goal}
    {result : Interpreted.Result matcher environment goal} {tail : Interpreted.Continuation matcher environment goal outer}
    {wanted : Interpreted.Result matcher environment outer} (meaning : Concludes tail result wanted) :
    ExpansionAccepts laws (delivered environment outer result tail) wanted := by
  cases tail with
  | done =>
      simpa [ExpansionAccepts, delivered, Concludes] using meaning.symm
  | nextPremise depth context premise premises initial tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, ordered, concludes⟩ := meaning
          simp only [ExpansionAccepts, delivered, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨.premises final events rest, by simpa [Interpreted.Result.ordered] using ordered, concludes⟩
  | prepend depth context premise premises initial middle event head tail =>
      cases result with
      | premises final events rest =>
          change ExpansionAccepts laws
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
          change ExpansionAccepts laws
            { tasks := [.evaluate
                (.quantified depth context parameter body (index + 1) elements
                  initial)
                (.prependElement depth context parameter body index element elements initial middle
                  event localTyped head tail)] } wanted
          simp only [ExpansionAccepts, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          exact ⟨.quantified final events rest, by simpa [Interpreted.Result.ordered] using ordered, concludes⟩
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
      cases result with
      | quantified final events rest =>
          change ExpansionAccepts laws
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
          obtain ⟨answer, traceEq, assignmentEq⟩ := represented _ targetTrace final matched
          cases assignmentEq
          cases traceEq
          exact ⟨Nat.zero_le _, answer, (laws.start _ _).mpr matched,
            matched, typed, concludes⟩

theorem evaluate_covers (laws : matcher.CursorLaws) (represented : Represents matcher) {environment : Environment} {goal outer : Goal}
    {tail : Interpreted.Continuation matcher environment goal outer} {wanted : Interpreted.Result matcher environment outer}
    (meaning : EvaluatesTo tail wanted) :
    ExpansionAccepts laws (evaluate environment outer goal tail) wanted := by
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
                simpa [Interpreted.Result.ordered, eventsDepth, Nat.max_le] using ordered
              simp only [ExpansionAccepts, evaluate.eq_3, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨.premise middle event head, by simpa [Interpreted.Result.ordered] using parts.1,
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
                simpa [Interpreted.Result.ordered, elementsDepth, eventsDepth, Nat.max_le] using ordered
              simp only [ExpansionAccepts, evaluate.eq_5, checked, dite_true, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨.premise middle event head, by simpa [Interpreted.Result.ordered] using parts.1,
                final, events, rest, parts.2, concludes⟩
  | premise depth context premise initial =>
      cases result with
      | premise final event held =>
          cases held with
          | @query context relation arguments initial final rowIndex origins query =>
              simp only [ExpansionAccepts, evaluate.eq_1, evaluatePremise.eq_1, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, TaskAccepts]
              exact ⟨Query.start_wellFormed _ _, by simp [Query.start],
                ⟨rowIndex, final, origins, query⟩, Query.unread_start_of_valid laws _ _ _, concludes⟩
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
                exact ⟨earlier, by simpa [Interpreted.Result.ordered, eventDepth] using ordered⟩
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
                exact ⟨earlier, by simpa [Interpreted.Result.ordered, eventDepth] using ordered⟩
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
                  by simpa [Interpreted.Result.ordered, eventDepth] using ordered, concludes⟩
  | root depth bound type source index =>
      cases depth with
      | zero =>
          cases result with
          | root _ _ _ _ _ _ => simp [Interpreted.Result.ordered] at ordered
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
                      obtain ⟨answer, traceEq, assignmentEq⟩ := represented _ trace captured matched
                      cases assignmentEq
                      cases traceEq
                      refine ⟨Nat.zero_le _, answer, (laws.start _ _).mpr matched,
                        matched, capturedTyped, ?_⟩
                      have bounded : eventsDepth history ≤ depth := by
                        have h : 1 + eventsDepth history ≤ depth + 1 := by
                          simpa [Interpreted.Result.ordered] using ordered
                        omega
                      exact ⟨.premises completed history premises,
                        by simpa [Interpreted.Result.ordered] using bounded,
                        target, converted, targetTyped, concludes⟩
  | steps depth bound type source limit =>
      cases result with
      | steps index trace captured completed history target earlier held =>
          simp only [ExpansionAccepts, evaluate.eq_7, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, TaskAccepts]
          refine ⟨index, earlier, Nat.zero_le _, ?_⟩
          exact ⟨.root trace captured completed history target held, ordered, concludes⟩


private theorem matcher_answers_grow (laws : matcher.CursorLaws)
    (request : GeneralScopedMatchMachine.Request) (state : matcher.State) :
    (matcher.answers state).length ≤ (matcher.answers (matcher.tick request state)).length :=
  (laws.answers_prefix request state).length_le

private theorem matcher_unread_settled (laws : matcher.CursorLaws)
    {request : GeneralScopedMatchMachine.Request} {state : matcher.State} {cursor : Nat}
    {answer : matcher.Answer} (reached : matcher.Reachable request state)
    (settled : matcher.complete state = true)
    (unavailable : (matcher.answers state)[cursor]? = none) :
    ¬ laws.Unread request state cursor answer := by
  rw [laws.complete reached settled]
  have consumed : (matcher.answers state).drop cursor = [] :=
    List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp unavailable)
  simp only [consumed, List.not_mem_nil, not_false_eq_true]

private theorem query_answers_grow (environment : Environment) (request : Query.Request)
    (state : Query.State environment request matcher) :
    state.answers.length ≤ (Query.tick environment request state).answers.length := by
  obtain ⟨suffix, same⟩ := Scheduler.tick_answers_prefix (Query.expand environment request) state
  change state.answers.length ≤
    (Scheduler.tick (Query.expand environment request) state).answers.length
  rw [same]
  simp

theorem query_covers (laws : matcher.CursorLaws) (represented : Represents matcher) {environment : Environment} {outer : Goal} {depth : Nat}
    {request : Query.Request} {state : Query.State environment request matcher} {cursor : Nat}
    {tail : Interpreted.Continuation matcher environment
      (.premise depth request.context (.relationQuery request.relation request.arguments) request.initial) outer}
    {wanted : Interpreted.Result matcher environment outer}
    (meaning : TaskAccepts laws (.query depth request state cursor tail) wanted) :
    ExpansionAccepts laws (expandQuery environment outer depth request state cursor tail) wanted := by
  obtain ⟨wellFormed, bounded, answer, unread, concludes⟩ := meaning
  unfold expandQuery
  split
  · rename_i seen found
    obtain same | remaining := (Query.unread_get laws environment request state cursor answer).mp unread
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
      exact False.elim (Query.unread_empty_of_settled laws environment request state cursor answer
        empty unavailable unread)
    · right
      refine ⟨_, List.mem_cons_self, Query.tick_wellFormed laws _ _ wellFormed, ?_, answer, ?_, concludes⟩
      · exact bounded.trans (query_answers_grow environment request state)
      · exact (Query.unread_tick_of_no_answer laws represented environment request state cursor answer
          wellFormed bounded unavailable).mpr unread

theorem rootMatch_covers (laws : matcher.CursorLaws) {environment : Environment} {outer : Goal}
    {frame : RootMatchFrame environment outer matcher} {wanted : Interpreted.Result matcher environment outer}
    (meaning : TaskAccepts laws (.rootMatch frame) wanted) :
    ExpansionAccepts laws (expandRootMatch environment outer frame) wanted := by
  obtain ⟨bounded, answer, unread, matched, typed, continued⟩ := meaning
  unfold expandRootMatch
  split
  · rename_i seen found
    change (matcher.answers frame.state)[frame.cursor]? = some seen at found
    unfold continueRootAnswer
    obtain same | remaining :=
      (laws.split (rootRequest frame) frame.state frame.cursor answer).mp unread
    · have equal : seen = answer := Option.some.inj (found.symm.trans same)
      subst seen
      have checked := checkTypedAssignment_complete typed
      simp only [checked, dite_true]
      right
      exact ⟨_, List.mem_cons_self, continued⟩
    · have newBound : frame.cursor + 1 ≤ (matcher.answers frame.state).length := by
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
      exact False.elim (matcher_unread_settled laws frame.reachable completed unavailable unread)
    · right
      refine ⟨_, List.mem_cons_self, ?_, answer, ?_, matched, typed, continued⟩
      · exact bounded.trans (matcher_answers_grow laws (rootRequest frame) frame.state)
      · exact (laws.tick frame.reachable bounded unavailable).mpr unread

theorem targetMatch_covers (laws : matcher.CursorLaws) {environment : Environment} {outer : Goal}
    {frame : TargetMatchFrame environment outer matcher} {wanted : Interpreted.Result matcher environment outer}
    (meaning : TaskAccepts laws (.targetMatch frame) wanted) :
    ExpansionAccepts laws (expandTargetMatch environment outer frame) wanted := by
  obtain ⟨bounded, answer, unread, matched, typed, continued⟩ := meaning
  unfold expandTargetMatch
  split
  · rename_i seen found
    change (matcher.answers frame.state)[frame.cursor]? = some seen at found
    obtain same | remaining :=
      (laws.split (targetRequest frame) frame.state frame.cursor answer).mp unread
    · have equal : seen = answer := Option.some.inj (found.symm.trans same)
      subst seen
      have checked := checkTypedAssignment_complete typed
      simp only [checked, dite_true]
      right
      exact ⟨_, List.mem_cons_self, continued⟩
    · have newBound : frame.cursor + 1 ≤ (matcher.answers frame.state).length := by
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
      exact False.elim (matcher_unread_settled laws frame.reachable completed unavailable unread)
    · right
      refine ⟨_, List.mem_cons_self, ?_, answer, ?_, matched, typed, continued⟩
      · exact bounded.trans (matcher_answers_grow laws (targetRequest frame) frame.state)
      · exact (laws.tick frame.reachable bounded unavailable).mpr unread

theorem expand_covers (laws : matcher.CursorLaws) (represented : Represents matcher) {environment : Environment} {goal : Goal}
    {task : Interpreted.Task matcher environment goal} {wanted : Interpreted.Result matcher environment goal}
    (meaning : TaskAccepts laws task wanted) :
    ExpansionAccepts laws (expand environment goal task) wanted := by
  cases task with
  | evaluate current tail => exact evaluate_covers laws represented meaning
  | deliver result tail => exact delivered_covers laws represented meaning
  | query depth request state cursor tail => exact query_covers laws represented meaning
  | rootMatch frame => exact rootMatch_covers laws meaning
  | targetMatch frame => exact targetMatch_covers laws meaning
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

theorem tick_covers (laws : matcher.CursorLaws) (represented : Represents matcher) {environment : Environment} {goal : Goal}
    {state : State environment goal matcher} {wanted : Interpreted.Result matcher environment goal}
    (meaning : StateAccepts laws state wanted) :
    StateAccepts laws (tick environment goal state) wanted := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, Scheduler.tick, agenda] using meaning
  | cons head rest =>
      unfold tick Scheduler.tick
      rw [agenda]
      rcases meaning with emitted | ⟨task, member, pending⟩
      · exact Or.inl (List.mem_append_left _ emitted)
      · rcases List.mem_cons.mp (agenda ▸ member) with same | later
        · subst task
          rcases expand_covers laws represented pending with emitted | ⟨child, childMember, childMeaning⟩
          · exact Or.inl (List.mem_append_right _ emitted)
          · exact Or.inr ⟨child, List.mem_append_left _ childMember, childMeaning⟩
        · exact Or.inr ⟨task, List.mem_append_right _ later, pending⟩

theorem run_covers (laws : matcher.CursorLaws) (represented : Represents matcher) {environment : Environment} {goal : Goal}
    (fuel : Nat) {state : State environment goal matcher} {wanted : Interpreted.Result matcher environment goal}
    (meaning : StateAccepts laws state wanted) :
    StateAccepts laws (run environment goal fuel state) wanted := by
  induction fuel generalizing state with
  | zero => exact meaning
  | succ fuel ih => exact ih (tick_covers laws represented meaning)


theorem answers_complete_of_drained (laws : matcher.CursorLaws) (represented : Represents matcher)
    (environment : Environment) (goal : Goal) (fuel : Nat)
    (wanted : Interpreted.Result matcher environment goal) (ordered : wanted.ordered = true)
    (drained : (run environment goal fuel (start environment goal matcher)).agenda = []) :
    wanted ∈ (run environment goal fuel (start environment goal matcher)).answers := by
  have initial : StateAccepts laws (start environment goal matcher) wanted :=
    .inr ⟨_, List.mem_cons_self, wanted, ordered, rfl⟩
  rcases run_covers laws represented fuel initial with emitted | ⟨task, member, _⟩
  · exact emitted
  · rw [drained] at member
    exact False.elim (List.not_mem_nil member)

#print axioms delivered_covers
#print axioms evaluate_covers
#print axioms query_covers
#print axioms rootMatch_covers
#print axioms targetMatch_covers
#print axioms expand_covers
#print axioms tick_covers
#print axioms run_covers
#print axioms answers_complete_of_drained

theorem finishWith_contains (cost : matcher.CursorCost) (laws : matcher.CursorLaws)
    (represented : Represents matcher) (environment : Environment) (goal : Goal)
    (wanted : Interpreted.Result matcher environment goal) (ordered : wanted.ordered = true) :
    wanted ∈ (finishWith cost environment goal).answers :=
  answers_complete_of_drained laws represented environment goal (treeStart cost environment goal).cost
    wanted ordered (finishWith_settled cost environment goal)

#print axioms finishWith_contains

/-- The established finite ordinary execution contains every bounded source answer. -/
theorem finish_contains (environment : Environment) (goal : Goal)
    (wanted : Result environment goal) (ordered : Interpreted.Result.ordered wanted = true) :
    wanted ∈ (finish environment goal).answers :=
  finishWith_contains MatchingExecution.ordinaryCursorCost MatchingExecution.ordinaryCursorLaws
    MatchingExecution.ordinary_answer_representation environment goal wanted ordered

#print axioms finish_contains

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled
