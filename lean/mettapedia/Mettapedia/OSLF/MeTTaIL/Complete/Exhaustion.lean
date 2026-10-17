import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledCoverage

/-!
# Depth exhaustion is the only way a scheduled search misses a derivation

`StructuralDescentScheduledCoverage` proves that a drained scheduled search at depth `d` holds
every derivation whose nesting fits in `d`. This module drops the depth bound from the
denotation of pending work. Every actual transition keeps each derivation, of any nesting, either
emitted, or denoted by a pending task, or else it records a `depthExhausted` obligation: the only
step that discards a branch is a root evaluated at depth zero.

- `finish_covers`: every derivation is in the drained search, or the search was cut by depth;
- `finish_contains_of_unexhausted`: a drained search with no `depthExhausted` obligation holds
  every derivation of its goal, at every nesting.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Exhaustion

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted
open StructuralDescent StructuralDescent.Scheduled

def Reaches {environment : Environment} {goal outer : Goal}
    (tail : Continuation environment goal outer) (result : Result environment goal)
    (wanted : Result environment outer) : Prop :=
  match tail with
  | .done _ => result = wanted
  | .nextPremise depth context premise premises initial tail =>
      match result with
      | .premise middle event head =>
          ∃ (final : Assignment) (events : List Event) (rest : PremisesHold environment context.next premises middle final events),
            Reaches tail (.premises final (event :: events) (.cons head rest)) wanted
  | .prepend depth _ _ _ _ _ event head tail =>
      match result with
      | .premises final events rest =>
          Reaches tail (.premises final (event :: events) (.cons head rest)) wanted
  | .quantifier depth context _ _ _ _ kind _ read tail =>
      match result with
      | .quantified final events held =>
          Reaches tail (.premise final
            (.quantified context.premiseIndex context.quantifierDepth kind events)
            (.quantified read held)) wanted
  | .element depth context parameter body index element elements initial localTyped tail =>
      match result with
      | .premise middle event head =>
          ∃ (final : Assignment) (events : List (Nat × Pattern × List Event)) (rest : QuantifiedElements environment context parameter body
              (index + 1) elements (restoreParameter parameter initial middle) final events),
            Reaches tail (.quantified final ((index, element, [event]) :: events)
              (.cons localTyped head rest)) wanted
  | .prependElement depth _ _ _ index element _ _ _ event localTyped head tail =>
      match result with
      | .quantified final events rest =>
          Reaches tail (.quantified final ((index, element, [event]) :: events)
            (.cons localTyped head rest)) wanted
  | .rootBody depth bound type _ index rule spec declared specified admitted sorted trace captured
      matched capturedTyped tail =>
      match result with
      | .premises completed events held =>
          ∃ (target : Pattern) (converted : reductWith? (ScopedReflectiveExecution.binderOperation
              environment.reflection rule) rule spec bound.length completed = some target)
              (typed : OpenPatternWellSorted environment.language environment.free bound type target),
            Reaches tail (.root trace captured completed events target
              (.fire declared specified admitted sorted matched capturedTyped held converted typed)) wanted
  | .searchedRoot depth _ _ _ index _ earlier tail =>
      match result with
      | .root trace captured completed events target held =>
          Reaches tail (.steps index trace captured completed events target earlier held) wanted
  | .stepped depth call tail =>
      match result with
      | .steps index trace captured completed events target _ held =>
          ∃ (final : Assignment) (targetTrace : List GeneralScopedMatchMachine.BagChoice)
              (matched : GeneralScopedMatchMachine.TracedMatches call.context.rule call.context.spec
                call.context.bound.length (call.context.site 1) [] call.binders.length
                call.initial call.targetSchema target targetTrace final)
              (typed : TypedAssignment environment call.context final),
            Reaches tail (.premise final
              (.child call.context.premiseIndex call.context.quantifierDepth index
                (call.binders ++ call.context.bound) call.source target trace targetTrace
                captured completed events)
              (call.conclude _ _ _ _ _ _ _ _ held matched typed)) wanted

/-- Pending evaluations denote actual independent semantic results, at any depth, together with
the meaning of the retained continuation. -/
def Evaluates {environment : Environment} {goal outer : Goal}
    (tail : Continuation environment goal outer) (wanted : Result environment outer) : Prop :=
  ∃ result : Result environment goal, Reaches tail result wanted


def Accepts {environment : Environment} {outer : Goal}
    (task : Task environment outer) (wanted : Result environment outer) : Prop :=
  match task with
  | .evaluate _ tail => Evaluates tail wanted
  | .deliver result tail => Reaches tail result wanted
  | .query _ request state cursor tail =>
      Query.StateWellFormed environment request state ∧ cursor ≤ state.answers.length ∧
      ∃ answer : Query.Answer environment request,
        Query.UnreadAccepts environment request state cursor answer ∧
        Reaches tail (.premise answer.assignment
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
          Evaluates (.rootBody frame.depth frame.bound frame.type frame.source frame.index frame.rule frame.spec
            frame.declared frame.specified frame.admitted frame.sorted answer.trace answer.assignment
            matched typed frame.tail) wanted
  | .targetMatch frame =>
      frame.cursor ≤ frame.state.answers.length ∧
      ∃ answer : GeneralScopedMatchMachine.Answer,
        GeneralScopedMatchMachine.MatcherUnread (targetRequest frame)
          frame.state frame.cursor answer ∧
        ∃ (matched : answer.Valid (targetRequest frame))
            (typed : TypedAssignment environment frame.call.context answer.assignment),
          Reaches frame.tail (.premise answer.assignment
            (.child frame.call.context.premiseIndex frame.call.context.quantifierDepth frame.index
              (frame.call.binders ++ frame.call.context.bound) frame.call.source frame.target
              frame.trace answer.trace frame.captured frame.completed frame.history)
            (frame.call.conclude _ _ _ _ _ _ _ _ frame.valid matched typed)) wanted
  | .scanChildren depth bound type source limit cursor tail =>
      ∃ (index : Nat) (earlier : index < limit), cursor ≤ index ∧
        Evaluates (.searchedRoot depth bound type source index limit earlier tail) wanted

/-- Some depth-exhausted branch was cut. -/
def Exhausted (unresolved : List Obligation) : Prop := ∃ index, Obligation.depthExhausted index ∈ unresolved

/-- The wanted result is emitted, or denoted by a pending task, or some branch was cut by depth. -/
def StateCovers {environment : Environment} {goal : Goal}
    (state : State environment goal) (wanted : Result environment goal) : Prop :=
  (wanted ∈ state.answers ∨ ∃ task ∈ state.agenda, Accepts task wanted) ∨ Exhausted state.unresolved

def Core {environment : Environment} {goal : Goal}
    (expansion : Scheduler.Expansion (Task environment goal) (Result environment goal) Obligation)
    (wanted : Result environment goal) : Prop :=
  wanted ∈ expansion.answers ∨ ∃ task ∈ expansion.tasks, Accepts task wanted

theorem delivered_covers {environment : Environment} {goal outer : Goal}
    {result : Result environment goal} {tail : Continuation environment goal outer}
    {wanted : Result environment outer} (meaning : Reaches tail result wanted) :
    Core (delivered environment outer result tail) wanted := by
  cases tail with
  | done =>
      simpa [Core, delivered, Reaches] using meaning.symm
  | nextPremise depth context premise premises initial tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, concludes⟩ := meaning
          simp only [Core, delivered, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, Accepts]
          exact ⟨.premises final events rest, concludes⟩
  | prepend depth context premise premises initial middle event head tail =>
      cases result with
      | premises final events rest =>
          change Core
            {tasks := [.deliver (.premises final (event :: events) (.cons head rest)) tail]} wanted
          simp only [Core, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, Accepts]
          change Reaches tail (.premises final (event :: events) (.cons head rest)) wanted at meaning
          exact meaning
  | quantifier depth context collection parameter body initial kind elements read tail =>
      cases result
      simpa only [Core, delivered.eq_4, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, Accepts, Reaches.eq_4] using meaning
  | element depth context parameter body index element elements initial localTyped tail =>
      cases result with
      | premise middle event head =>
          obtain ⟨final, events, rest, concludes⟩ := meaning
          change Core
            { tasks := [.evaluate
                (.quantified depth context parameter body (index + 1) elements
                  (restoreParameter parameter initial middle))
                (.prependElement depth context parameter body index element elements initial middle
                  event localTyped head tail)] } wanted
          simp only [Core, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, Accepts]
          exact ⟨.quantified final events rest, concludes⟩
  | prependElement depth context parameter body index element elements initial middle event localTyped head tail =>
      cases result with
      | quantified final events rest =>
          change Core
            {tasks := [.deliver (.quantified final ((index, element, [event]) :: events)
              (.cons localTyped head rest)) tail]} wanted
          simp only [Core, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, Accepts]
          change Reaches tail (.quantified final ((index, element, [event]) :: events)
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
            simpa [Core, checked, Accepts] using concludes
  | searchedRoot depth bound type source index limit earlier tail =>
      cases result
      simpa only [Core, delivered.eq_8, List.not_mem_nil, false_or,
        List.mem_singleton, exists_eq_left, Accepts, Reaches.eq_8] using meaning
  | stepped depth call tail =>
      cases result with
      | steps index trace captured completed events target earlier valid =>
          obtain ⟨final, targetTrace, matched, typed, concludes⟩ := meaning
          simp only [Core, delivered, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, Accepts]
          exact ⟨Nat.zero_le _, ⟨final, targetTrace⟩,
            (GeneralScopedMatchMachine.start_unread_iff _ _).mpr matched,
            matched, typed, concludes⟩

theorem evaluate_covers {environment : Environment} {goal outer : Goal}
    {tail : Continuation environment goal outer} {wanted : Result environment outer}
    (meaning : Evaluates tail wanted) :
    Core (evaluate environment outer goal tail) wanted ∨ Exhausted (evaluate environment outer goal tail).unresolved := by
  obtain ⟨result, concludes⟩ := meaning
  cases goal with
  | premises depth context premises initial =>
      refine Or.inl ?_
      cases result with
      | premises final events held =>
          cases held with
          | nil =>
              simpa only [Core, evaluate.eq_2, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, Accepts] using concludes
          | @cons context premise premises initial middle final event events head rest =>
              simp only [Core, evaluate.eq_3, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, Accepts]
              exact ⟨.premise middle event head, final, events, rest, concludes⟩
  | quantified depth context parameter body index elements initial =>
      refine Or.inl ?_
      cases result with
      | quantified final events held =>
          cases held with
          | nil => simpa only [Core, evaluate.eq_4, List.not_mem_nil, false_or,
                List.mem_singleton, exists_eq_left, Accepts] using concludes
          | @cons context parameter body index element elements initial middle final event events localTyped head rest =>
              have checked := checkTypedAssignment_complete localTyped
              simp only [Core, evaluate.eq_5, checked, dite_true, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, Accepts]
              exact ⟨.premise middle event head, final, events, rest, concludes⟩
  | premise depth context premise initial =>
      refine Or.inl ?_
      cases result with
      | premise final event held =>
          cases held with
          | @query context relation arguments initial final rowIndex origins query =>
              simp only [Core, evaluate.eq_1, evaluatePremise.eq_1, List.not_mem_nil,
                false_or, List.mem_singleton, exists_eq_left, Accepts]
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
                simpa [Core, checked, Accepts] using concludes
          | @step context source target actualSource actualTarget type initial final captured completed
              childIndex trace targetTrace history typed interpreted child matched finalTyped =>
              have earlier : childIndex < environment.language.rewrites.length := by
                cases child with
                | fire declared _ _ _ _ _ _ _ _ =>
                    exact (List.getElem?_eq_some_iff.mp declared).1
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
                  simp only [Core, List.not_mem_nil, false_or,
                    List.mem_singleton, exists_eq_left, Accepts]
                  exact ⟨.steps childIndex trace captured completed history actualTarget earlier child,
                    final, targetTrace, matched, finalTyped, concludes⟩
          | @scopedStep context step actualSource actualTarget initial final captured completed childIndex
              trace targetTrace history interpreted child matched finalTyped =>
              have earlier : childIndex < environment.language.rewrites.length := by
                cases child with
                | fire declared _ _ _ _ _ _ _ _ =>
                    exact (List.getElem?_eq_some_iff.mp declared).1
              rw [evaluate.eq_1]
              rw [evaluatePremise.eq_5]
              split
              · rename_i unavailable
                simp [interpreted] at unavailable
              · rename_i actual actualRead
                have same : actual = actualSource := Option.some.inj (actualRead.symm.trans interpreted)
                subst actual
                simp only [Core, List.not_mem_nil, false_or,
                  List.mem_singleton, exists_eq_left, Accepts]
                exact ⟨.steps childIndex trace captured completed history actualTarget earlier child,
                  final, targetTrace, matched, finalTyped, concludes⟩
          | @quantified context collection parameter body initial final kind elements history read quantified =>
              rw [evaluate.eq_1]
              rw [evaluatePremise.eq_3]
              split
              · rename_i unavailable
                simp [read] at unavailable
              · rename_i actualKind actualElements actualRead
                have same := Option.some.inj (actualRead.symm.trans read)
                cases same
                simp only [Core, List.not_mem_nil, false_or,
                  List.mem_singleton, exists_eq_left, Accepts]
                exact ⟨.quantified final history quantified, concludes⟩
  | root depth bound type source index =>
      cases depth with
      | zero =>
          exact Or.inr ⟨index, by simp [evaluate, evaluateRoot]⟩
      | succ depth =>
          refine Or.inl ?_
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
                      simp only [admitted, checked, dite_true, Core, List.not_mem_nil,
                        false_or, List.mem_singleton, exists_eq_left, Accepts]
                      refine ⟨Nat.zero_le _, ⟨captured, trace⟩,
                        (GeneralScopedMatchMachine.start_unread_iff _ _).mpr matched,
                        matched, capturedTyped, ?_⟩
                      exact ⟨.premises completed history premises, target, converted, targetTyped, concludes⟩
  | steps depth bound type source limit =>
      refine Or.inl ?_
      cases result with
      | steps index trace captured completed history target earlier held =>
          simp only [Core, evaluate.eq_7, List.not_mem_nil, false_or,
            List.mem_singleton, exists_eq_left, Accepts]
          refine ⟨index, earlier, Nat.zero_le _, ?_⟩
          exact ⟨.root trace captured completed history target held, concludes⟩


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
    (meaning : Accepts (.query depth request state cursor tail) wanted) :
    Core (expandQuery environment outer depth request state cursor tail) wanted := by
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
    (meaning : Accepts (.rootMatch frame) wanted) :
    Core (expandRootMatch environment outer frame) wanted := by
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
    (meaning : Accepts (.targetMatch frame) wanted) :
    Core (expandTargetMatch environment outer frame) wanted := by
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
    (meaning : Accepts task wanted) :
    Core (expand environment goal task) wanted ∨ Exhausted (expand environment goal task).unresolved := by
  cases task with
  | evaluate current tail => exact evaluate_covers meaning
  | deliver result tail => exact Or.inl (delivered_covers meaning)
  | query depth request state cursor tail => exact Or.inl (query_covers meaning)
  | rootMatch frame => exact Or.inl (rootMatch_covers meaning)
  | targetMatch frame => exact Or.inl (targetMatch_covers meaning)
  | scanChildren depth bound type source limit cursor tail =>
      refine Or.inl ?_
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
    (meaning : StateCovers state wanted) :
    StateCovers (tick environment goal state) wanted := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, Scheduler.tick, agenda] using meaning
  | cons head rest =>
      unfold tick Scheduler.tick
      rw [agenda]
      rcases meaning with (emitted | ⟨task, member, pending⟩) | ⟨index, found⟩
      · exact Or.inl (Or.inl (List.mem_append_left _ emitted))
      · rcases List.mem_cons.mp (agenda ▸ member) with same | later
        · subst task
          rcases expand_covers pending with (emitted | ⟨child, childMember, childMeaning⟩) | ⟨index, found⟩
          · exact Or.inl (Or.inl (List.mem_append_right _ emitted))
          · exact Or.inl (Or.inr ⟨child, List.mem_append_left _ childMember, childMeaning⟩)
          · exact Or.inr ⟨index, List.mem_append_right _ found⟩
        · exact Or.inl (Or.inr ⟨task, List.mem_append_right _ later, pending⟩)
      · exact Or.inr ⟨index, List.mem_append_left _ found⟩

theorem run_covers {environment : Environment} {goal : Goal}
    (fuel : Nat) {state : State environment goal} {wanted : Result environment goal}
    (meaning : StateCovers state wanted) :
    StateCovers (run environment goal fuel state) wanted := by
  induction fuel generalizing state with
  | zero => exact meaning
  | succ fuel ih => exact ih (tick_covers meaning)

/-- **Every derivation is found, or depth cut a branch.** -/
theorem finish_covers (environment : Environment) (goal : Goal) (wanted : Result environment goal) :
    wanted ∈ (finish environment goal).answers ∨ Exhausted (finish environment goal).unresolved := by
  have initial : StateCovers (start environment goal) wanted :=
    Or.inl (Or.inr ⟨_, List.mem_cons_self, wanted, rfl⟩)
  have final := run_covers (treeStart environment goal).cost initial
  rcases final with (emitted | ⟨task, member, _⟩) | exhausted
  · exact Or.inl emitted
  · have empty : (run environment goal (treeStart environment goal).cost (start environment goal)).agenda = [] :=
      finish_settled environment goal
    rw [empty] at member
    exact False.elim (List.not_mem_nil member)
  · exact Or.inr exhausted

/-- **An uncut drained search is exact.** With no `depthExhausted` obligation, the drained search
holds every derivation of its goal, at every nesting. -/
theorem finish_contains_of_unexhausted (environment : Environment) (goal : Goal)
    (uncut : ∀ index, Obligation.depthExhausted index ∉ (finish environment goal).unresolved)
    (wanted : Result environment goal) : wanted ∈ (finish environment goal).answers := by
  rcases finish_covers environment goal wanted with found | ⟨index, cut⟩
  · exact found
  · exact absurd cut (uncut index)

end Mettapedia.OSLF.MeTTaIL.Complete.Exhaustion
