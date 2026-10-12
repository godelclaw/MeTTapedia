import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTermination
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCursor

/-!
# Independent coverage of suspended relation queries

Pending rows denote actual provider positions. Argument frames denote the
remaining independent traced argument judgment; matcher frames denote unread
structural answers or pending structural work. Cursor bounds are earned from
the actual transitions, rather than assumed as a completion certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

abbrev CertifiedAnswer := Answer

theorem answer_eq_of_readout {environment : Environment} {request : Request}
    {first second : Answer environment request}
    (row : first.rowIndex = second.rowIndex)
    (assignment : first.assignment = second.assignment)
    (origins : first.origins = second.origins) : first = second := by
  cases first
  cases second
  cases row
  cases assignment
  cases origins
  rfl

def ArgumentsAccepts (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request) (wanted : CertifiedAnswer environment request) : Prop :=
  wanted.rowIndex = frame.rowIndex ∧ ∃ traces,
    TracedArgumentsHold request.context frame.index frame.assignment frame.schemas frame.values
      frame.modes wanted.assignment traces ∧
    TypedAssignment environment request.context wanted.assignment ∧
    wanted.origins = frame.origins ++ traces

def MatcherAccepts (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request) (wanted : CertifiedAnswer environment request) : Prop :=
  frame.cursor ≤ frame.state.answers.length ∧ wanted.rowIndex = frame.rowIndex ∧
    ∃ matched traces, GeneralScopedMatchMachine.MatcherUnread frame.query frame.state frame.cursor matched ∧
      TracedArgumentsHold request.context (frame.argumentIndex + 1) matched.assignment frame.schemas
        frame.values frame.modes wanted.assignment traces ∧
      TypedAssignment environment request.context wanted.assignment ∧
      wanted.origins = (frame.origins ++ [(frame.argumentIndex, matched.trace)]) ++ traces

def TaskAccepts (environment : Environment) (request : Request) :
    Task environment request → CertifiedAnswer environment request → Prop
  | .start, wanted => TracedQuery environment request.context request.relation request.arguments
      request.initial wanted.rowIndex wanted.assignment wanted.origins
  | .rows frame, wanted => frame.cursor ≤ wanted.rowIndex ∧
      TracedQuery environment request.context request.relation request.arguments
        request.initial wanted.rowIndex wanted.assignment wanted.origins
  | .arguments frame, wanted => ArgumentsAccepts environment request frame wanted
  | .matcher frame, wanted => MatcherAccepts environment request frame wanted

def TaskWellFormed (environment : Environment) (request : Request) : Task environment request → Prop
  | .matcher frame => frame.cursor ≤ frame.state.answers.length
  | _ => True

def StateWellFormed (environment : Environment) (request : Request)
    (state : State environment request) : Prop :=
  ∀ task ∈ state.agenda, TaskWellFormed environment request task

def ExpansionAccepts (environment : Environment) (request : Request)
    (expansion : Scheduler.Expansion (Task environment request) (Answer environment request) Obligation)
    (wanted : CertifiedAnswer environment request) : Prop :=
  wanted ∈ expansion.answers ∨ ∃ task ∈ expansion.tasks, TaskAccepts environment request task wanted

def StateAccepts (environment : Environment) (request : Request)
    (state : State environment request) (wanted : CertifiedAnswer environment request) : Prop :=
  wanted ∈ state.answers ∨ ∃ task ∈ state.agenda, TaskAccepts environment request task wanted

def UnreadAccepts (environment : Environment) (request : Request)
    (state : State environment request) (cursor : Nat) (wanted : CertifiedAnswer environment request) : Prop :=
  wanted ∈ state.answers.drop cursor ∨ ∃ task ∈ state.agenda, TaskAccepts environment request task wanted

abbrev QueryUnread := UnreadAccepts

private theorem matcher_length_mono (query : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) :
    state.answers.length ≤ (GeneralScopedMatchMachine.tick query state).answers.length := by
  cases agenda : state.agenda with
  | nil => simp [GeneralScopedMatchMachine.tick, agenda]
  | cons work agenda =>
      cases tasks : work.tasks <;> simp [GeneralScopedMatchMachine.tick, agenda, tasks]

theorem expand_wellFormed (environment : Environment) (request : Request)
    (task branch : Task environment request) (wellFormed : TaskWellFormed environment request task)
    (member : branch ∈ (expand environment request task).tasks) :
    TaskWellFormed environment request branch := by
  cases task with
  | start =>
      simp only [expand] at member
      split at member
      · simp at member
      · simp only [List.mem_singleton] at member
        subst branch
        trivial
  | rows frame =>
      simp only [expand] at member
      split at member
      · simp at member
      · split at member
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with same | same <;> subst branch <;> trivial
        · simp only [List.mem_singleton] at member
          subst branch
          trivial
  | arguments frame =>
      simp only [expand] at member
      unfold expandArguments at member
      split at member
      · split at member <;> simp at member
      · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
        cases mode with
        | input =>
            dsimp only at member
            split at member
            · simp at member
            · split at member
              · simp only [List.mem_singleton] at member
                subst branch
                trivial
              · simp at member
        | output =>
            dsimp only at member
            simp only [List.mem_singleton] at member
            subst branch
            exact Nat.zero_le _
      · simp at member
  | matcher frame =>
      simp only [expand] at member
      unfold expandMatcher at member
      split at member
      · rename_i matched found
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with same | same <;> subst branch
        · trivial
        · exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp found).1
      · split at member
        · simp at member
        · simp only [List.mem_singleton] at member
          subst branch
          exact wellFormed.trans (matcher_length_mono frame.query frame.state)

theorem start_wellFormed (environment : Environment) (request : Request) :
    StateWellFormed environment request (start environment request) := by
  intro task member
  simp only [start, List.mem_singleton] at member
  subst task
  trivial

theorem tick_wellFormed (environment : Environment) (request : Request)
    {state : State environment request} (wellFormed : StateWellFormed environment request state) :
    StateWellFormed environment request (tick environment request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, Scheduler.tick, agenda] using wellFormed
  | cons task tasks =>
      intro branch member
      simp only [tick, Scheduler.tick, agenda, List.mem_append] at member
      rcases member with generated | later
      · exact expand_wellFormed environment request task branch
          (wellFormed task (by rw [agenda]; exact List.mem_cons_self)) generated
      · exact wellFormed branch (by rw [agenda]; exact List.mem_cons_of_mem _ later)

theorem run_wellFormed (environment : Environment) (request : Request) (fuel : Nat)
    {state : State environment request} (wellFormed : StateWellFormed environment request state) :
    StateWellFormed environment request (run environment request fuel state) := by
  induction fuel generalizing state with
  | zero => exact wellFormed
  | succ fuel ih => exact ih (tick_wellFormed environment request wellFormed)


private theorem traced_nil_readout {context : Context} {index : Nat} {initial final : Assignment}
    {traces : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedArgumentsHold context index initial [] [] [] final traces) :
    final = initial ∧ traces = [] := by cases held; exact ⟨rfl, rfl⟩

private theorem traced_shapes {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    {traces : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedArgumentsHold context index initial schemas values modes final traces) :
    (schemas = [] ∧ values = [] ∧ modes = []) ∨
      ∃ schema tailSchemas value tailValues mode tailModes,
        schemas = schema :: tailSchemas ∧ values = value :: tailValues ∧ modes = mode :: tailModes := by
  cases held with
  | nil => exact .inl ⟨rfl, rfl, rfl⟩
  | input _ _ => exact .inr ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩
  | output _ _ => exact .inr ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩

theorem expandArguments_accepts_iff (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request) (wanted : CertifiedAnswer environment request) :
    ExpansionAccepts environment request (expandArguments environment request frame) wanted ↔
      ArgumentsAccepts environment request frame wanted := by
  unfold expandArguments
  split
  · rename_i schemasFound valuesFound modesFound
    split
    · rename_i checked
      simp only [ExpansionAccepts, List.mem_singleton, List.not_mem_nil, false_and,
        exists_false, or_false]
      constructor
      · intro same
        subst wanted
        exact ⟨rfl, [], by simpa only [schemasFound, valuesFound, modesFound] using
            (show TracedArgumentsHold request.context frame.index frame.assignment [] [] [] frame.assignment [] from .nil),
          checkTypedAssignment_sound checked, by simp⟩
      · rintro ⟨rowSame, traces, held, typed, originsSame⟩
        rw [schemasFound, valuesFound, modesFound] at held
        obtain ⟨assignmentSame, tracesSame⟩ := traced_nil_readout held
        subst traces
        apply answer_eq_of_readout rowSame assignmentSame
        simpa using originsSame
    · rename_i unchecked
      simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
      rintro ⟨_, traces, held, typed, _⟩
      rw [schemasFound, valuesFound, modesFound] at held
      have same := (traced_nil_readout held).1
      rw [same] at typed
      exact unchecked (checkTypedAssignment_complete typed)
  · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
    cases mode with
    | input =>
        dsimp only
        split
        · rename_i unavailable
          simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
          rintro ⟨_, traces, held, _, _⟩
          rw [schemasFound, valuesFound, modesFound] at held
          cases held with
          | input interpreted _ => simp [unavailable] at interpreted
        · rename_i actual interpreted
          split
          · rename_i same
            simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
            constructor
            · rintro ⟨branch, rfl, rowSame, traces, tail, typed, originsSame⟩
              refine ⟨rowSame, (frame.index, []) :: traces, ?_, typed, ?_⟩
              · rw [schemasFound, valuesFound, modesFound]
                exact .input (by simpa only [beq_iff_eq.mp same] using interpreted) tail
              · simpa only [List.append_assoc, List.singleton_append] using originsSame
            · rintro ⟨rowSame, traces, held, typed, originsSame⟩
              rw [schemasFound, valuesFound, modesFound] at held
              cases held with
              | input interpreted tail =>
                  refine ⟨_, rfl, rowSame, _, tail, typed, ?_⟩
                  simpa only [List.append_assoc, List.singleton_append] using originsSame
          · rename_i different
            simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
            rintro ⟨_, traces, held, _, _⟩
            rw [schemasFound, valuesFound, modesFound] at held
            cases held with
            | input matched _ =>
                have equal := Option.some.inj (interpreted.symm.trans matched)
                exact different (beq_iff_eq.mpr equal)
    | output =>
        dsimp only
        simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
        constructor
        · rintro ⟨branch, rfl, bounded, rowSame, matched, traces, unread, tail, typed, originsSame⟩
          refine ⟨rowSame, (frame.index, matched.trace) :: traces, ?_, typed, ?_⟩
          · rw [schemasFound, valuesFound, modesFound]
            exact .output ((GeneralScopedMatchMachine.start_unread_iff _ _).mp unread) tail
          · simpa only [List.append_assoc, List.singleton_append] using originsSame
        · rintro ⟨rowSame, traces, held, typed, originsSame⟩
          rw [schemasFound, valuesFound, modesFound] at held
          cases held with
          | @output index initial middle final schema value schemas values modes trace traces matched tail =>
              refine ⟨_, rfl, Nat.zero_le _, rowSame, ⟨middle, trace⟩, traces, ?_, tail, typed, ?_⟩
              · exact (GeneralScopedMatchMachine.start_unread_iff _ _).mpr matched
              · simpa only [List.append_assoc, List.singleton_append] using originsSame
  · rename_i nilMismatch consMismatch
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
    rintro ⟨_, traces, held, _, _⟩
    rcases traced_shapes held with ⟨schemas, values, modes⟩ | ⟨schema, schemas, value, values, mode, modes, hs, hv, hm⟩
    · exact nilMismatch schemas values modes
    · exact consMismatch schema schemas value values mode modes hs hv hm


theorem expandMatcher_accepts_iff (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request) (wanted : CertifiedAnswer environment request)
    (wellFormed : frame.cursor ≤ frame.state.answers.length) :
    ExpansionAccepts environment request (expandMatcher environment request frame) wanted ↔
      MatcherAccepts environment request frame wanted := by
  unfold expandMatcher
  split
  · rename_i answer found
    simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_cons, or_false]
    have remainingBound : frame.cursor + 1 ≤ frame.state.answers.length :=
      Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp found).1
    constructor
    · rintro ⟨branch, (same | same), accepted⟩
      · subst branch
        obtain ⟨rowSame, traces, tail, typed, originsSame⟩ := accepted
        exact ⟨wellFormed, rowSame, answer, traces,
          (GeneralScopedMatchMachine.unread_cursor_split _ _ _ _).mpr (.inl found), tail, typed, originsSame⟩
      · subst branch
        obtain ⟨_, rowSame, matched, traces, unread, tail, typed, originsSame⟩ := accepted
        exact ⟨wellFormed, rowSame, matched, traces,
          (GeneralScopedMatchMachine.unread_cursor_split _ _ _ _).mpr (.inr unread), tail, typed, originsSame⟩
    · rintro ⟨_, rowSame, matched, traces, unread, tail, typed, originsSame⟩
      rcases (GeneralScopedMatchMachine.unread_cursor_split _ _ _ _).mp unread with head | later
      · have same := Option.some.inj (found.symm.trans head)
        subst matched
        exact ⟨_, .inl rfl, rowSame, traces, tail, typed, originsSame⟩
      · exact ⟨_, .inr rfl, remainingBound, rowSame, matched, traces, later, tail, typed, originsSame⟩
  · rename_i unavailable
    split
    · rename_i completed
      simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
      rintro ⟨bounded, _, matched, _, unread, _, _, _⟩
      have atEnd : frame.cursor = frame.state.answers.length := by
        have beyond := List.getElem?_eq_none_iff.mp unavailable
        omega
      rw [atEnd, GeneralScopedMatchMachine.unread_at_end_iff] at unread
      obtain ⟨work, member, _⟩ := unread
      have idle := (GeneralScopedMatchMachine.complete_eq_true_iff _).mp completed
      simp only [idle, List.not_mem_nil] at member
    · simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, _, rowSame, matched, traces, unread, tail, typed, originsSame⟩
        exact ⟨wellFormed, rowSame, matched, traces,
          (GeneralScopedMatchMachine.unread_tick_of_no_answer _ _ _ _ wellFormed unavailable).mp unread,
          tail, typed, originsSame⟩
      · rintro ⟨_, rowSame, matched, traces, unread, tail, typed, originsSame⟩
        exact ⟨_, rfl, wellFormed.trans (matcher_length_mono _ _), rowSame, matched, traces,
          (GeneralScopedMatchMachine.unread_tick_of_no_answer _ _ _ _ wellFormed unavailable).mpr unread,
          tail, typed, originsSame⟩


private theorem valid_details (environment : Environment) (request : Request)
    (signature : Signature)
    (found : signature? environment.provider request.relation request.arguments.length = some signature)
    (wanted : CertifiedAnswer environment request) :
    ∃ row, environment.provider.rows[wanted.rowIndex]? = some row ∧
      RowTyped environment.language environment.free request.context.bound signature row ∧
      TracedArgumentsHold request.context 0 request.initial request.arguments row.values signature.modes
        wanted.assignment wanted.origins ∧ TypedAssignment environment request.context wanted.assignment := by
  cases wanted.valid with
  | @row row actual final origins selected declared typed held finalTyped =>
      have same := Option.some.inj (declared.symm.trans found)
      subst actual
      exact ⟨row, selected, typed, held, finalTyped⟩

theorem expandRows_accepts_iff (environment : Environment) (request : Request)
    (frame : RowsFrame environment request) (wanted : CertifiedAnswer environment request) :
    ExpansionAccepts environment request (expand environment request (.rows frame)) wanted ↔
      TaskAccepts environment request (.rows frame) wanted := by
  simp only [expand]
  split
  · rename_i unavailable
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff,
      TaskAccepts]
    rintro ⟨bounded, _⟩
    obtain ⟨row, selected, _, _, _⟩ := valid_details environment request _ frame.signatureFound wanted
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have beyond := List.getElem?_eq_none_iff.mp unavailable
    omega
  · rename_i row found
    split
    · simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_cons, or_false]
      constructor
      · rintro ⟨branch, (same | same), accepted⟩
        · subst branch
          obtain ⟨rowSame, _, _, _, _⟩ := accepted
          exact ⟨by simp only [rowSame]; exact Nat.le_refl _, wanted.valid⟩
        · subst branch
          exact ⟨Nat.le_trans (Nat.le_succ _) accepted.1, accepted.2⟩
      · rintro ⟨bounded, _⟩
        by_cases current : wanted.rowIndex = frame.cursor
        · obtain ⟨actual, selected, _, held, typed⟩ :=
            valid_details environment request _ frame.signatureFound wanted
          rw [current] at selected
          have same := Option.some.inj (found.symm.trans selected)
          subst actual
          exact ⟨_, .inl rfl, current, wanted.origins, held, typed, by simp⟩
        · exact ⟨_, .inr rfl, by dsimp only; omega, wanted.valid⟩
    · rename_i unchecked
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, bounded, valid⟩
        exact ⟨Nat.le_trans (Nat.le_succ _) bounded, valid⟩
      · rintro ⟨bounded, valid⟩
        have later : frame.cursor + 1 ≤ wanted.rowIndex := by
          by_cases current : wanted.rowIndex = frame.cursor
          · obtain ⟨actual, selected, typed, _, _⟩ :=
              valid_details environment request _ frame.signatureFound wanted
            rw [current] at selected
            have same := Option.some.inj (found.symm.trans selected)
            subst actual
            exact False.elim (unchecked (checkRow_complete typed))
          · omega
        exact ⟨_, rfl, later, valid⟩

theorem expandStart_accepts_iff (environment : Environment) (request : Request)
    (wanted : CertifiedAnswer environment request) :
    ExpansionAccepts environment request (expand environment request .start) wanted ↔
      TaskAccepts environment request .start wanted := by
  simp only [expand]
  split
  · rename_i unavailable
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff,
      TaskAccepts]
    intro valid
    cases valid with
    | row _ declared _ _ _ => simp [unavailable] at declared
  · simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
    constructor
    · rintro ⟨branch, rfl, _, valid⟩
      exact valid
    · intro valid
      exact ⟨_, rfl, Nat.zero_le _, valid⟩

theorem expand_accepts_iff (environment : Environment) (request : Request)
    (task : Task environment request) (wanted : CertifiedAnswer environment request)
    (wellFormed : TaskWellFormed environment request task) :
    ExpansionAccepts environment request (expand environment request task) wanted ↔
      TaskAccepts environment request task wanted := by
  cases task with
  | start => exact expandStart_accepts_iff _ _ _
  | rows frame => exact expandRows_accepts_iff _ _ _ _
  | arguments frame => exact expandArguments_accepts_iff _ _ _ _
  | matcher frame => exact expandMatcher_accepts_iff _ _ _ _ wellFormed


theorem tick_accepts_iff (environment : Environment) (request : Request)
    (state : State environment request) (wanted : CertifiedAnswer environment request)
    (wellFormed : StateWellFormed environment request state) :
    StateAccepts environment request (tick environment request state) wanted ↔
      StateAccepts environment request state wanted := by
  cases agenda : state.agenda with
  | nil => simp only [tick, Scheduler.tick, agenda]
  | cons task tasks =>
      have taskWF := wellFormed task (by rw [agenda]; exact List.mem_cons_self)
      simp only [StateAccepts, tick, Scheduler.tick, agenda, List.mem_append, List.mem_cons]
      constructor
      · rintro ((old | emitted) | ⟨branch, (generated | later), accepted⟩)
        · exact .inl old
        · exact .inr ⟨task, .inl rfl,
            (expand_accepts_iff environment request task wanted taskWF).mp (.inl emitted)⟩
        · exact .inr ⟨task, .inl rfl,
            (expand_accepts_iff environment request task wanted taskWF).mp (.inr ⟨branch, generated, accepted⟩)⟩
        · exact .inr ⟨branch, .inr later, accepted⟩
      · rintro (old | ⟨branch, (same | later), accepted⟩)
        · exact .inl (.inl old)
        · subst branch
          rcases (expand_accepts_iff environment request task wanted taskWF).mpr accepted with
            emitted | ⟨generated, member, accepted⟩
          · exact .inl (.inr emitted)
          · exact .inr ⟨generated, .inl member, accepted⟩
        · exact .inr ⟨branch, .inr later, accepted⟩

theorem start_accepts_iff (environment : Environment) (request : Request)
    (wanted : CertifiedAnswer environment request) :
    StateAccepts environment request (start environment request) wanted ↔
      TracedQuery environment request.context request.relation request.arguments request.initial
        wanted.rowIndex wanted.assignment wanted.origins := by
  simp only [StateAccepts, start, List.not_mem_nil, false_or, List.mem_singleton,
    exists_eq_left, TaskAccepts]

theorem run_accepts_iff (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request) (wanted : CertifiedAnswer environment request)
    (wellFormed : StateWellFormed environment request state) :
    StateAccepts environment request (run environment request fuel state) wanted ↔
      StateAccepts environment request state wanted := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      exact (ih (tick environment request state) (tick_wellFormed _ _ wellFormed)).trans
        (tick_accepts_iff _ _ _ _ wellFormed)

theorem state_accepts_iff (environment : Environment) (request : Request) (fuel : Nat)
    (wanted : CertifiedAnswer environment request) :
    StateAccepts environment request (run environment request fuel (start environment request)) wanted ↔
      TracedQuery environment request.context request.relation request.arguments request.initial
        wanted.rowIndex wanted.assignment wanted.origins :=
  (run_accepts_iff _ _ _ _ _ (start_wellFormed _ _)).trans (start_accepts_iff _ _ _)

theorem unread_get (environment : Environment) (request : Request)
    (state : State environment request) (cursor : Nat) (wanted : CertifiedAnswer environment request) :
    UnreadAccepts environment request state cursor wanted ↔
      state.answers[cursor]? = some wanted ∨ UnreadAccepts environment request state (cursor + 1) wanted := by
  unfold UnreadAccepts
  rw [GeneralScopedMatchMachine.mem_drop_cursor_iff]
  exact or_assoc

theorem unread_start_of_valid (environment : Environment) (request : Request)
    (wanted : CertifiedAnswer environment request) :
    UnreadAccepts environment request (start environment request) 0 wanted :=
  (start_accepts_iff _ _ _).mpr wanted.valid

theorem unread_empty_of_settled (environment : Environment) (request : Request)
    (state : State environment request) (cursor : Nat) (wanted : CertifiedAnswer environment request)
    (settled : state.agenda = []) (unavailable : state.answers[cursor]? = none) :
    ¬ UnreadAccepts environment request state cursor wanted := by
  have consumed : state.answers.drop cursor = [] :=
    List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp unavailable)
  simp only [UnreadAccepts, consumed, settled, List.not_mem_nil, false_and, exists_false, or_self, not_false_eq_true]

theorem unread_tick_of_no_answer (environment : Environment) (request : Request)
    (state : State environment request) (cursor : Nat) (wanted : CertifiedAnswer environment request)
    (wellFormed : StateWellFormed environment request state)
    (bounded : cursor ≤ state.answers.length) (unavailable : state.answers[cursor]? = none) :
    UnreadAccepts environment request (tick environment request state) cursor wanted ↔
      UnreadAccepts environment request state cursor wanted := by
  have atEnd : cursor = state.answers.length := by
    have beyond := List.getElem?_eq_none_iff.mp unavailable
    omega
  subst cursor
  cases agenda : state.agenda with
  | nil => simp only [tick, Scheduler.tick, agenda]
  | cons task tasks =>
      have taskWF := wellFormed task (by rw [agenda]; exact List.mem_cons_self)
      simp only [UnreadAccepts, tick, Scheduler.tick, agenda]
      rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
      simp only [List.nil_append, List.not_mem_nil, false_or,
        List.mem_append, List.mem_cons]
      constructor
      · rintro (emitted | ⟨branch, (generated | later), accepted⟩)
        · exact ⟨task, .inl rfl,
            (expand_accepts_iff environment request task wanted taskWF).mp (.inl emitted)⟩
        · exact ⟨task, .inl rfl,
            (expand_accepts_iff environment request task wanted taskWF).mp (.inr ⟨branch, generated, accepted⟩)⟩
        · exact ⟨branch, .inr later, accepted⟩
      · rintro ⟨branch, (same | later), accepted⟩
        · subst branch
          rcases (expand_accepts_iff environment request task wanted taskWF).mpr accepted with
            emitted | ⟨generated, member, accepted⟩
          · exact .inl emitted
          · exact .inr ⟨generated, .inl member, accepted⟩
        · exact .inr ⟨branch, .inr later, accepted⟩

theorem answers_complete (environment : Environment) (request : Request) (fuel : Nat)
    (wanted : CertifiedAnswer environment request)
    (settled : (run environment request fuel (start environment request)).agenda = []) :
    wanted ∈ (run environment request fuel (start environment request)).answers := by
  rcases (state_accepts_iff environment request fuel wanted).mpr wanted.valid with emitted | pending
  · exact emitted
  · obtain ⟨task, member, _⟩ := pending
    simp only [settled, List.not_mem_nil] at member

theorem completedEventually (environment : Environment) (request : Request) :
    ∃ fuel, (run environment request fuel (start environment request)).agenda = [] ∧
      ∀ wanted : CertifiedAnswer environment request,
        wanted ∈ (run environment request fuel (start environment request)).answers := by
  obtain ⟨fuel, settled⟩ := finiteDrain environment request (start environment request)
  exact ⟨fuel, settled, fun wanted => answers_complete environment request fuel wanted settled⟩

theorem traced_query_eventually (environment : Environment) (request : Request)
    {rowIndex : Nat} {assignment : Assignment} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment request.context request.relation request.arguments request.initial
      rowIndex assignment origins) :
    ∃ fuel, (run environment request fuel (start environment request)).agenda = [] ∧
      ∃ answer ∈ (run environment request fuel (start environment request)).answers,
        answer.rowIndex = rowIndex ∧ answer.assignment = assignment ∧ answer.origins = origins := by
  obtain ⟨fuel, settled, exhaustive⟩ := completedEventually environment request
  exact ⟨fuel, settled, ⟨rowIndex, assignment, origins, held⟩,
    exhaustive ⟨rowIndex, assignment, origins, held⟩, rfl, rfl, rfl⟩

#print axioms expand_accepts_iff
#print axioms unread_tick_of_no_answer
#print axioms traced_query_eventually

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching
open ConditionalEquationExecution
open GeneralScopedMatchMachine

theorem removed_parameter_free_within (footprint : List String) (parameter : String)
    (assignment : Assignment) (stored : assignmentFreeWithin footprint assignment) :
    assignmentFreeWithin footprint (removeParameter parameter assignment) := by
  have subset : ∀ entry ∈ removeParameter parameter assignment, entry ∈ assignment := by
    clear stored
    induction assignment with
    | nil => intro entry member; cases member
    | cons entry entries ih =>
        rcases entry with ⟨key, value⟩
        simp only [removeParameter]
        split
        · intro entry member
          exact List.mem_cons_of_mem _ (ih entry member)
        · intro entry member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih entry member)
  intro entry member name occurs
  exact stored entry (subset entry member) name occurs

theorem bound_parameter_free_within (footprint : List String) (parameter : String)
    (value : ContextualValue) (assignment : Assignment)
    (stored : assignmentFreeWithin footprint assignment)
    (inserted : ∀ name ∈ value.body.freeFvarNames, name ∈ footprint) :
    assignmentFreeWithin footprint (bindParameter parameter value assignment) := by
  intro entry member name occurs
  rcases List.mem_cons.mp member with rfl | member
  · exact inserted name occurs
  · exact removed_parameter_free_within footprint parameter assignment stored entry member name occurs

theorem restored_parameter_free_within (footprint : List String) (parameter : String)
    (initial final : Assignment) (before : assignmentFreeWithin footprint initial)
    (after : assignmentFreeWithin footprint final) :
    assignmentFreeWithin footprint (restoreParameter parameter initial final) := by
  unfold restoreParameter
  cases found : lookup initial parameter with
  | none => exact removed_parameter_free_within footprint parameter final after
  | some value =>
      intro entry member name occurs
      rcases List.mem_cons.mp member with rfl | member
      · exact before _ (ConditionalEquationExecution.lookup_assignment_member initial parameter value found) name occurs
      · exact removed_parameter_free_within footprint parameter final after entry member name occurs

theorem finite_collection_free_within (footprint : List String) (ambient : Nat)
    (assignment : Assignment) (name : String) (kind : CollType) (elements : List Pattern)
    (stored : assignmentFreeWithin footprint assignment)
    (read : finiteCollection? ambient assignment name = some (kind, elements)) :
    patternsFreeWithin footprint elements := by
  unfold finiteCollection? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  rcases read with ⟨value, found, pattern, instantiated, concrete⟩
  have covered := instantiate_value_free_within footprint value ambient 0 [] pattern
    (stored _ (ConditionalEquationExecution.lookup_assignment_member assignment name value found))
    (by intro p member; cases member) instantiated
  unfold concreteCollection? at concrete
  split at concrete <;> cases concrete
  intro element member free occurs
  apply covered free
  simp only [Pattern.freeFvarNames, Option.toList_none, List.append_nil]
  exact List.mem_flatMap.mpr ⟨element, member, occurs⟩

def taskFreeWithin (footprint : List String) {environment : Environment}
    {request : Query.Request} : Query.Task environment request → Prop
  | .start => assignmentFreeWithin footprint request.initial
  | .rows _ => assignmentFreeWithin footprint request.initial
  | .arguments frame => assignmentFreeWithin footprint frame.assignment ∧
      patternsFreeWithin footprint frame.values
  | .matcher frame => assignmentFreeWithin footprint frame.query.initial ∧
      (∀ name ∈ frame.query.target.freeFvarNames, name ∈ footprint) ∧
      patternsFreeWithin footprint frame.values

def stateFreeWithin (footprint : List String) (environment : Environment)
    (request : Query.Request) (state : Query.State environment request) : Prop :=
  (∀ task ∈ state.agenda, taskFreeWithin footprint task) ∧
  (∀ answer ∈ state.answers, assignmentFreeWithin footprint answer.assignment)

theorem arguments_expansion_free_within (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request)
    (stored : assignmentFreeWithin footprint frame.assignment)
    (values : patternsFreeWithin footprint frame.values) :
    (∀ task ∈ (Query.expandArguments environment request frame).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Query.expandArguments environment request frame).answers,
      assignmentFreeWithin footprint answer.assignment) := by
  unfold Query.expandArguments
  split
  · split
    · constructor
      · intro task member; cases member
      · intro answer member
        rcases List.mem_singleton.mp member with rfl
        exact stored
    · constructor <;> intro item member <;> cases member
  · rename_i schema schemas value tailValues mode modes schemasFound valuesFound modesFound
    split
    ·
        split
        · constructor <;> intro item member <;> cases member
        · split
          · constructor
            · intro task member
              rcases List.mem_singleton.mp member with rfl
              constructor
              · exact stored
              · intro pattern member name occurs
                apply values pattern _ name occurs
                rw [valuesFound]
                exact List.mem_cons_of_mem _ member
            · intro answer member; cases member
          · constructor <;> intro item member <;> cases member
    ·
        constructor
        · intro task member
          rcases List.mem_singleton.mp member with rfl
          refine ⟨stored, ?_, ?_⟩
          · exact values value (by rw [valuesFound]; simp)
          · intro pattern member name occurs
            apply values pattern _ name occurs
            rw [valuesFound]
            exact List.mem_cons_of_mem _ member
        · intro answer member; cases member
  · constructor <;> intro item member <;> cases member

theorem matcher_expansion_free_within (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (frame : Query.MatcherFrame environment request)
    (stored : assignmentFreeWithin footprint frame.query.initial)
    (target : ∀ name ∈ frame.query.target.freeFvarNames, name ∈ footprint)
    (values : patternsFreeWithin footprint frame.values) :
    (∀ task ∈ (Query.expandMatcher environment request frame).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Query.expandMatcher environment request frame).answers,
      assignmentFreeWithin footprint answer.assignment) := by
  unfold Query.expandMatcher
  split
  · rename_i answer found
    have captured := matcher_answer_free_within frame.query frame.state frame.reachable answer
      (List.mem_of_getElem? found) footprint stored target
    constructor
    · intro task member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨captured, values⟩
      · exact ⟨stored, target, values⟩
    · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨stored, target, values⟩
      · intro answer member; cases member

theorem expansion_free_within (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (task : Query.Task environment request) (covered : taskFreeWithin footprint task) :
    (∀ next ∈ (Query.expand environment request task).tasks, taskFreeWithin footprint next) ∧
    (∀ answer ∈ (Query.expand environment request task).answers,
      assignmentFreeWithin footprint answer.assignment) := by
  cases task with
  | start =>
      simp only [Query.expand]
      split
      · constructor <;> intro item member <;> cases member
      · constructor
        · intro next member
          rcases List.mem_singleton.mp member with rfl
          exact covered
        · intro answer member; cases member
  | rows frame =>
      simp only [Query.expand]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i row found
        split
        · constructor
          · intro next member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact ⟨covered, provider row (List.mem_of_getElem? found)⟩
            · exact covered
          · intro answer member; cases member
        · constructor
          · intro next member
            rcases List.mem_singleton.mp member with rfl
            exact covered
          · intro answer member; cases member
  | arguments frame => exact arguments_expansion_free_within footprint environment request frame covered.1 covered.2
  | matcher frame => exact matcher_expansion_free_within footprint environment request frame covered.1 covered.2.1 covered.2.2
theorem run_free_within (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (fuel : Nat) (state : Query.State environment request)
    (covered : stateFreeWithin footprint environment request state) :
    stateFreeWithin footprint environment request (Query.run environment request fuel state) :=
  Scheduler.run_preserves (taskFreeWithin footprint) (fun (answer : Query.Answer environment request) => assignmentFreeWithin footprint answer.assignment)
    (Query.expand environment request) (expansion_free_within footprint environment request provider)
    fuel state covered

theorem start_free_within (footprint : List String) (environment : Environment)
    (request : Query.Request) (stored : assignmentFreeWithin footprint request.initial) :
    stateFreeWithin footprint environment request (Query.start environment request) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact stored
  · intro answer member; cases member

theorem run_from_start_free_within (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (stored : assignmentFreeWithin footprint request.initial) (fuel : Nat) :
    stateFreeWithin footprint environment request
      (Query.run environment request fuel (Query.start environment request)) :=
  run_free_within footprint environment request provider fuel _
    (start_free_within footprint environment request stored)
theorem tick_free_within (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (state : Query.State environment request) (covered : stateFreeWithin footprint environment request state) :
    stateFreeWithin footprint environment request (Query.tick environment request state) :=
  Scheduler.tick_preserves (taskFreeWithin footprint)
    (fun (answer : Query.Answer environment request) => assignmentFreeWithin footprint answer.assignment)
    (Query.expand environment request) (expansion_free_within footprint environment request provider) state covered
theorem run_answer_free_within (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (stored : assignmentFreeWithin footprint request.initial) (fuel : Nat)
    (answer : Query.Answer environment request)
    (member : answer ∈ (Query.run environment request fuel (Query.start environment request)).answers) :
    assignmentFreeWithin footprint answer.assignment :=
  (run_from_start_free_within footprint environment request provider stored fuel).2 answer member
theorem run_finite_free_within (environment : Environment) (request : Query.Request) (fuel : Nat) :
    stateFreeWithin (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider)
      environment request (Query.run environment request fuel (Query.start environment request)) := by
  apply run_from_start_free_within
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · exact assignment_coverage_mono _ _ request.initial
      (fun name member => List.mem_append_left _ member) (assignment_covered_by_own_names request.initial)

theorem prefix_assignment_check_snapshot (environment : Environment) (request : Query.Request)
    (fuel : Nat) (frame : Query.ArgumentsFrame environment request)
    (member : Query.Task.arguments frame ∈
      (Query.run environment request fuel (Query.start environment request)).agenda) :
    ConditionalEquationExecution.checkAssignment environment.language
      (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList
        (environment.free.entriesOn (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider)))
      request.context.bound request.context.rule request.context.spec frame.assignment =
      checkTypedAssignment environment request.context frame.assignment := by
  unfold checkTypedAssignment
  apply ConditionalEquationExecution.checkAssignment_snapshot
  apply assignment_free_names_covered
  exact ((run_finite_free_within environment request fuel).1 _ member).1

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.removed_parameter_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.bound_parameter_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.restored_parameter_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.finite_collection_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.taskFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.stateFreeWithin
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.arguments_expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.matcher_expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.expansion_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.run_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.start_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.run_from_start_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.tick_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.run_answer_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.run_finite_free_within
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.prefix_assignment_check_snapshot

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
