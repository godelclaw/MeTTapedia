import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTermination
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCursor

/-!
# Independent coverage of suspended relation queries

Pending rows denote actual provider positions. Argument frames retain the
selected independent matching interpretation; matcher frames retain its unread
cursor contract. Represented semantic witnesses justify output matching.
Cursor bounds follow from the transitions. A drained query contains every
interpreted answer. The ordinary service additionally supplies finite drainage
and free-name preservation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {matcher : MatchingExecution}

abbrev CertifiedAnswer (environment : Environment) (request : Request)
    (matcher : MatchingExecution := .ordinary) := Answer environment request matcher

theorem answer_eq_of_readout {environment : Environment} {request : Request}
    {first second : Answer environment request matcher}
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
    (frame : ArgumentsFrame environment request matcher) (wanted : CertifiedAnswer environment request matcher) : Prop :=
  wanted.rowIndex = frame.rowIndex ∧ ∃ traces,
    Interpreted.TracedArgumentsHold matcher.meaning request.context frame.index frame.assignment frame.schemas frame.values
      frame.modes wanted.assignment traces ∧
    TypedAssignment environment request.context wanted.assignment ∧
    wanted.origins = frame.origins ++ traces

def MatcherAccepts (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request matcher) (wanted : CertifiedAnswer environment request matcher) : Prop :=
  frame.cursor ≤ (matcher.answers frame.state).length ∧ wanted.rowIndex = frame.rowIndex ∧
    ∃ matched traces, laws.Unread frame.query frame.state frame.cursor matched ∧
      Interpreted.TracedArgumentsHold matcher.meaning request.context (frame.argumentIndex + 1) (matcher.assignment matched) frame.schemas
        frame.values frame.modes wanted.assignment traces ∧
      TypedAssignment environment request.context wanted.assignment ∧
      wanted.origins = (frame.origins ++ [(frame.argumentIndex, (matcher.trace matched))]) ++ traces

/-- Native-row alternatives retain the exact acquired table and occurrence
index; a different provider call cannot supply their pending answers. -/
def DynamicRowsAccepts (environment : Environment) (request : Request)
    (signature : Signature) (rows : List (List Pattern)) (cursor : Nat)
    (wanted : CertifiedAnswer environment request matcher) : Prop :=
  ∃ nativeIndex values, cursor ≤ nativeIndex ∧
    wanted.rowIndex = environment.provider.rows.length + nativeIndex ∧
    rows[nativeIndex]? = some values ∧
    RowTyped environment.language environment.free request.context.bound signature
      ⟨request.relation, values⟩ ∧
    Interpreted.TracedArgumentsHold matcher.meaning request.context 0 request.initial request.arguments values signature.modes
      wanted.assignment wanted.origins ∧ TypedAssignment environment request.context wanted.assignment

/-- Pending input resolution denotes the original remaining input judgment,
then the acquired provider table, then its exact native-row alternatives. -/
def DynamicInputsAccepts (environment : Environment) (request : Request)
    (frame : DynamicInputsFrame environment request)
    (wanted : CertifiedAnswer environment request matcher) : Prop :=
  ∃ values rows,
    DynamicInputs request.context frame.index request.initial frame.schemas frame.modes values ∧
    environment.dynamic.Source request.relation (frame.resolvedRev.reverse ++ values) rows ∧
    DynamicRowsAccepts environment request frame.signature rows 0 wanted

def TaskAccepts (laws : matcher.CursorLaws) (environment : Environment) (request : Request) :
    Task environment request matcher → CertifiedAnswer environment request matcher → Prop
  | .start, wanted => Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments
      request.initial wanted.rowIndex wanted.assignment wanted.origins
  | .rows frame, wanted => frame.cursor ≤ wanted.rowIndex ∧
      wanted.rowIndex < environment.provider.rows.length ∧ Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments
        request.initial wanted.rowIndex wanted.assignment wanted.origins
  | .dynamicInputs frame, wanted => DynamicInputsAccepts environment request frame wanted
  | .dynamicRows frame, wanted => DynamicRowsAccepts environment request frame.signature frame.rows frame.cursor wanted
  | .arguments frame, wanted => ArgumentsAccepts environment request frame wanted
  | .matcher frame, wanted => MatcherAccepts laws environment request frame wanted

def TaskWellFormed (environment : Environment) (request : Request) : Task environment request matcher → Prop
  | .matcher frame => frame.cursor ≤ (matcher.answers frame.state).length
  | _ => True

def StateWellFormed (environment : Environment) (request : Request)
    (state : State environment request matcher) : Prop :=
  ∀ task ∈ state.agenda, TaskWellFormed environment request task

def ExpansionAccepts (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (expansion : Scheduler.Expansion (Task environment request matcher) (Answer environment request matcher) Obligation)
    (wanted : CertifiedAnswer environment request matcher) : Prop :=
  wanted ∈ expansion.answers ∨ ∃ task ∈ expansion.tasks, TaskAccepts laws environment request task wanted

def StateAccepts (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (state : State environment request matcher) (wanted : CertifiedAnswer environment request matcher) : Prop :=
  wanted ∈ state.answers ∨ ∃ task ∈ state.agenda, TaskAccepts laws environment request task wanted

def UnreadAccepts (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (state : State environment request matcher) (cursor : Nat) (wanted : CertifiedAnswer environment request matcher) : Prop :=
  wanted ∈ state.answers.drop cursor ∨ ∃ task ∈ state.agenda, TaskAccepts laws environment request task wanted

abbrev QueryUnread (laws : matcher.CursorLaws) := UnreadAccepts laws

private theorem matcher_length_mono (laws : matcher.CursorLaws)
    (query : GeneralScopedMatchMachine.Request) (state : matcher.State) :
    (matcher.answers state).length ≤ (matcher.answers (matcher.tick query state)).length :=
  (laws.answers_prefix query state).length_le

theorem expand_wellFormed (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (task branch : Task environment request matcher) (wellFormed : TaskWellFormed environment request task)
    (member : branch ∈ (expand environment request task).tasks) :
    TaskWellFormed environment request branch := by
  cases task with
  | start =>
      simp only [expand] at member
      split at member
      · simp at member
      · split at member
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with same | same <;> subst branch <;> trivial
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
  | dynamicInputs frame =>
      simp only [expand] at member
      unfold expandDynamicInputs at member
      split at member
      · split at member
        · simp at member
        · simp only [List.mem_singleton] at member
          subst branch
          trivial
      · split at member
        · simp at member
        · simp only [List.mem_singleton] at member
          subst branch
          trivial
      · simp only [List.mem_singleton] at member
        subst branch
        trivial
      · simp at member
  | dynamicRows frame =>
      simp only [expand] at member
      unfold expandDynamicRows at member
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
          exact wellFormed.trans (matcher_length_mono laws frame.query frame.state)

theorem start_wellFormed (environment : Environment) (request : Request) :
    StateWellFormed environment request (start environment request matcher) := by
  intro task member
  simp only [start, List.mem_singleton] at member
  subst task
  trivial

theorem tick_wellFormed (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    {state : State environment request matcher} (wellFormed : StateWellFormed environment request state) :
    StateWellFormed environment request (tick environment request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, Scheduler.tick, agenda] using wellFormed
  | cons task tasks =>
      intro branch member
      simp only [tick, Scheduler.tick, agenda, List.mem_append] at member
      rcases member with generated | later
      · exact expand_wellFormed laws environment request task branch
          (wellFormed task (by rw [agenda]; exact List.mem_cons_self)) generated
      · exact wellFormed branch (by rw [agenda]; exact List.mem_cons_of_mem _ later)

theorem run_wellFormed (laws : matcher.CursorLaws) (environment : Environment) (request : Request) (fuel : Nat)
    {state : State environment request matcher} (wellFormed : StateWellFormed environment request state) :
    StateWellFormed environment request (run environment request fuel state) := by
  induction fuel generalizing state with
  | zero => exact wellFormed
  | succ fuel ih => exact ih (tick_wellFormed laws environment request wellFormed)


private theorem traced_nil_readout {context : Context} {index : Nat} {initial final : Assignment}
    {traces : List (Nat × List matcher.Choice)}
    (held : Interpreted.TracedArgumentsHold matcher.meaning context index initial [] [] [] final traces) :
    final = initial ∧ traces = [] := by cases held; exact ⟨rfl, rfl⟩

private theorem traced_shapes {context : Context} {index : Nat} {initial final : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    {traces : List (Nat × List matcher.Choice)}
    (held : Interpreted.TracedArgumentsHold matcher.meaning context index initial schemas values modes final traces) :
    (schemas = [] ∧ values = [] ∧ modes = []) ∨
      ∃ schema tailSchemas value tailValues mode tailModes,
        schemas = schema :: tailSchemas ∧ values = value :: tailValues ∧ modes = mode :: tailModes := by
  cases held with
  | nil => exact .inl ⟨rfl, rfl, rfl⟩
  | input _ _ => exact .inr ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩
  | output _ _ => exact .inr ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩

theorem expandArguments_accepts_iff (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request matcher) (wanted : CertifiedAnswer environment request matcher) :
    ExpansionAccepts laws environment request (expandArguments environment request frame) wanted ↔
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
            (show Interpreted.TracedArgumentsHold matcher.meaning request.context frame.index frame.assignment [] [] [] frame.assignment [] from .nil),
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
          | input heldInput _ =>
              obtain ⟨actual, read, _⟩ := matcher.input_complete heldInput
              rw [unavailable] at read
              cases read
        · rename_i actual interpreted
          split
          · rename_i same
            simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
            constructor
            · rintro ⟨branch, rfl, rowSame, traces, tail, typed, originsSame⟩
              refine ⟨rowSame, (frame.index, []) :: traces, ?_, typed, ?_⟩
              · rw [schemasFound, valuesFound, modesFound]
                exact .input (matcher.input_sound interpreted same) tail
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
            | input heldInput _ =>
                obtain ⟨expected, read, accepted⟩ := matcher.input_complete heldInput
                have equal := Option.some.inj (interpreted.symm.trans read)
                cases equal
                exact different accepted
    | output =>
        dsimp only
        simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
        constructor
        · rintro ⟨branch, rfl, bounded, rowSame, matched, traces, unread, tail, typed, originsSame⟩
          refine ⟨rowSame, (frame.index, (matcher.trace matched)) :: traces, ?_, typed, ?_⟩
          · rw [schemasFound, valuesFound, modesFound]
            exact .output ((laws.start _ _).mp unread) tail
          · simpa only [List.append_assoc, List.singleton_append] using originsSame
        · rintro ⟨rowSame, traces, held, typed, originsSame⟩
          rw [schemasFound, valuesFound, modesFound] at held
          cases held with
          | @output index initial middle final schema value schemas values modes trace traces matched tail =>
              obtain ⟨answer, answerTrace, answerAssignment⟩ := represented
                (matchingRequest request frame.index frame.assignment schema value) trace middle matched
              refine ⟨_, rfl, Nat.zero_le _, rowSame, answer, traces, ?_, ?_, typed, ?_⟩
              · apply (laws.start _ _).mpr
                simpa only [matchingRequest, answerTrace, answerAssignment] using matched
              · simpa only [answerAssignment] using tail
              · simpa only [answerTrace, List.append_assoc, List.singleton_append] using originsSame
  · rename_i nilMismatch consMismatch
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
    rintro ⟨_, traces, held, _, _⟩
    rcases traced_shapes held with ⟨schemas, values, modes⟩ | ⟨schema, schemas, value, values, mode, modes, hs, hv, hm⟩
    · exact nilMismatch schemas values modes
    · exact consMismatch schema schemas value values mode modes hs hv hm


theorem expandMatcher_accepts_iff (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (frame : MatcherFrame environment request matcher) (wanted : CertifiedAnswer environment request matcher)
    (wellFormed : frame.cursor ≤ (matcher.answers frame.state).length) :
    ExpansionAccepts laws environment request (expandMatcher environment request frame) wanted ↔
      MatcherAccepts laws environment request frame wanted := by
  unfold expandMatcher
  split
  · rename_i answer found
    simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_cons, or_false]
    have remainingBound : frame.cursor + 1 ≤ (matcher.answers frame.state).length :=
      Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp found).1
    constructor
    · rintro ⟨branch, (same | same), accepted⟩
      · subst branch
        obtain ⟨rowSame, traces, tail, typed, originsSame⟩ := accepted
        exact ⟨wellFormed, rowSame, answer, traces,
          (laws.split _ _ _ _).mpr (.inl found), tail, typed, originsSame⟩
      · subst branch
        obtain ⟨_, rowSame, matched, traces, unread, tail, typed, originsSame⟩ := accepted
        exact ⟨wellFormed, rowSame, matched, traces,
          (laws.split _ _ _ _).mpr (.inr unread), tail, typed, originsSame⟩
    · rintro ⟨_, rowSame, matched, traces, unread, tail, typed, originsSame⟩
      rcases (laws.split _ _ _ _).mp unread with head | later
      · have same := Option.some.inj (found.symm.trans head)
        subst matched
        exact ⟨_, .inl rfl, rowSame, traces, tail, typed, originsSame⟩
      · exact ⟨_, .inr rfl, remainingBound, rowSame, matched, traces, later, tail, typed, originsSame⟩
  · rename_i unavailable
    change (matcher.answers frame.state)[frame.cursor]? = none at unavailable
    split
    · rename_i completed
      simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
      rintro ⟨bounded, _, matched, _, unread, _, _, _⟩
      have atEnd : frame.cursor = (matcher.answers frame.state).length := by
        have beyond := List.getElem?_eq_none_iff.mp unavailable
        omega
      rw [atEnd] at unread
      exact laws.no_unread_after_complete frame.reachable completed matched unread
    · simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, _, rowSame, matched, traces, unread, tail, typed, originsSame⟩
        exact ⟨wellFormed, rowSame, matched, traces,
          (laws.tick frame.reachable wellFormed unavailable).mp unread,
          tail, typed, originsSame⟩
      · rintro ⟨_, rowSame, matched, traces, unread, tail, typed, originsSame⟩
        exact ⟨_, rfl, wellFormed.trans (matcher_length_mono laws _ _), rowSame, matched, traces,
          (laws.tick frame.reachable wellFormed unavailable).mpr unread,
          tail, typed, originsSame⟩


private theorem valid_details (environment : Environment) (request : Request)
    (signature : Signature)
    (found : signature? environment.provider request.relation request.arguments.length = some signature)
    (wanted : CertifiedAnswer environment request matcher)
    (finite : wanted.rowIndex < environment.provider.rows.length) :
    ∃ row, environment.provider.rows[wanted.rowIndex]? = some row ∧
      RowTyped environment.language environment.free request.context.bound signature row ∧
      Interpreted.TracedArgumentsHold matcher.meaning request.context 0 request.initial request.arguments row.values signature.modes
        wanted.assignment wanted.origins ∧ TypedAssignment environment request.context wanted.assignment := by
  rcases wanted with ⟨wantedIndex, wantedAssignment, wantedOrigins, valid⟩
  dsimp only at finite ⊢
  cases valid with
  | @row rowIndex row actual final origins selected declared typed held finalTyped =>
      have same := Option.some.inj (declared.symm.trans found)
      subst actual
      exact ⟨row, selected, typed, held, finalTyped⟩
  | dynamicRow _ _ _ _ _ _ _ _ => omega

theorem expandRows_accepts_iff (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (frame : RowsFrame environment request) (wanted : CertifiedAnswer environment request matcher) :
    ExpansionAccepts laws environment request (expand environment request (.rows frame)) wanted ↔
      TaskAccepts laws environment request (.rows frame) wanted := by
  simp only [expand]
  split
  · rename_i unavailable
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff,
      TaskAccepts]
    rintro ⟨bounded, finite, _⟩
    obtain ⟨row, selected, _, _, _⟩ := valid_details environment request _ frame.signatureFound wanted finite
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
          exact ⟨by simp only [rowSame]; exact Nat.le_refl _,
            by rw [rowSame]; exact (List.getElem?_eq_some_iff.mp found).1, wanted.valid⟩
        · subst branch
          exact ⟨Nat.le_trans (Nat.le_succ _) accepted.1, accepted.2⟩
      · rintro ⟨bounded, finite, _⟩
        by_cases current : wanted.rowIndex = frame.cursor
        · obtain ⟨actual, selected, _, held, typed⟩ :=
            valid_details environment request _ frame.signatureFound wanted finite
          rw [current] at selected
          have same := Option.some.inj (found.symm.trans selected)
          subst actual
          exact ⟨_, .inl rfl, current, wanted.origins, held, typed, by simp⟩
        · exact ⟨_, .inr rfl, by dsimp only; omega, finite, wanted.valid⟩
    · rename_i unchecked
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, bounded, finite, valid⟩
        exact ⟨Nat.le_trans (Nat.le_succ _) bounded, finite, valid⟩
      · rintro ⟨bounded, finite, valid⟩
        have later : frame.cursor + 1 ≤ wanted.rowIndex := by
          by_cases current : wanted.rowIndex = frame.cursor
          · obtain ⟨actual, selected, typed, _, _⟩ :=
              valid_details environment request _ frame.signatureFound wanted finite
            rw [current] at selected
            have same := Option.some.inj (found.symm.trans selected)
            subst actual
            exact False.elim (unchecked (checkRow_complete typed))
          · omega
        exact ⟨_, rfl, later, finite, valid⟩

private theorem dynamic_input_shapes {context : Context} {index : Nat} {initial : Assignment}
    {schemas values : List Pattern} {modes : List RelationArgMode}
    (held : DynamicInputs context index initial schemas modes values) :
    (schemas = [] ∧ modes = []) ∨
      (∃ schema tail tailModes, schemas = schema :: tail ∧ modes = .input :: tailModes) ∨
      (∃ schema tail tailModes, schemas = schema :: tail ∧ modes = .output :: tailModes) := by
  cases held with
  | nil => exact .inl ⟨rfl, rfl⟩
  | input _ _ => exact .inr (.inl ⟨_, _, _, rfl, rfl⟩)
  | output _ => exact .inr (.inr ⟨_, _, _, rfl, rfl⟩)

theorem expandDynamicInputs_accepts_iff (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (frame : DynamicInputsFrame environment request) (wanted : CertifiedAnswer environment request matcher) :
    ExpansionAccepts laws environment request (expandDynamicInputs environment request frame matcher) wanted ↔
      DynamicInputsAccepts environment request frame wanted := by
  unfold expandDynamicInputs
  split
  · rename_i schemasFound modesFound
    split
    · rename_i unavailable
      simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
      rintro ⟨values, rows, held, source, _⟩
      rw [schemasFound, modesFound] at held
      cases held
      have computed := (environment.dynamic.rows_exact _ _ _).mpr
        (by simpa only [List.append_nil] using source)
      rw [unavailable] at computed
      cases computed
    · rename_i rows computed
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, accepted⟩
        refine ⟨[], rows, ?_, ?_, accepted⟩
        · rw [schemasFound, modesFound]
          exact .nil
        · simpa only [List.append_nil] using (environment.dynamic.rows_exact _ _ _).mp computed
      · rintro ⟨values, actual, held, source, accepted⟩
        rw [schemasFound, modesFound] at held
        cases held
        have source' : environment.dynamic.Source request.relation frame.resolvedRev.reverse actual :=
          by simpa only [List.append_nil] using source
        have same := environment.dynamic.source_unique ((environment.dynamic.rows_exact _ _ _).mp computed) source'
        subst actual
        exact ⟨_, rfl, accepted⟩
  · rename_i schema schemas modes schemasFound modesFound
    split
    · rename_i unavailable
      simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
      rintro ⟨values, rows, held, _, _⟩
      rw [schemasFound, modesFound] at held
      cases held with
      | input interpreted _ => rw [unavailable] at interpreted; cases interpreted
    · rename_i value interpreted
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, values, rows, tail, source, accepted⟩
        refine ⟨value :: values, rows, ?_, ?_, accepted⟩
        · rw [schemasFound, modesFound]
          exact .input interpreted tail
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using source
      · rintro ⟨values, rows, held, source, accepted⟩
        rw [schemasFound, modesFound] at held
        cases held with
        | input matched tail =>
            have same := Option.some.inj (interpreted.symm.trans matched)
            cases same
            refine ⟨_, rfl, _, rows, tail, ?_, accepted⟩
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using source
  · rename_i schema schemas modes schemasFound modesFound
    simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
    constructor
    · rintro ⟨branch, rfl, values, rows, tail, source, accepted⟩
      refine ⟨schema :: values, rows, ?_, ?_, accepted⟩
      · rw [schemasFound, modesFound]
        exact .output tail
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using source
    · rintro ⟨values, rows, held, source, accepted⟩
      rw [schemasFound, modesFound] at held
      cases held with
      | output tail =>
          refine ⟨_, rfl, _, rows, tail, ?_, accepted⟩
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using source
  · rename_i nilMismatch inputMismatch outputMismatch
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
    rintro ⟨values, rows, held, _, _⟩
    rcases dynamic_input_shapes held with ⟨schemas, modes⟩ | ⟨schema, schemas, modes, hs, hm⟩ | ⟨schema, schemas, modes, hs, hm⟩
    · exact nilMismatch schemas modes
    · exact inputMismatch schema schemas modes hs hm
    · exact outputMismatch schema schemas modes hs hm

theorem expandDynamicRows_accepts_iff (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) (wanted : CertifiedAnswer environment request matcher) :
    ExpansionAccepts laws environment request (expandDynamicRows environment request frame matcher) wanted ↔
      DynamicRowsAccepts environment request frame.signature frame.rows frame.cursor wanted := by
  unfold expandDynamicRows
  split
  · rename_i unavailable
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
    rintro ⟨nativeIndex, values, bounded, _, selected, _, _, _⟩
    have within := (List.getElem?_eq_some_iff.mp selected).1
    have beyond := List.getElem?_eq_none_iff.mp unavailable
    omega
  · rename_i values selected
    split
    · rename_i checked
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_cons, or_false]
      constructor
      · rintro ⟨branch, (same | same), accepted⟩
        · subst branch
          obtain ⟨rowSame, traces, held, typed, originsSame⟩ := accepted
          refine ⟨frame.cursor, values, Nat.le_refl _, rowSame, selected, checkRow_sound checked, ?_, typed⟩
          simpa only [List.nil_append] using originsSame ▸ held
        · subst branch
          obtain ⟨nativeIndex, actual, bounded, rowSame, found, typed, held, finalTyped⟩ := accepted
          exact ⟨nativeIndex, actual, Nat.le_trans (Nat.le_succ _) bounded,
            rowSame, found, typed, held, finalTyped⟩
      · rintro ⟨nativeIndex, actual, bounded, rowSame, found, typed, held, finalTyped⟩
        by_cases current : nativeIndex = frame.cursor
        · subst nativeIndex
          have same := Option.some.inj (selected.symm.trans found)
          subst actual
          exact ⟨_, .inl rfl, rowSame, wanted.origins, held, finalTyped, by simp⟩
        · exact ⟨_, .inr rfl, nativeIndex, actual, by dsimp only; omega,
            rowSame, found, typed, held, finalTyped⟩
    · rename_i unchecked
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · rintro ⟨branch, rfl, nativeIndex, actual, bounded, rowSame, found, typed, held, finalTyped⟩
        exact ⟨nativeIndex, actual, Nat.le_trans (Nat.le_succ _) bounded,
          rowSame, found, typed, held, finalTyped⟩
      · rintro ⟨nativeIndex, actual, bounded, rowSame, found, typed, held, finalTyped⟩
        have later : frame.cursor + 1 ≤ nativeIndex := by
          by_cases current : nativeIndex = frame.cursor
          · subst nativeIndex
            have same := Option.some.inj (selected.symm.trans found)
            subst actual
            exact False.elim (unchecked (checkRow_complete typed))
          · omega
        exact ⟨_, rfl, nativeIndex, actual, later, rowSame, found, typed, held, finalTyped⟩

theorem expandStart_accepts_iff (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (wanted : CertifiedAnswer environment request matcher) :
    ExpansionAccepts laws environment request (expand (matcher := matcher) environment request .start) wanted ↔
      TaskAccepts laws environment request .start wanted := by
  rcases wanted with ⟨rowIndex, final, origins, valid⟩
  simp only [expand]
  split
  · rename_i unavailable
    simp only [ExpansionAccepts, List.not_mem_nil, false_and, exists_false, or_self, false_iff]
    intro _
    cases valid with
    | row _ declared _ _ _ => simp [unavailable] at declared
    | dynamicRow _ declared _ _ _ _ _ _ => simp [unavailable] at declared
  · rename_i signature found
    split
    · rename_i registered
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_cons, or_false]
      constructor
      · intro _
        exact valid
      · intro _
        cases valid with
        | @row rowIndex row actual final origins selected declared typed held finalTyped =>
            have same := Option.some.inj (declared.symm.trans found)
            subst actual
            exact ⟨_, .inl rfl, Nat.zero_le _, (List.getElem?_eq_some_iff.mp selected).1,
              .row selected found typed held finalTyped⟩
        | @dynamicRow nativeIndex actual final resolved rows values origins enabled declared inputs source selected typed held finalTyped =>
            have same := Option.some.inj (declared.symm.trans found)
            subst actual
            refine ⟨_, .inr rfl, resolved, rows, ?_, ?_, nativeIndex, values,
              Nat.zero_le _, rfl, selected, typed, held, finalTyped⟩
            · simpa only using inputs
            · simpa only [List.reverse_nil, List.nil_append] using source
    · rename_i unregistered
      simp only [ExpansionAccepts, List.not_mem_nil, false_or, List.mem_singleton]
      constructor
      · intro _
        exact valid
      · intro _
        cases valid with
        | @row rowIndex row actual final origins selected declared typed held finalTyped =>
            have same := Option.some.inj (declared.symm.trans found)
            subst actual
            exact ⟨_, rfl, Nat.zero_le _, (List.getElem?_eq_some_iff.mp selected).1,
              .row selected found typed held finalTyped⟩
        | dynamicRow enabled _ _ _ _ _ _ _ => exact False.elim (unregistered enabled)

theorem expand_accepts_iff (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request)
    (task : Task environment request matcher) (wanted : CertifiedAnswer environment request matcher)
    (wellFormed : TaskWellFormed environment request task) :
    ExpansionAccepts laws environment request (expand environment request task) wanted ↔
      TaskAccepts laws environment request task wanted := by
  cases task with
  | start => exact expandStart_accepts_iff laws _ _ _
  | rows frame => exact expandRows_accepts_iff laws _ _ _ _
  | dynamicInputs frame => exact expandDynamicInputs_accepts_iff laws _ _ _ _
  | dynamicRows frame => exact expandDynamicRows_accepts_iff laws _ _ _ _
  | arguments frame => exact expandArguments_accepts_iff laws represented _ _ _ _
  | matcher frame => exact expandMatcher_accepts_iff laws _ _ _ _ wellFormed


theorem tick_accepts_iff (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request)
    (state : State environment request matcher) (wanted : CertifiedAnswer environment request matcher)
    (wellFormed : StateWellFormed environment request state) :
    StateAccepts laws environment request (tick environment request state) wanted ↔
      StateAccepts laws environment request state wanted := by
  cases agenda : state.agenda with
  | nil => simp only [tick, Scheduler.tick, agenda]
  | cons task tasks =>
      have taskWF := wellFormed task (by rw [agenda]; exact List.mem_cons_self)
      simp only [StateAccepts, tick, Scheduler.tick, agenda, List.mem_append, List.mem_cons]
      constructor
      · rintro ((old | emitted) | ⟨branch, (generated | later), accepted⟩)
        · exact .inl old
        · exact .inr ⟨task, .inl rfl,
            (expand_accepts_iff laws represented environment request task wanted taskWF).mp (.inl emitted)⟩
        · exact .inr ⟨task, .inl rfl,
            (expand_accepts_iff laws represented environment request task wanted taskWF).mp (.inr ⟨branch, generated, accepted⟩)⟩
        · exact .inr ⟨branch, .inr later, accepted⟩
      · rintro (old | ⟨branch, (same | later), accepted⟩)
        · exact .inl (.inl old)
        · subst branch
          rcases (expand_accepts_iff laws represented environment request task wanted taskWF).mpr accepted with
            emitted | ⟨generated, member, accepted⟩
          · exact .inl (.inr emitted)
          · exact .inr ⟨generated, .inl member, accepted⟩
        · exact .inr ⟨branch, .inr later, accepted⟩

theorem start_accepts_iff (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (wanted : CertifiedAnswer environment request matcher) :
    StateAccepts laws environment request (start environment request matcher) wanted ↔
      Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments request.initial
        wanted.rowIndex wanted.assignment wanted.origins := by
  simp only [StateAccepts, start, List.not_mem_nil, false_or, List.mem_singleton,
    exists_eq_left, TaskAccepts]

theorem run_accepts_iff (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request matcher) (wanted : CertifiedAnswer environment request matcher)
    (wellFormed : StateWellFormed environment request state) :
    StateAccepts laws environment request (run environment request fuel state) wanted ↔
      StateAccepts laws environment request state wanted := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      exact (ih (tick environment request state) (tick_wellFormed laws _ _ wellFormed)).trans
        (tick_accepts_iff laws represented _ _ _ _ wellFormed)

theorem state_accepts_iff (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request) (fuel : Nat)
    (wanted : CertifiedAnswer environment request matcher) :
    StateAccepts laws environment request (run environment request fuel (start environment request matcher)) wanted ↔
      Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments request.initial
        wanted.rowIndex wanted.assignment wanted.origins :=
  (run_accepts_iff laws represented _ _ _ _ _ (start_wellFormed _ _)).trans (start_accepts_iff laws _ _ _)

theorem unread_get (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (state : State environment request matcher) (cursor : Nat) (wanted : CertifiedAnswer environment request matcher) :
    UnreadAccepts laws environment request state cursor wanted ↔
      state.answers[cursor]? = some wanted ∨ UnreadAccepts laws environment request state (cursor + 1) wanted := by
  unfold UnreadAccepts
  rw [GeneralScopedMatchMachine.mem_drop_cursor_iff]
  exact or_assoc

theorem unread_start_of_valid (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (wanted : CertifiedAnswer environment request matcher) :
    UnreadAccepts laws environment request (start environment request matcher) 0 wanted :=
  (start_accepts_iff laws _ _ _).mpr wanted.valid

theorem unread_empty_of_settled (laws : matcher.CursorLaws) (environment : Environment) (request : Request)
    (state : State environment request matcher) (cursor : Nat) (wanted : CertifiedAnswer environment request matcher)
    (settled : state.agenda = []) (unavailable : state.answers[cursor]? = none) :
    ¬ UnreadAccepts laws environment request state cursor wanted := by
  have consumed : state.answers.drop cursor = [] :=
    List.drop_eq_nil_iff.mpr (List.getElem?_eq_none_iff.mp unavailable)
  simp only [UnreadAccepts, consumed, settled, List.not_mem_nil, false_and, exists_false, or_self, not_false_eq_true]

theorem unread_tick_of_no_answer (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request)
    (state : State environment request matcher) (cursor : Nat) (wanted : CertifiedAnswer environment request matcher)
    (wellFormed : StateWellFormed environment request state)
    (bounded : cursor ≤ state.answers.length) (unavailable : state.answers[cursor]? = none) :
    UnreadAccepts laws environment request (tick environment request state) cursor wanted ↔
      UnreadAccepts laws environment request state cursor wanted := by
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
            (expand_accepts_iff laws represented environment request task wanted taskWF).mp (.inl emitted)⟩
        · exact ⟨task, .inl rfl,
            (expand_accepts_iff laws represented environment request task wanted taskWF).mp (.inr ⟨branch, generated, accepted⟩)⟩
        · exact ⟨branch, .inr later, accepted⟩
      · rintro ⟨branch, (same | later), accepted⟩
        · subst branch
          rcases (expand_accepts_iff laws represented environment request task wanted taskWF).mpr accepted with
            emitted | ⟨generated, member, accepted⟩
          · exact .inl emitted
          · exact .inr ⟨generated, .inl member, accepted⟩
        · exact .inr ⟨branch, .inr later, accepted⟩

theorem answers_complete (laws : matcher.CursorLaws) (represented : ∀ query trace final,
      matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final) (environment : Environment) (request : Request) (fuel : Nat)
    (wanted : CertifiedAnswer environment request matcher)
    (settled : (run environment request fuel (start environment request matcher)).agenda = []) :
    wanted ∈ (run environment request fuel (start environment request matcher)).answers := by
  rcases (state_accepts_iff laws represented environment request fuel wanted).mpr wanted.valid with emitted | pending
  · exact emitted
  · obtain ⟨task, member, _⟩ := pending
    simp only [settled, List.not_mem_nil] at member


theorem completedEventually (laws : matcher.CursorLaws) (cost : matcher.CursorCost)
    (represented : ∀ query trace final, matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final)
    (environment : Environment) (request : Request) :
    ∃ fuel, (run environment request fuel (start environment request matcher)).agenda = [] ∧
      ∀ wanted : CertifiedAnswer environment request matcher,
        wanted ∈ (run environment request fuel (start environment request matcher)).answers := by
  obtain ⟨fuel, settled⟩ := finiteDrain cost environment request (start environment request matcher)
  exact ⟨fuel, settled, fun wanted => answers_complete laws represented
    environment request fuel wanted settled⟩

theorem traced_query_eventually (laws : matcher.CursorLaws) (cost : matcher.CursorCost)
    (represented : ∀ query trace final, matcher.meaning.Matches query trace final →
      ∃ answer : matcher.Answer,
        matcher.trace answer = trace ∧ matcher.assignment answer = final)
    (environment : Environment) (request : Request)
    {rowIndex : Nat} {assignment : Assignment} {origins : List (Nat × List matcher.Choice)}
    (held : Interpreted.TracedQuery matcher.meaning environment request.context request.relation request.arguments request.initial
      rowIndex assignment origins) :
    ∃ fuel, (run environment request fuel (start environment request matcher)).agenda = [] ∧
      ∃ answer ∈ (run environment request fuel (start environment request matcher)).answers,
        answer.rowIndex = rowIndex ∧ answer.assignment = assignment ∧ answer.origins = origins := by
  obtain ⟨fuel, settled, exhaustive⟩ := completedEventually laws cost represented environment request
  exact ⟨fuel, settled, ⟨rowIndex, assignment, origins, held⟩,
    exhaustive ⟨rowIndex, assignment, origins, held⟩, rfl, rfl, rfl⟩

#print axioms answer_eq_of_readout
#print axioms matcher_length_mono
#print axioms expand_wellFormed
#print axioms start_wellFormed
#print axioms tick_wellFormed
#print axioms run_wellFormed
#print axioms traced_nil_readout
#print axioms traced_shapes
#print axioms expandArguments_accepts_iff
#print axioms expandMatcher_accepts_iff
#print axioms valid_details
#print axioms expandRows_accepts_iff
#print axioms dynamic_input_shapes
#print axioms expandDynamicInputs_accepts_iff
#print axioms expandDynamicRows_accepts_iff
#print axioms expandStart_accepts_iff
#print axioms expand_accepts_iff
#print axioms tick_accepts_iff
#print axioms start_accepts_iff
#print axioms run_accepts_iff
#print axioms state_accepts_iff
#print axioms unread_get
#print axioms unread_start_of_valid
#print axioms unread_empty_of_settled
#print axioms unread_tick_of_no_answer
#print axioms answers_complete

#print axioms completedEventually
#print axioms traced_query_eventually

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

/-! ## Free-name coverage of the retained operations -/

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

/-- Each registered primitive response supplies its own object-value
support. Authored output schemas in the resolved request remain holes. -/
def DynamicOutputsFreeWithin (footprint : List String) (environment : Environment) : Prop :=
  ∀ relation ∈ environment.provider.dynamicRelations, ∀ resolved rows,
    environment.dynamic.Source relation resolved rows →
      ∀ values ∈ rows, patternsFreeWithin footprint values

theorem DynamicOutputsFreeWithin.of_empty (footprint : List String) (environment : Environment)
    (empty : environment.dynamic = DynamicProvider.empty) :
    DynamicOutputsFreeWithin footprint environment := by
  intro relation _ resolved rows source
  rw [empty] at source
  cases source

/-- A provider with no registered native methods has no native output
support obligation, regardless of the unused implementation. -/
theorem DynamicOutputsFreeWithin.of_unregistered (footprint : List String)
    (environment : Environment) (empty : environment.provider.dynamicRelations = []) :
    DynamicOutputsFreeWithin footprint environment := by
  intro relation registered
  simp only [empty, List.not_mem_nil] at registered

variable {matcher : MatchingExecution}

def taskFreeWithin (footprint : List String) {environment : Environment}
    {request : Query.Request} : Query.Task environment request matcher → Prop
  | .start => assignmentFreeWithin footprint request.initial
  | .rows _ => assignmentFreeWithin footprint request.initial
  | .dynamicInputs _ => assignmentFreeWithin footprint request.initial
  | .dynamicRows frame => assignmentFreeWithin footprint request.initial ∧
      ∀ values ∈ frame.rows, patternsFreeWithin footprint values
  | .arguments frame => assignmentFreeWithin footprint frame.assignment ∧
      patternsFreeWithin footprint frame.values
  | .matcher frame => assignmentFreeWithin footprint frame.query.initial ∧
      (∀ name ∈ frame.query.target.freeFvarNames, name ∈ footprint) ∧
      patternsFreeWithin footprint frame.values

def stateFreeWithin (footprint : List String) (environment : Environment)
    (request : Query.Request) (state : Query.State environment request matcher) : Prop :=
  (∀ task ∈ state.agenda, taskFreeWithin footprint task) ∧
  (∀ answer ∈ state.answers, assignmentFreeWithin footprint answer.assignment)

theorem arguments_expansion_free_within (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (frame : Query.ArgumentsFrame environment request matcher)
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

theorem matcher_expansion_free_within (support : matcher.PreservesFreeNames) (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (frame : Query.MatcherFrame environment request matcher)
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
    have captured := MatchingExecution.answer_free_within support frame.query frame.state frame.reachable answer
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

theorem dynamicInputs_expansion_free_within (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (dynamic : DynamicOutputsFreeWithin footprint environment)
    (frame : Query.DynamicInputsFrame environment request)
    (stored : assignmentFreeWithin footprint request.initial) :
    (∀ task ∈ (Query.expandDynamicInputs environment request frame matcher).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Query.expandDynamicInputs environment request frame matcher).answers,
      assignmentFreeWithin footprint answer.assignment) := by
  unfold Query.expandDynamicInputs
  split
  · split
    · constructor <;> intro item member <;> cases member
    · rename_i rows computed
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        refine ⟨stored, ?_⟩
        exact dynamic request.relation frame.registered _ rows
          ((environment.dynamic.rows_exact _ _ _).mp computed)
      · intro item member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact stored
      · intro item member; cases member
  · constructor
    · intro task member
      rcases List.mem_singleton.mp member with rfl
      exact stored
    · intro item member; cases member
  · constructor <;> intro item member <;> cases member

theorem dynamicRows_expansion_free_within (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (frame : Query.DynamicRowsFrame environment request)
    (stored : assignmentFreeWithin footprint request.initial)
    (values : ∀ row ∈ frame.rows, patternsFreeWithin footprint row) :
    (∀ task ∈ (Query.expandDynamicRows environment request frame matcher).tasks,
      taskFreeWithin footprint task) ∧
    (∀ answer ∈ (Query.expandDynamicRows environment request frame matcher).answers,
      assignmentFreeWithin footprint answer.assignment) := by
  unfold Query.expandDynamicRows
  split
  · constructor <;> intro item member <;> cases member
  · rename_i row selected
    split
    · constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨stored, values row (List.mem_of_getElem? selected)⟩
        · exact ⟨stored, values⟩
      · intro item member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨stored, values⟩
      · intro item member; cases member

theorem expansion_free_within (support : matcher.PreservesFreeNames) (footprint : List String)
    (environment : Environment) (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : DynamicOutputsFreeWithin footprint environment)
    (task : Query.Task environment request matcher) (covered : taskFreeWithin footprint task) :
    (∀ next ∈ (Query.expand environment request task).tasks, taskFreeWithin footprint next) ∧
    (∀ answer ∈ (Query.expand environment request task).answers,
      assignmentFreeWithin footprint answer.assignment) := by
  cases task with
  | start =>
      simp only [Query.expand]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor
          · intro next member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl <;> exact covered
          · intro item member; cases member
        · constructor
          · intro next member
            rcases List.mem_singleton.mp member with rfl
            exact covered
          · intro item member; cases member
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
  | dynamicInputs frame => exact dynamicInputs_expansion_free_within footprint environment request dynamic frame covered
  | dynamicRows frame => exact dynamicRows_expansion_free_within footprint environment request frame covered.1 covered.2
  | arguments frame => exact arguments_expansion_free_within footprint environment request frame covered.1 covered.2
  | matcher frame => exact matcher_expansion_free_within support footprint environment request frame covered.1 covered.2.1 covered.2.2
theorem run_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : DynamicOutputsFreeWithin footprint environment)
    (fuel : Nat) (state : Query.State environment request matcher)
    (covered : stateFreeWithin footprint environment request state) :
    stateFreeWithin footprint environment request (Query.run environment request fuel state) :=
  Scheduler.run_preserves (taskFreeWithin footprint) (fun (answer : Query.Answer environment request matcher) => assignmentFreeWithin footprint answer.assignment)
    (Query.expand environment request) (expansion_free_within support footprint environment request provider dynamic)
    fuel state covered

theorem start_free_within (footprint : List String) (environment : Environment)
    (request : Query.Request) (stored : assignmentFreeWithin footprint request.initial) :
    stateFreeWithin footprint environment request (Query.start environment request matcher) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact stored
  · intro answer member; cases member

theorem run_from_start_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : DynamicOutputsFreeWithin footprint environment)
    (stored : assignmentFreeWithin footprint request.initial) (fuel : Nat) :
    stateFreeWithin footprint environment request
      (Query.run environment request fuel (Query.start environment request matcher)) :=
  run_free_within support footprint environment request provider dynamic fuel _
    (start_free_within footprint environment request stored)
theorem tick_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : DynamicOutputsFreeWithin footprint environment)
    (state : Query.State environment request matcher) (covered : stateFreeWithin footprint environment request state) :
    stateFreeWithin footprint environment request (Query.tick environment request state) :=
  Scheduler.tick_preserves (taskFreeWithin footprint)
    (fun (answer : Query.Answer environment request matcher) => assignmentFreeWithin footprint answer.assignment)
    (Query.expand environment request) (expansion_free_within support footprint environment request provider dynamic) state covered
theorem run_answer_free_within (support : matcher.PreservesFreeNames) (footprint : List String) (environment : Environment)
    (request : Query.Request)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : DynamicOutputsFreeWithin footprint environment)
    (stored : assignmentFreeWithin footprint request.initial) (fuel : Nat)
    (answer : Query.Answer environment request matcher)
    (member : answer ∈ (Query.run environment request fuel (Query.start environment request matcher)).answers) :
    assignmentFreeWithin footprint answer.assignment :=
  (run_from_start_free_within support footprint environment request provider dynamic stored fuel).2 answer member
theorem run_finite_free_within (support : matcher.PreservesFreeNames) (environment : Environment) (request : Query.Request)
    (dynamic : DynamicOutputsFreeWithin
      (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider) environment)
    (fuel : Nat) :
    stateFreeWithin (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider)
      environment request (Query.run environment request fuel (Query.start environment request matcher)) := by
  apply run_from_start_free_within support
  · exact provider_coverage_mono _ _ environment.provider
      (fun name member => List.mem_append_right _ member) (provider_covered_by_own_names environment.provider)
  · exact dynamic
  · exact assignment_coverage_mono _ _ request.initial
      (fun name member => List.mem_append_left _ member) (assignment_covered_by_own_names request.initial)

theorem prefix_assignment_check_snapshot (support : matcher.PreservesFreeNames) (environment : Environment) (request : Query.Request)
    (dynamic : DynamicOutputsFreeWithin
      (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider) environment)
    (fuel : Nat) (frame : Query.ArgumentsFrame environment request matcher)
    (member : Query.Task.arguments frame ∈
      (Query.run environment request fuel (Query.start environment request matcher)).agenda) :
    ConditionalEquationExecution.checkAssignment environment.language
      (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList
        (environment.free.entriesOn (ConditionalEquationExecution.assignmentFreeNames request.initial ++ providerFreeNames environment.provider)))
      request.context.bound request.context.rule request.context.spec frame.assignment =
      checkTypedAssignment environment request.context frame.assignment := by
  unfold checkTypedAssignment
  apply ConditionalEquationExecution.checkAssignment_snapshot
  apply assignment_free_names_covered
  exact ((run_finite_free_within support environment request dynamic fuel).1 _ member).1



#print axioms removed_parameter_free_within
#print axioms bound_parameter_free_within
#print axioms restored_parameter_free_within
#print axioms finite_collection_free_within
#print axioms DynamicOutputsFreeWithin.of_empty
#print axioms DynamicOutputsFreeWithin.of_unregistered
#print axioms arguments_expansion_free_within
#print axioms matcher_expansion_free_within
#print axioms dynamicInputs_expansion_free_within
#print axioms dynamicRows_expansion_free_within
#print axioms expansion_free_within
#print axioms run_free_within
#print axioms start_free_within
#print axioms run_from_start_free_within
#print axioms tick_free_within
#print axioms run_answer_free_within
#print axioms run_finite_free_within
#print axioms prefix_assignment_check_snapshot

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query


namespace Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

open Syntax RuleBinding ScopedRuleMatching GeneralPremise Mettapedia.GSLT.LanguageDef.WellSorted

variable {table : List String}

theorem valuesTyped_covered {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {values : List Pattern} {types : List TypeExpr}
    (typed : ValuesTyped language free bound values types) {footprint : List String}
    (declarations : ∀ rule ∈ language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (freeNames : patternsFreeWithin footprint values) : PatternsCovered table values := by
  induction typed with
  | nil => intro value member; cases member
  | cons head tail ih =>
      intro value member
      rcases List.mem_cons.mp member with rfl | later
      · apply TypedObjectAlphabet.wellSorted_covered head declarations
        intro name occurs
        exact included name (freeNames _ List.mem_cons_self name occurs)
      · exact ih (fun value member => freeNames value (List.mem_cons_of_mem _ member)) value later

end Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport

open Syntax RuleBinding ScopedRuleMatching CanonicalCompare CanonicalCompare.AllNameSupport
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {matcher : MatchingExecution} {table footprint : List String}

def TaskCovered {environment : Environment} {request : Query.Request} :
    Query.Task environment request matcher → Prop
  | .start | .rows _ => AssignmentCovered table request.initial
  | .dynamicInputs frame => AssignmentCovered table request.initial ∧
      PatternsCovered table frame.schemas ∧ PatternsCovered table frame.resolvedRev
  | .dynamicRows _ => AssignmentCovered table request.initial
  | .arguments frame => AssignmentCovered table frame.assignment ∧
      PatternsCovered table frame.schemas ∧ PatternsCovered table frame.values
  | .matcher frame => AssignmentCovered table frame.query.initial ∧ Covered table frame.query.target ∧
      PatternsCovered table frame.schemas ∧ PatternsCovered table frame.values

def StateCovered (environment : Environment) (request : Query.Request)
    (state : Query.State environment request matcher) : Prop :=
  (∀ task ∈ state.agenda, TaskCovered (table := table) task) ∧
    (∀ answer ∈ state.answers, AssignmentCovered table answer.assignment)

def ExpansionCovered {environment : Environment} {request : Query.Request}
    (expansion : Scheduler.Expansion (Query.Task environment request matcher)
      (Query.Answer environment request matcher) Query.Obligation) : Prop :=
  (∀ task ∈ expansion.tasks, TaskCovered (table := table) task) ∧
    (∀ answer ∈ expansion.answers, AssignmentCovered table answer.assignment)

theorem arguments_expansion_covered (environment : Environment) (request : Query.Request)
    (_spines : SpecificationCovered table request.context.spec)
    (frame : Query.ArgumentsFrame environment request matcher)
    (covered : TaskCovered (table := table) (.arguments frame)) :
    ExpansionCovered (table := table) (Query.expandArguments environment request frame) := by
  unfold Query.expandArguments
  split
  · split
    · constructor
      · intro task member; cases member
      · intro answer member
        rcases List.mem_singleton.mp member with rfl
        exact covered.1
    · constructor <;> intro item member <;> cases member
  · rename_i schema schemas value values mode modes schemasFound valuesFound modesFound
    have schemasCovered : PatternsCovered table schemas :=
      fun schema member => covered.2.1 schema (by rw [schemasFound]; exact List.mem_cons_of_mem _ member)
    have valueCovered := covered.2.2 value (by rw [valuesFound]; exact List.mem_cons_self)
    have valuesCovered : PatternsCovered table values :=
      fun value member => covered.2.2 value (by rw [valuesFound]; exact List.mem_cons_of_mem _ member)
    split
    · split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact ⟨covered.1, schemasCovered, valuesCovered⟩
          · intro answer member; cases member
        · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact ⟨covered.1, valueCovered, schemasCovered, valuesCovered⟩
      · intro answer member; cases member
  · constructor <;> intro item member <;> cases member

theorem matcher_expansion_covered (support : matcher.PreservesNames)
    (environment : Environment) (request : Query.Request)
    (frame : Query.MatcherFrame environment request matcher)
    (covered : TaskCovered (table := table) (.matcher frame)) :
    ExpansionCovered (table := table) (Query.expandMatcher environment request frame) := by
  unfold Query.expandMatcher
  split
  · rename_i answer found
    have captured := MatchingExecution.answer_covered support frame.reachable
      (List.mem_of_getElem? found) covered.1 covered.2.1
    constructor
    · intro task member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨captured, covered.2.2⟩
      · exact covered
    · intro answer member; cases member
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact covered
      · intro answer member; cases member

theorem dynamicInputs_expansion_covered (environment : Environment) (request : Query.Request)
    (spines : SpecificationCovered table request.context.spec)
    (frame : Query.DynamicInputsFrame environment request)
    (covered : TaskCovered (matcher := matcher) (table := table) (.dynamicInputs frame)) :
    ExpansionCovered (table := table) (Query.expandDynamicInputs environment request frame matcher) := by
  unfold Query.expandDynamicInputs
  split
  · split
    · constructor <;> intro item member <;> cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact covered.1
      · intro answer member; cases member
  · rename_i schema schemas modes schemasFound modesFound
    have schemasCovered : PatternsCovered table schemas :=
      fun schema member => covered.2.1 schema (by rw [schemasFound]; exact List.mem_cons_of_mem _ member)
    split
    · constructor <;> intro item member <;> cases member
    · rename_i value interpreted
      have valueCovered := instantiateAt_covered covered.1 spines
        (covered.2.1 schema (by rw [schemasFound]; exact List.mem_cons_self)) interpreted
      constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        refine ⟨covered.1, schemasCovered, ?_⟩
        intro value member
        rcases List.mem_cons.mp member with rfl | later
        · exact valueCovered
        · exact covered.2.2 value later
      · intro answer member; cases member
  · rename_i schema schemas modes schemasFound modesFound
    constructor
    · intro task member
      rcases List.mem_singleton.mp member with rfl
      refine ⟨covered.1, ?_, ?_⟩
      · intro schema member
        exact covered.2.1 schema (by rw [schemasFound]; exact List.mem_cons_of_mem _ member)
      · intro value member
        rcases List.mem_cons.mp member with rfl | later
        · exact covered.2.1 value (by rw [schemasFound]; exact List.mem_cons_self)
        · exact covered.2.2 value later
    · intro answer member; cases member
  · constructor <;> intro item member <;> cases member

theorem dynamicRows_expansion_covered (environment : Environment) (request : Query.Request)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (schemas : PatternsCovered table request.arguments)
    (frame : Query.DynamicRowsFrame environment request)
    (free : Query.taskFreeWithin footprint (matcher := matcher) (.dynamicRows frame))
    (covered : TaskCovered (matcher := matcher) (table := table) (.dynamicRows frame)) :
    ExpansionCovered (table := table) (Query.expandDynamicRows environment request frame matcher) := by
  unfold Query.expandDynamicRows
  split
  · constructor <;> intro item member <;> cases member
  · rename_i values found
    split
    · rename_i checked
      have valuesCovered := valuesTyped_covered (checkRow_sound checked).2 declarations included
        (free.2 values (List.mem_of_getElem? found))
      constructor
      · intro task member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ⟨covered, schemas, valuesCovered⟩
        · exact covered
      · intro answer member; cases member
    · constructor
      · intro task member
        rcases List.mem_singleton.mp member with rfl
        exact covered
      · intro answer member; cases member

theorem expansion_covered (support : matcher.PreservesNames)
    (environment : Environment) (request : Query.Request)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (schemas : PatternsCovered table request.arguments)
    (spines : SpecificationCovered table request.context.spec)
    (task : Query.Task environment request matcher)
    (free : Query.taskFreeWithin footprint task) (covered : TaskCovered (table := table) task) :
    ExpansionCovered (table := table) (Query.expand environment request task) := by
  cases task with
  | start =>
      simp only [Query.expand]
      split
      · constructor <;> intro item member <;> cases member
      · split
        · constructor
          · intro task member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact covered
            · exact ⟨covered, schemas, by intro value member; cases member⟩
          · intro answer member; cases member
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact covered
          · intro answer member; cases member
  | rows frame =>
      simp only [Query.expand]
      split
      · constructor <;> intro item member <;> cases member
      · rename_i row found
        split
        · rename_i checked
          have valuesCovered := valuesTyped_covered (checkRow_sound checked).2 declarations included
            (provider row (List.mem_of_getElem? found))
          constructor
          · intro task member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact ⟨covered, schemas, valuesCovered⟩
            · exact covered
          · intro answer member; cases member
        · constructor
          · intro task member
            rcases List.mem_singleton.mp member with rfl
            exact covered
          · intro answer member; cases member
  | dynamicInputs frame => exact dynamicInputs_expansion_covered environment request spines frame covered
  | dynamicRows frame => exact dynamicRows_expansion_covered environment request declarations included schemas frame free covered
  | arguments frame => exact arguments_expansion_covered environment request spines frame covered
  | matcher frame => exact matcher_expansion_covered support environment request frame covered

theorem run_covered (support : matcher.PreservesNames) (freeSupport : matcher.PreservesFreeNames)
    (environment : Environment) (request : Query.Request)
    (declarations : ∀ rule ∈ environment.language.terms, rule.label ∈ table)
    (included : ∀ name ∈ footprint, name ∈ table)
    (provider : ∀ row ∈ environment.provider.rows, patternsFreeWithin footprint row.values)
    (dynamic : Query.DynamicOutputsFreeWithin footprint environment)
    (schemas : PatternsCovered table request.arguments)
    (spines : SpecificationCovered table request.context.spec)
    (fuel : Nat) (state : Query.State environment request matcher)
    (free : Query.stateFreeWithin footprint environment request state)
    (covered : StateCovered (table := table) environment request state) :
    StateCovered (table := table) environment request (Query.run environment request fuel state) := by
  let taskProperty : Query.Task environment request matcher → Prop :=
    fun task => Query.taskFreeWithin footprint task ∧ TaskCovered (table := table) task
  let answerProperty : Query.Answer environment request matcher → Prop :=
    fun answer => assignmentFreeWithin footprint answer.assignment ∧ AssignmentCovered table answer.assignment
  have preserves : ∀ task, taskProperty task →
      (∀ next ∈ (Query.expand environment request task).tasks, taskProperty next) ∧
      (∀ answer ∈ (Query.expand environment request task).answers, answerProperty answer) := by
    intro task before
    have freeNext := Query.expansion_free_within freeSupport footprint environment request provider dynamic task before.1
    have namesNext := expansion_covered support environment request declarations included provider schemas spines task before.1 before.2
    exact ⟨fun next member => ⟨freeNext.1 next member, namesNext.1 next member⟩,
      fun answer member => ⟨freeNext.2 answer member, namesNext.2 answer member⟩⟩
  have result := Scheduler.run_preserves taskProperty answerProperty (Query.expand environment request) preserves fuel state
    ⟨fun task member => ⟨free.1 task member, covered.1 task member⟩,
      fun answer member => ⟨free.2 answer member, covered.2 answer member⟩⟩
  exact ⟨fun task member => (result.1 task member).2, fun answer member => (result.2 answer member).2⟩

theorem start_covered (environment : Environment) (request : Query.Request)
    (covered : AssignmentCovered table request.initial) :
    StateCovered (table := table) environment request (Query.start environment request matcher) := by
  constructor
  · intro task member
    rcases List.mem_singleton.mp member with rfl
    exact covered
  · intro answer member; cases member

theorem input_actual_covered {environment : Environment} {request : Query.Request}
    {frame : Query.ArgumentsFrame environment request matcher}
    (spines : SpecificationCovered table request.context.spec)
    (covered : TaskCovered (table := table) (.arguments frame))
    {schema : Pattern} {schemas : List Pattern} (shape : frame.schemas = schema :: schemas)
    {actual : Pattern}
    (read : instantiateAt? request.context.rule request.context.spec request.context.bound.length
      (request.context.site frame.index) [] 0 frame.assignment schema = some actual) : Covered table actual :=
  instantiateAt_covered covered.1 spines
    (covered.2.1 schema (by rw [shape]; exact List.mem_cons_self)) read


end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport

#print axioms Mettapedia.OSLF.MeTTaIL.CanonicalCompare.AllNameSupport.valuesTyped_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.TaskCovered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.StateCovered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.ExpansionCovered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.arguments_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.matcher_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.dynamicInputs_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.dynamicRows_expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.expansion_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.run_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.start_covered
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query.NameSupport.input_actual_covered
