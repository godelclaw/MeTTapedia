import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryCorrectness
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
import Mettapedia.OSLF.Framework.GeneralFiniteWorkReadout

/-!
# The order in which a relation query emits its answers

The shared premise scheduler reads out the answers of a finite expansion tree
in scheduler order (`Scheduler.TaskTree.answers`, `finiteWork_readouts`). The
query machine builds such a tree for every retained task from its termination
rank (`taskTree`), so a task denotes the ordered list of answers it will still
emit (`eventual`), and a drained run has emitted exactly its agenda's answers, in
agenda order (`run_settled`). From the start, these are the answers of the
provider rows, in row order (`eventual_rows_some`).

Every answer of a row's argument task belongs to that row
(`eventual_rowIndex`). For first-order argument schemas the scoped matcher is
deterministic, so each row contributes at most one answer
(`eventual_arguments_length_le_one`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection (FirstOrder)

/-- A structural task whose schemas are first-order: constructors and
metavariables only. -/
def TaskFirstOrder : Task → Prop
  | .tree _ _ schema _ => FirstOrder schema
  | .arguments _ _ _ schemas _ => ∀ schema ∈ schemas, FirstOrder schema
  | _ => False

def WorkFirstOrder (work : Work) : Prop := ∀ task ∈ work.tasks, TaskFirstOrder task

/-- A first-order task has at most one continuation, which is first-order and
makes no collection choice. -/
theorem expand_firstOrder (request : Request) (initial : Assignment) {task : Task}
    (shape : TaskFirstOrder task) :
    (expand request initial task).length ≤ 1 ∧
      ∀ work ∈ expand request initial task, WorkFirstOrder work ∧ work.trace = [] := by
  cases task with
  | tree path depth schema target =>
    cases shape with
    | metavariable name =>
      simp only [expand]
      cases (capture? request.rule request.spec request.ambient depth request.site path initial
          name target) <;> simp [WorkFirstOrder]
    | constructor label schemas children =>
      cases target
      case apply actualLabel targets =>
        simp only [expand]
        split
        · refine ⟨by simp, ?_⟩
          intro work member
          simp only [List.mem_singleton] at member
          subst member
          refine ⟨?_, rfl⟩
          intro task taskMember
          simp only [List.mem_singleton] at taskMember
          subst taskMember
          exact children
        · simp
      all_goals simp [expand]
  | arguments path depth index schemas targets =>
    cases schemas with
    | nil => cases targets <;> simp [expand, WorkFirstOrder]
    | cons schema schemas =>
      cases targets with
      | nil => simp [expand]
      | cons target targets =>
        simp only [expand]
        refine ⟨by simp, ?_⟩
        intro work member
        simp only [List.mem_singleton] at member
        subst member
        refine ⟨?_, rfl⟩
        intro task taskMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at taskMember
        rcases taskMember with rfl | rfl
        · exact shape schema (List.mem_cons_self ..)
        · exact fun child member => shape child (List.mem_cons_of_mem _ member)
  | bag => exact shape.elim
  | bagSelect => exact shape.elim
  | restCapture => exact shape.elim

theorem advance_firstOrder (request : Request) {work : Work} (shape : WorkFirstOrder work) :
    (advance request work).length ≤ 1 ∧
      ∀ next ∈ advance request work, WorkFirstOrder next ∧ next.trace = work.trace := by
  unfold advance
  split
  · simp
  · rename_i task tasks tasksEq
    have taskShape : TaskFirstOrder task := shape task (by simp [tasksEq])
    have restShape : ∀ later ∈ tasks, TaskFirstOrder later :=
      fun later member => shape later (by simp [tasksEq, member])
    obtain ⟨bound, branches⟩ := expand_firstOrder request work.assignment taskShape
    refine ⟨by simpa using bound, ?_⟩
    intro next member
    obtain ⟨branch, branchMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨branchShape, branchTrace⟩ := branches branch branchMember
    refine ⟨?_, by simp [branchTrace]⟩
    intro later laterMember
    rcases List.mem_append.mp laterMember with inBranch | inRest
    · exact branchShape later inBranch
    · exact restShape later inRest

/-- A deterministic matcher state: at most one branch is pending or finished,
and every pending branch is first-order. -/
def Deterministic (state : State) : Prop :=
  state.agenda.length + state.answers.length ≤ 1 ∧ ∀ work ∈ state.agenda, WorkFirstOrder work

theorem start_deterministic {request : Request} (shape : FirstOrder request.schema) :
    Deterministic (start request) := by
  refine ⟨by simp [start], ?_⟩
  intro work member
  simp only [start, List.mem_singleton] at member
  subst member
  intro task taskMember
  simp only [List.mem_singleton] at taskMember
  subst taskMember
  exact shape

theorem tick_deterministic (request : Request) {state : State} (deterministic : Deterministic state) :
    Deterministic (tick request state) := by
  obtain ⟨count, shapes⟩ := deterministic
  unfold tick
  split
  · exact ⟨count, shapes⟩
  · rename_i work rest agendaEq
    rw [agendaEq] at count shapes
    simp only [List.length_cons] at count
    have restNil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    have answersNil : state.answers = [] := List.eq_nil_of_length_eq_zero (by omega)
    have workShape : WorkFirstOrder work := shapes work (List.mem_cons_self ..)
    split
    · exact ⟨by simp [restNil, answersNil], by simp [restNil]⟩
    · obtain ⟨bound, nexts⟩ := advance_firstOrder request workShape
      refine ⟨by simp only [restNil, answersNil, List.append_nil, List.length_nil]; omega, ?_⟩
      intro next member
      rw [restNil, List.append_nil] at member
      exact (nexts next member).1

theorem run_deterministic (request : Request) :
    ∀ (fuel : Nat) {state : State}, Deterministic state → Deterministic (run request fuel state)
  | 0, _, deterministic => deterministic
  | fuel + 1, _, deterministic => run_deterministic request fuel (tick_deterministic request deterministic)

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection (FirstOrder)

/-! ## The ordered denotation of retained query work -/

/-- The finite expansion tree of a retained query task, built from the
termination rank. -/
def taskTree (environment : Environment) (request : Request) (task : Task environment request) :
    Scheduler.TaskTree (expand environment request) task :=
  .branch (Scheduler.forestOfTrees (expand environment request) (expand environment request task).tasks
    fun branch _member => taskTree environment request branch)
termination_by task.rank environment request
decreasing_by exact expand_decreases environment request task branch _member

/-- The answers a retained query task emits, in emission order: the scheduler's
readout of its expansion tree. -/
abbrev eventual (environment : Environment) (request : Request) (task : Task environment request) :
    List (Answer environment request) :=
  (taskTree environment request task).answers

private theorem forestOfTrees_answers (environment : Environment) (request : Request) :
    ∀ tasks : List (Task environment request),
      (Scheduler.forestOfTrees (expand environment request) tasks
          fun branch _ => taskTree environment request branch).answers =
        tasks.flatMap (eventual environment request)
  | [] => rfl
  | task :: tasks => by
    simp only [Scheduler.forestOfTrees, Scheduler.TaskForest.answers, List.flatMap_cons]
    rw [forestOfTrees_answers environment request tasks]

theorem eventual_eq (environment : Environment) (request : Request) (task : Task environment request) :
    eventual environment request task =
      (expand environment request task).answers ++
        (expand environment request task).tasks.flatMap (eventual environment request) := by
  show (taskTree environment request task).answers = _
  rw [taskTree, Scheduler.TaskTree.answers, forestOfTrees_answers]

/-- Exact denotation of every retained task, including acquired native rows
and suspended input resolution, against the independent acceptance relation. -/
theorem mem_eventual_iff (environment : Environment) (request : Request)
    (task : Task environment request) (wanted : Answer environment request)
    (wellFormed : TaskWellFormed environment request task) :
    wanted ∈ eventual environment request task ↔ TaskAccepts environment request task wanted := by
  apply Iff.trans ?_ (expand_accepts_iff environment request task wanted wellFormed)
  rw [eventual_eq]
  simp only [List.mem_append, List.mem_flatMap, ExpansionAccepts]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨branch, member, accepted⟩
    exact ⟨branch, member, (mem_eventual_iff environment request branch wanted
      (expand_wellFormed environment request task branch wellFormed member)).mp accepted⟩
  · rintro ⟨branch, member, accepted⟩
    exact ⟨branch, member, (mem_eventual_iff environment request branch wanted
      (expand_wellFormed environment request task branch wellFormed member)).mpr accepted⟩
termination_by task.rank environment request
decreasing_by all_goals exact expand_decreases environment request task branch member

/-- **A drained query run has emitted exactly its agenda's answers, in agenda order.** -/
theorem run_settled (environment : Environment) (request : Request) (fuel : Nat)
    (state : State environment request) (settled : (run environment request fuel state).agenda = []) :
    (run environment request fuel state).answers =
      state.answers ++ state.agenda.flatMap (eventual environment request) := by
  let forest := Scheduler.forestOfTrees (expand environment request) state.agenda
    fun branch _ => taskTree environment request branch
  have drained := Scheduler.finiteWork_drains (expand environment request) forest.cost state forest (Nat.le_refl _)
  have same := Scheduler.settled_run_unique (expand environment request) state fuel forest.cost settled drained
  change (Scheduler.run (expand environment request) fuel state).answers = _
  rw [same, (Scheduler.finiteWork_readouts (expand environment request) forest.cost state forest
    (Nat.le_refl _)).1, forestOfTrees_answers]

theorem settled_answers (environment : Environment) (request : Request) (fuel : Nat)
    (settled : (run environment request fuel (start environment request)).agenda = []) :
    (run environment request fuel (start environment request)).answers =
      eventual environment request .start := by
  rw [run_settled environment request fuel _ settled]
  simp [start]

/-- Every certified answer is emitted by the start task's denotation. -/
theorem mem_eventual_start (environment : Environment) (request : Request)
    (wanted : Answer environment request) : wanted ∈ eventual environment request .start := by
  obtain ⟨fuel, settled, exhaustive⟩ := completedEventually environment request
  rw [← settled_answers environment request fuel settled]
  exact exhaustive wanted


/-! ## Provider rows, in order -/

/-- The argument task that a scanned provider row starts. -/
def rowArguments {environment : Environment} {request : Request} (frame : RowsFrame environment request)
    (row : ProviderRow) (found : environment.provider.rows[frame.cursor]? = some row)
    (checked : checkRow environment.language environment.free request.context.bound frame.signature row = true) :
    ArgumentsFrame environment request where
  rowIndex := frame.cursor
  index := 0
  assignment := request.initial
  schemas := request.arguments
  values := row.values
  modes := frame.signature.modes
  origins := []
  finish := fun final traces held typed => by
    simpa using TracedQuery.row found frame.signatureFound (checkRow_sound checked) held typed

def RowsFrame.next {environment : Environment} {request : Request} (frame : RowsFrame environment request) :
    RowsFrame environment request := { frame with cursor := frame.cursor + 1 }

def dynamicInputsStart (environment : Environment) (request : Request) (signature : Signature)
    (found : signature? environment.provider request.relation request.arguments.length = some signature)
    (registered : request.relation ∈ environment.provider.dynamicRelations) :
    DynamicInputsFrame environment request where
  signature := signature
  signatureFound := found
  registered := registered
  index := 0
  schemas := request.arguments
  modes := signature.modes
  resolvedRev := []
  finish := by intro values held; simpa only [List.reverse_nil, List.nil_append] using held

theorem eventual_start_some (environment : Environment) (request : Request) {signature : Signature}
    (found : signature? environment.provider request.relation request.arguments.length = some signature) :
    eventual environment request .start =
      eventual environment request (.rows ⟨signature, found, 0⟩) ++
        if registered : request.relation ∈ environment.provider.dynamicRelations then
          eventual environment request (.dynamicInputs
            (dynamicInputsStart environment request signature found registered))
        else [] := by
  rw [eventual_eq]
  simp only [expand]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i other otherFound
    have same : other = signature := Option.some.inj (otherFound.symm.trans found)
    subst same
    split <;> simp [dynamicInputsStart]

theorem eventual_start_none (environment : Environment) (request : Request)
    (missing : signature? environment.provider request.relation request.arguments.length = none) :
    eventual environment request .start = [] := by
  rw [eventual_eq]
  simp only [expand]
  split
  · simp
  · rename_i other otherFound
    rw [missing] at otherFound
    cases otherFound

theorem eventual_rows_none (environment : Environment) (request : Request)
    (frame : RowsFrame environment request)
    (missing : environment.provider.rows[frame.cursor]? = none) :
    eventual environment request (.rows frame) = [] := by
  rw [eventual_eq]
  simp only [expand]
  split
  · simp
  · rename_i row found
    rw [missing] at found
    cases found

/-- **Rows are scanned in order.** A checked row contributes its argument
task's answers before the remaining rows; an unchecked row contributes none. -/
theorem eventual_rows_some (environment : Environment) (request : Request)
    (frame : RowsFrame environment request) {row : ProviderRow}
    (found : environment.provider.rows[frame.cursor]? = some row) :
    eventual environment request (.rows frame) =
      (if checked : checkRow environment.language environment.free request.context.bound
            frame.signature row = true then
          eventual environment request (.arguments (rowArguments frame row found checked))
        else []) ++
      eventual environment request (.rows frame.next) := by
  rw [eventual_eq]
  simp only [expand]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i other otherFound
    have same : other = row := Option.some.inj (otherFound.symm.trans found)
    subst same
    split
    · rename_i checked
      simp [RowsFrame.next, rowArguments]
    · rename_i unchecked
      simp [RowsFrame.next]

/-- The original argument machine retains the acquired native table's
source proof and the offset occurrence index. -/
def dynamicRowArguments {environment : Environment} {request : Request}
    (frame : DynamicRowsFrame environment request) (values : List Pattern)
    (found : frame.rows[frame.cursor]? = some values)
    (checked : checkRow environment.language environment.free request.context.bound
      frame.signature ⟨request.relation, values⟩ = true) : ArgumentsFrame environment request where
  rowIndex := environment.provider.rows.length + frame.cursor
  index := 0
  assignment := request.initial
  schemas := request.arguments
  values := values
  modes := frame.signature.modes
  origins := []
  finish := fun final traces held typed => by
    simpa only [List.nil_append] using TracedQuery.dynamicRow frame.registered
      frame.signatureFound frame.inputs frame.source found (checkRow_sound checked) held typed

def DynamicRowsFrame.next {environment : Environment} {request : Request}
    (frame : DynamicRowsFrame environment request) : DynamicRowsFrame environment request :=
  { frame with cursor := frame.cursor + 1 }

theorem eventual_dynamicRows_none (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) (missing : frame.rows[frame.cursor]? = none) :
    eventual environment request (.dynamicRows frame) = [] := by
  rw [eventual_eq]
  simp only [expand, expandDynamicRows]
  split
  · simp
  · rename_i values found
    rw [missing] at found
    cases found

/-- The retained acquired table is scanned in occurrence order. Equal rows
remain separate positions and each accepted row precedes its remaining tail. -/
theorem eventual_dynamicRows_some (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) {values : List Pattern}
    (found : frame.rows[frame.cursor]? = some values) :
    eventual environment request (.dynamicRows frame) =
      (if checked : checkRow environment.language environment.free request.context.bound
          frame.signature ⟨request.relation, values⟩ = true then
        eventual environment request (.arguments (dynamicRowArguments frame values found checked))
      else []) ++ eventual environment request (.dynamicRows frame.next) := by
  rw [eventual_eq]
  simp only [expand, expandDynamicRows]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i actual actualFound
    have same : actual = values := Option.some.inj (actualFound.symm.trans found)
    subst same
    split
    · simp [DynamicRowsFrame.next, dynamicRowArguments]
    · simp [DynamicRowsFrame.next]

/-- Every native-row answer is located at the actual acquired row and in
that row's original argument/matcher execution, retaining the native index. -/
theorem eventual_dynamicRows_locate (environment : Environment) (request : Request)
    (frame : DynamicRowsFrame environment request) (wanted : Answer environment request)
    (member : wanted ∈ eventual environment request (.dynamicRows frame)) :
    ∃ nativeIndex, frame.cursor ≤ nativeIndex ∧
      wanted.rowIndex = environment.provider.rows.length + nativeIndex ∧
      ∃ values, ∃ found : frame.rows[nativeIndex]? = some values,
        ∃ checked : checkRow environment.language environment.free request.context.bound
          frame.signature ⟨request.relation, values⟩ = true,
        wanted ∈ eventual environment request (.arguments
          (dynamicRowArguments { frame with cursor := nativeIndex } values found checked)) := by
  obtain ⟨nativeIndex, values, bounded, rowSame, found, typed, held, finalTyped⟩ :=
    (mem_eventual_iff environment request (.dynamicRows frame) wanted trivial).mp member
  refine ⟨nativeIndex, bounded, rowSame, values, found, checkRow_complete typed, ?_⟩
  apply (mem_eventual_iff environment request (.arguments
    (dynamicRowArguments { frame with cursor := nativeIndex } values found (checkRow_complete typed)))
    wanted trivial).mpr
  exact ⟨rowSame, wanted.origins, held, finalTyped, by simp [dynamicRowArguments]⟩

/-! ## Answers belong to the row that started them -/

/-- The provider row a retained argument or matcher task belongs to. -/
def Task.row? {environment : Environment} {request : Request} : Task environment request → Option Nat
  | .arguments frame => some frame.rowIndex
  | .matcher frame => some frame.rowIndex
  | _ => none

theorem expand_row (environment : Environment) (request : Request) {task : Task environment request}
    {index : Nat} (owned : task.row? = some index) :
    (∀ answer ∈ (expand environment request task).answers, answer.rowIndex = index) ∧
      ∀ branch ∈ (expand environment request task).tasks, branch.row? = some index := by
  cases task with
  | start => cases owned
  | rows => cases owned
  | dynamicInputs => cases owned
  | dynamicRows => cases owned
  | arguments frame =>
    simp only [Task.row?, Option.some.injEq] at owned
    subst owned
    simp only [expand]
    unfold expandArguments
    split
    · split
      · refine ⟨?_, by simp⟩
        intro answer member
        simp only [List.mem_singleton] at member
        subst member
        rfl
      · simp
    · rename_i mode modes _ _ _
      cases mode with
      | input =>
        dsimp only
        split
        · simp
        · split
          · refine ⟨by simp, ?_⟩
            intro branch member
            simp only [List.mem_singleton] at member
            subst member
            rfl
          · simp
      | output =>
        dsimp only
        refine ⟨by simp, ?_⟩
        intro branch member
        simp only [List.mem_singleton] at member
        subst member
        rfl
    · simp
  | matcher frame =>
    simp only [Task.row?, Option.some.injEq] at owned
    subst owned
    simp only [expand]
    unfold expandMatcher
    split
    · refine ⟨by simp, ?_⟩
      intro branch member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    · split
      · simp
      · refine ⟨by simp, ?_⟩
        intro branch member
        simp only [List.mem_singleton] at member
        subst member
        rfl

/-- Every answer of a retained argument or matcher task has that task's row. -/
theorem eventual_rowIndex (environment : Environment) (request : Request)
    (task : Task environment request) {index : Nat} (owned : task.row? = some index) :
    ∀ answer ∈ eventual environment request task, answer.rowIndex = index := by
  intro answer member
  rw [eventual_eq] at member
  obtain ⟨direct, branches⟩ := expand_row environment request owned
  rcases List.mem_append.mp member with here | later
  · exact direct answer here
  · obtain ⟨branch, branchMember, inBranch⟩ := List.mem_flatMap.mp later
    exact eventual_rowIndex environment request branch (branches branch branchMember) answer inBranch
termination_by task.rank environment request
decreasing_by exact expand_decreases environment request task branch branchMember

/-- Every answer of a row scan comes from its cursor's row or a later one, and
lies in that row's own argument task. -/
theorem eventual_rows_locate (environment : Environment) (request : Request)
    (frame : RowsFrame environment request) (wanted : Answer environment request)
    (member : wanted ∈ eventual environment request (.rows frame)) :
    frame.cursor ≤ wanted.rowIndex ∧ ∀ cursor, wanted.rowIndex = cursor →
      ∃ row, ∃ found : environment.provider.rows[cursor]? = some row,
        ∃ checked : checkRow environment.language environment.free request.context.bound
            frame.signature row = true,
          wanted ∈ eventual environment request
            (.arguments (rowArguments { frame with cursor := cursor } row found checked)) := by
  cases rowFound : environment.provider.rows[frame.cursor]? with
  | none =>
    rw [eventual_rows_none environment request frame rowFound] at member
    cases member
  | some row =>
    have within : frame.cursor < environment.provider.rows.length :=
      (List.getElem?_eq_some_iff.mp rowFound).1
    rw [eventual_rows_some environment request frame rowFound] at member
    rcases List.mem_append.mp member with here | later
    · split at here
      · rename_i checked
        have same := eventual_rowIndex environment request _ (index := frame.cursor) rfl wanted here
        refine ⟨by omega, ?_⟩
        intro cursor atCursor
        have cursorEq : cursor = frame.cursor := by omega
        subst cursorEq
        exact ⟨row, rowFound, checked, here⟩
      · cases here
    · have next := eventual_rows_locate environment request frame.next wanted later
      exact ⟨by simp only [RowsFrame.next] at next; omega, next.2⟩
termination_by environment.provider.rows.length - frame.cursor
decreasing_by
  simp only [RowsFrame.next]
  omega

/-- **Each certified answer lies in its own row's argument task.** -/
theorem mem_rowArguments (environment : Environment) (request : Request) {signature : Signature}
    (found : signature? environment.provider request.relation request.arguments.length = some signature)
    (wanted : Answer environment request) (finite : wanted.rowIndex < environment.provider.rows.length) :
    ∃ row, ∃ rowFound : environment.provider.rows[wanted.rowIndex]? = some row,
      ∃ checked : checkRow environment.language environment.free request.context.bound signature row = true,
        wanted ∈ eventual environment request
          (.arguments (rowArguments ⟨signature, found, wanted.rowIndex⟩ row rowFound checked)) := by
  have accepted : TaskAccepts environment request (.rows ⟨signature, found, 0⟩) wanted :=
    ⟨Nat.zero_le _, finite, wanted.valid⟩
  have member := (mem_eventual_iff environment request (.rows ⟨signature, found, 0⟩) wanted trivial).mpr accepted
  exact (eventual_rows_locate environment request ⟨signature, found, 0⟩ wanted member).2 _ rfl

/-! ## First-order rows contribute at most one answer -/

/-- Retained work whose remaining argument schemas are first-order and whose
matcher is deterministic. -/
def TaskDeterministic {environment : Environment} {request : Request} : Task environment request → Prop
  | .arguments frame => ∀ schema ∈ frame.schemas, FirstOrder schema
  | .matcher frame => GeneralScopedMatchMachine.Deterministic frame.state ∧
      ∀ schema ∈ frame.schemas, FirstOrder schema
  | _ => False

/-- The number of answers a deterministic task can still emit. -/
def Task.answerBound {environment : Environment} {request : Request} : Task environment request → Nat
  | .arguments _ => 1
  | .matcher frame => (frame.state.answers.length - frame.cursor) + frame.state.agenda.length
  | _ => 0

theorem expand_deterministic (environment : Environment) (request : Request)
    {task : Task environment request} (deterministic : TaskDeterministic task) :
    (expand environment request task).answers.length +
        ((expand environment request task).tasks.map Task.answerBound).sum ≤ task.answerBound ∧
      ∀ branch ∈ (expand environment request task).tasks, TaskDeterministic branch := by
  cases task with
  | start => exact deterministic.elim
  | rows => exact deterministic.elim
  | dynamicInputs => exact deterministic.elim
  | dynamicRows => exact deterministic.elim
  | arguments frame =>
    simp only [expand]
    unfold expandArguments
    split
    · split <;> simp [Task.answerBound]
    · rename_i schema schemas value values mode modes schemasFound _ _
      have head : FirstOrder schema := deterministic schema (by simp [schemasFound])
      have rest : ∀ later ∈ schemas, FirstOrder later :=
        fun later member => deterministic later (by simp [schemasFound, member])
      cases mode with
      | input =>
        dsimp only
        split
        · simp [Task.answerBound]
        · split
          · refine ⟨by simp [Task.answerBound], ?_⟩
            intro branch member
            simp only [List.mem_singleton] at member
            subst member
            exact rest
          · simp [Task.answerBound]
      | output =>
        dsimp only
        refine ⟨by simp [Task.answerBound, GeneralScopedMatchMachine.start], ?_⟩
        intro branch member
        simp only [List.mem_singleton] at member
        subst member
        exact ⟨GeneralScopedMatchMachine.start_deterministic head, rest⟩
    · simp [Task.answerBound]
  | matcher frame =>
    obtain ⟨machine, shapes⟩ := deterministic
    simp only [expand]
    unfold expandMatcher
    split
    · rename_i answer found
      have within : frame.cursor < frame.state.answers.length := (List.getElem?_eq_some_iff.mp found).1
      refine ⟨by simp only [Task.answerBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_nil]; omega, ?_⟩
      intro branch member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact shapes
      · exact ⟨machine, shapes⟩
    · rename_i missing
      have consumed : frame.state.answers.length ≤ frame.cursor := List.getElem?_eq_none_iff.mp missing
      split
      · simp [Task.answerBound]
      · rename_i pending
        have pending' : GeneralScopedMatchMachine.complete frame.state = false := Bool.eq_false_iff.mpr pending
        have nonempty : frame.state.agenda ≠ [] := by
          intro empty
          simp [GeneralScopedMatchMachine.complete, empty] at pending'
        have agendaPositive : 0 < frame.state.agenda.length := List.length_pos_iff.mpr nonempty
        have ticked := GeneralScopedMatchMachine.tick_deterministic frame.query ⟨machine.1, machine.2⟩
        refine ⟨?_, ?_⟩
        · simp only [Task.answerBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            List.length_nil]
          have := machine.1
          have := ticked.1
          omega
        · intro branch member
          simp only [List.mem_singleton] at member
          subst member
          exact ⟨ticked, shapes⟩

private theorem sum_map_le {α : Type} (items : List α) (small large : α → Nat)
    (pointwise : ∀ item ∈ items, small item ≤ large item) :
    (items.map small).sum ≤ (items.map large).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have here := pointwise item (List.mem_cons_self ..)
    have later := ih (fun other member => pointwise other (List.mem_cons_of_mem _ member))
    omega

theorem eventual_length_le (environment : Environment) (request : Request)
    (task : Task environment request) (deterministic : TaskDeterministic task) :
    (eventual environment request task).length ≤ task.answerBound := by
  rw [eventual_eq, List.length_append, List.length_flatMap]
  obtain ⟨bound, branches⟩ := expand_deterministic environment request deterministic
  have each := sum_map_le (expand environment request task).tasks
    (fun branch => (eventual environment request branch).length) Task.answerBound
    (fun branch member => eventual_length_le environment request branch (branches branch member))
  omega
termination_by task.rank environment request
decreasing_by exact expand_decreases environment request task branch member

/-- **A row with first-order argument schemas contributes at most one answer.** -/
theorem eventual_arguments_length_le_one (environment : Environment) (request : Request)
    (frame : ArgumentsFrame environment request) (shapes : ∀ schema ∈ frame.schemas, FirstOrder schema) :
    (eventual environment request (.arguments frame)).length ≤ 1 :=
  eventual_length_le environment request (.arguments frame) shapes

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
