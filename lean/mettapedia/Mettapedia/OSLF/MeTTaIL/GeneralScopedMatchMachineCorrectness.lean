import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-!
# Scoped matcher continuation correctness

Independent tree derivations give meaning to pending tasks. The state
invariant accounts jointly for already emitted answers and unfinished work,
so every suspension retains exactly the complete traced search space.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

inductive TaskRuns (request : Request) :
    Assignment → Task → List BagChoice → Assignment → Prop where
  | tree {initial path depth schema target trace final} :
      TracedMatches request.rule request.spec request.ambient request.site path depth
        initial schema target trace final →
      TaskRuns request initial (.tree path depth schema target) trace final
  | arguments {initial path depth index schemas targets trace final} :
      TracedArguments request.rule request.spec request.ambient request.site path depth
        initial index schemas targets trace final →
      TaskRuns request initial (.arguments path depth index schemas targets) trace final
  | bag {initial path depth index schemas rest kind targets trace final} :
      TracedBag request.rule request.spec request.ambient request.site path depth
        initial index schemas rest kind targets trace final →
      TaskRuns request initial (.bag path depth index schemas rest kind targets) trace final
  | bagSelect {initial path depth index schema schemas rest kind targets cursor
      middle final headTrace tailTrace} (selected : Nat) :
      cursor ≤ selected → (within : selected < targets.length) →
      TracedMatches request.rule request.spec request.ambient request.site (path ++ [index]) depth
        initial schema targets[selected] headTrace middle →
      TracedBag request.rule request.spec request.ambient request.site path depth
        middle (index + 1) schemas rest kind (targets.eraseIdx selected) tailTrace final →
      TaskRuns request initial (.bagSelect path depth index schema schemas rest kind targets cursor)
        ({ path := path ++ [index], selected } :: (headTrace ++ tailTrace)) final
  | restCapture {initial path depth name kind targets final} :
      captureRest? request.rule request.spec request.ambient depth request.site path initial name kind targets =
        some final → TaskRuns request initial (.restCapture path depth name kind targets) [] final

inductive TasksRun (request : Request) :
    Assignment → List Task → List BagChoice → Assignment → Prop where
  | nil {initial} : TasksRun request initial [] [] initial
  | cons {initial task tasks headTrace tailTrace middle final} :
      TaskRuns request initial task headTrace middle →
      TasksRun request middle tasks tailTrace final →
      TasksRun request initial (task :: tasks) (headTrace ++ tailTrace) final

def WorkAccepts (request : Request) (work : Work) (answer : Answer) : Prop :=
  ∃ suffix, TasksRun request work.assignment work.tasks suffix answer.assignment ∧
    answer.trace = work.trace ++ suffix

theorem TaskRuns.tree_iff {request : Request} {initial final : Assignment}
    {path : List Nat} {depth : Nat} {schema target : Pattern} {trace : List BagChoice} :
    TaskRuns request initial (.tree path depth schema target) trace final ↔
      TracedMatches request.rule request.spec request.ambient request.site path depth
        initial schema target trace final := by
  constructor
  · intro run
    cases run with | tree matched => exact matched
  · exact TaskRuns.tree

theorem TaskRuns.arguments_iff {request : Request} {initial final : Assignment}
    {path : List Nat} {depth index : Nat} {schemas targets : List Pattern} {trace : List BagChoice} :
    TaskRuns request initial (.arguments path depth index schemas targets) trace final ↔
      TracedArguments request.rule request.spec request.ambient request.site path depth
        initial index schemas targets trace final := by
  constructor
  · intro run
    cases run with | arguments matched => exact matched
  · exact TaskRuns.arguments

theorem TaskRuns.bag_iff {request : Request} {initial final : Assignment}
    {path : List Nat} {depth index : Nat} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType} {trace : List BagChoice} :
    TaskRuns request initial (.bag path depth index schemas rest kind targets) trace final ↔
      TracedBag request.rule request.spec request.ambient request.site path depth
        initial index schemas rest kind targets trace final := by
  constructor
  · intro run
    cases run with | bag matched => exact matched
  · exact TaskRuns.bag

theorem TaskRuns.restCapture_iff {request : Request} {initial final : Assignment}
    {path : List Nat} {depth : Nat} {name : String} {kind : CollType}
    {targets : List Pattern} {trace : List BagChoice} :
    TaskRuns request initial (.restCapture path depth name kind targets) trace final ↔
      trace = [] ∧
        captureRest? request.rule request.spec request.ambient depth request.site path initial name kind targets =
          some final := by
  constructor
  · intro run
    cases run with | restCapture captured => exact ⟨rfl, captured⟩
  · rintro ⟨rfl, captured⟩
    exact .restCapture captured

theorem TasksRun.nil_iff {request : Request} {initial final : Assignment} {trace : List BagChoice} :
    TasksRun request initial [] trace final ↔ trace = [] ∧ final = initial := by
  constructor
  · intro run
    cases run
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .nil

theorem TasksRun.singleton_iff {request : Request} {initial final : Assignment}
    {task : Task} {trace : List BagChoice} :
    TasksRun request initial [task] trace final ↔ TaskRuns request initial task trace final := by
  constructor
  · intro run
    cases run with
    | cons head tail =>
      cases tail
      simpa only [List.append_nil] using head
  · intro head
    simpa only [List.append_nil] using TasksRun.cons head TasksRun.nil

theorem TasksRun.append {request : Request} {initial middle final : Assignment}
    {before after : List Task} {first second : List BagChoice}
    (front : TasksRun request initial before first middle)
    (back : TasksRun request middle after second final) :
    TasksRun request initial (before ++ after) (first ++ second) final := by
  induction front with
  | nil => exact back
  | cons head tail ih =>
    simpa only [List.cons_append, List.append_assoc] using TasksRun.cons head (ih back)

theorem TasksRun.append_iff {request : Request} {initial final : Assignment}
    {before after : List Task} {trace : List BagChoice} :
    TasksRun request initial (before ++ after) trace final ↔
      ∃ middle first second, TasksRun request initial before first middle ∧
        TasksRun request middle after second final ∧ trace = first ++ second := by
  constructor
  · intro run
    induction before generalizing initial trace with
    | nil => exact ⟨initial, [], trace, .nil, run, rfl⟩
    | cons task tasks ih =>
      cases run with
      | cons head tail =>
        obtain ⟨middle, first, second, front, back, same⟩ := ih tail
        exact ⟨middle, _ ++ first, second, .cons head front, back,
          by simp only [same, List.append_assoc]⟩
  · rintro ⟨middle, first, second, front, back, rfl⟩
    exact front.append back

theorem TasksRun.pair_iff {request : Request} {initial final : Assignment}
    {head tail : Task} {trace : List BagChoice} :
    TasksRun request initial [head, tail] trace final ↔
      ∃ middle first second, TaskRuns request initial head first middle ∧
        TaskRuns request middle tail second final ∧ trace = first ++ second := by
  constructor
  · intro run
    cases run with
    | cons head tail => exact ⟨_, _, _, head, TasksRun.singleton_iff.mp tail, rfl⟩
  · rintro ⟨middle, first, second, head, tail, rfl⟩
    exact .cons head (TasksRun.singleton_iff.mpr tail)

theorem workAccepts_empty {request : Request} {initial : Assignment} {history : List BagChoice}
    {answer : Answer} :
    WorkAccepts request { assignment := initial, tasks := [], trace := history } answer ↔
      answer.assignment = initial ∧ answer.trace = history := by
  constructor
  · rintro ⟨suffix, run, same⟩
    obtain ⟨rfl, final⟩ := TasksRun.nil_iff.mp run
    exact ⟨final, by simpa only [List.append_nil] using same⟩
  · rintro ⟨final, same⟩
    exact ⟨[], final ▸ TasksRun.nil, by simpa only [List.append_nil] using same⟩

theorem workAccepts_singleton {request : Request} {initial : Assignment}
    {history : List BagChoice} {task : Task} {answer : Answer} :
    WorkAccepts request { assignment := initial, tasks := [task], trace := history } answer ↔
      ∃ suffix, TaskRuns request initial task suffix answer.assignment ∧
        answer.trace = history ++ suffix := by
  simp only [WorkAccepts, TasksRun.singleton_iff]

theorem workAccepts_pair {request : Request} {initial : Assignment}
    {history : List BagChoice} {head tail : Task} {answer : Answer} :
    WorkAccepts request { assignment := initial, tasks := [head, tail], trace := history } answer ↔
      ∃ middle first second, TaskRuns request initial head first middle ∧
        TaskRuns request middle tail second answer.assignment ∧ answer.trace = history ++ (first ++ second) := by
  constructor
  · rintro ⟨suffix, run, same⟩
    obtain ⟨middle, first, second, head, tail, rfl⟩ := TasksRun.pair_iff.mp run
    exact ⟨middle, first, second, head, tail, same⟩
  · rintro ⟨middle, first, second, head, tail, same⟩
    exact ⟨first ++ second, TasksRun.pair_iff.mpr ⟨middle, first, second, head, tail, rfl⟩, same⟩

theorem expand_complete {request : Request} {initial final : Assignment}
    {task : Task} {trace : List BagChoice} (run : TaskRuns request initial task trace final) :
    ∃ branch ∈ expand request initial task,
      WorkAccepts request branch { assignment := final, trace } := by
  cases run with
  | tree matched =>
    cases matched with
    | capture captured =>
      refine ⟨_, ?_, workAccepts_empty.mpr ⟨rfl, rfl⟩⟩
      simp only [expand, captured, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton]
    | bound =>
      refine ⟨_, ?_, workAccepts_empty.mpr ⟨rfl, rfl⟩⟩
      simp only [expand, ↓reduceIte, List.mem_singleton]
    | constructor arguments =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr ⟨_, .arguments arguments, rfl⟩⟩
      simp only [expand, ↓reduceIte, List.mem_singleton]
    | binder body =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr ⟨_, .tree body, rfl⟩⟩
      simp only [expand, List.mem_singleton]
    | binders body =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr ⟨_, .tree body, rfl⟩⟩
      simp only [expand, ↓reduceIte, List.mem_singleton]
    | substitution body replacement =>
      refine ⟨_, ?_, (workAccepts_pair (history := [])).mpr ⟨_, _, _, .tree body, .tree replacement, rfl⟩⟩
      simp only [expand, List.mem_singleton]
    | bag notVector bag =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr ⟨_, .bag bag, rfl⟩⟩
      simp only [expand, notVector, true_and, ↓reduceIte, List.mem_singleton]
    | vector arguments =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr ⟨_, .arguments arguments, rfl⟩⟩
      simp only [expand, true_and, ↓reduceIte, List.mem_singleton]
    | vectorRest arguments captured =>
      refine ⟨_, ?_, (workAccepts_pair (history := [])).mpr ⟨_, _, [], .arguments arguments, .restCapture captured, ?_⟩⟩
      · simp only [expand, true_and, ↓reduceIte, List.mem_singleton]
      · simp only [List.append_nil, List.nil_append]
  | arguments matched =>
    cases matched with
    | nil =>
      refine ⟨_, ?_, workAccepts_empty.mpr ⟨rfl, rfl⟩⟩
      simp only [expand, List.mem_singleton]
    | cons head tail =>
      refine ⟨_, ?_, (workAccepts_pair (history := [])).mpr ⟨_, _, _, .tree head, .arguments tail, rfl⟩⟩
      simp only [expand, List.mem_singleton]
  | bag matched =>
    cases matched with
    | nil =>
      refine ⟨_, ?_, workAccepts_empty.mpr ⟨rfl, rfl⟩⟩
      simp only [expand, ↓reduceIte, List.mem_singleton]
    | rest captured =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr ⟨[], .restCapture captured, rfl⟩⟩
      simp only [expand, List.mem_singleton]
    | cons selected within head tail =>
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr
        ⟨_, .bagSelect selected (Nat.zero_le _) within head tail, rfl⟩⟩
      simp only [expand, List.mem_singleton]
  | @bagSelect path depth index schema schemas rest kind targets cursor
      middle final headTrace tailTrace selected eligible within head tail =>
    by_cases same : cursor = selected
    · subst cursor
      refine ⟨_, ?_, (workAccepts_pair (history := [{ path := path ++ [index], selected }])).mpr
        ⟨middle, headTrace, tailTrace, .tree head, .bag tail, rfl⟩⟩
      simp only [expand, List.getElem?_eq_getElem within, List.mem_cons]
      exact .inl True.intro
    · have cursorWithin : cursor < targets.length := lt_of_le_of_lt eligible within
      refine ⟨_, ?_, (workAccepts_singleton (history := [])).mpr
        ⟨_, .bagSelect (cursor := cursor + 1) selected (by omega) within head tail, rfl⟩⟩
      simp only [expand, List.getElem?_eq_getElem cursorWithin, List.mem_cons]
      exact .inr (.inl True.intro)
  | restCapture captured =>
    refine ⟨_, ?_, workAccepts_empty.mpr ⟨rfl, rfl⟩⟩
    simp only [expand, captured, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton]

theorem expand_sound {request : Request} {initial : Assignment} {task : Task}
    {branch : Work} {answer : Answer} (member : branch ∈ expand request initial task)
    (accepted : WorkAccepts request branch answer) :
    TaskRuns request initial task answer.trace answer.assignment := by
  cases task with
  | tree path depth schema target =>
    cases schema with
    | fvar name =>
      obtain ⟨final, captured, same⟩ := List.mem_map.mp member
      subst branch
      obtain ⟨finalEq, traceEq⟩ := workAccepts_empty.mp accepted
      rw [finalEq, traceEq]
      exact .tree (.capture (Option.mem_toList.mp captured))
    | bvar expected =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      next equal =>
        subst_vars
        simp only [List.mem_singleton] at member
        subst branch
        obtain ⟨finalEq, traceEq⟩ := workAccepts_empty.mp accepted
        rw [finalEq, traceEq]
        exact .tree .bound
      next => contradiction
    | apply label schemas =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      next equal =>
        subst_vars
        simp only [List.mem_singleton] at member
        subst branch
        obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
        simp only [List.nil_append] at same
        rw [same]
        exact .tree (.constructor (TaskRuns.arguments_iff.mp next))
      next => contradiction
    | lambda display body =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      simp only [List.mem_singleton] at member
      subst branch
      obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
      simp only [List.nil_append] at same
      rw [same]
      exact .tree (.binder (TaskRuns.tree_iff.mp next))
    | multiLambda arity display body =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      next equal =>
        subst_vars
        simp only [List.mem_singleton] at member
        subst branch
        obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
        simp only [List.nil_append] at same
        rw [same]
        exact .tree (.binders (TaskRuns.tree_iff.mp next))
      next => contradiction
    | subst body replacement =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      simp only [List.mem_singleton] at member
      subst branch
      obtain ⟨middle, first, second, front, back, same⟩ := workAccepts_pair.mp accepted
      simp only [List.nil_append] at same
      rw [same]
      exact .tree (.substitution (TaskRuns.tree_iff.mp front) (TaskRuns.tree_iff.mp back))
    | collection kind schemas rest =>
      cases target <;> simp only [expand] at member
      all_goals try contradiction
      split at member
      next conditions =>
        obtain ⟨kindEq, restEq⟩ := conditions
        subst_vars
        split at member
        next vector =>
          subst_vars
          cases rest with
          | none =>
            simp only [List.mem_singleton] at member
            subst branch
            obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
            simp only [List.nil_append] at same
            rw [same]
            exact .tree (.vector (TaskRuns.arguments_iff.mp next))
          | some name =>
            simp only [List.mem_singleton] at member
            subst branch
            obtain ⟨middle, first, second, front, back, same⟩ := workAccepts_pair.mp accepted
            obtain ⟨rfl, captured⟩ := TaskRuns.restCapture_iff.mp back
            simp only [List.nil_append, List.append_nil] at same
            rw [same]
            exact .tree (.vectorRest (TaskRuns.arguments_iff.mp front) captured)
        next notVector =>
          simp only [List.mem_singleton] at member
          subst branch
          obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
          simp only [List.nil_append] at same
          rw [same]
          exact .tree (.bag notVector (TaskRuns.bag_iff.mp next))
      next => contradiction
  | arguments path depth index schemas targets =>
    cases schemas with
    | nil =>
      cases targets <;> simp only [expand] at member
      · simp only [List.mem_singleton] at member
        subst branch
        obtain ⟨finalEq, traceEq⟩ := workAccepts_empty.mp accepted
        rw [finalEq, traceEq]
        exact .arguments .nil
      · contradiction
    | cons schema schemas =>
      cases targets <;> simp only [expand] at member
      · contradiction
      · simp only [List.mem_singleton] at member
        subst branch
        obtain ⟨middle, first, second, front, back, same⟩ := workAccepts_pair.mp accepted
        simp only [List.nil_append] at same
        rw [same]
        exact .arguments (.cons (TaskRuns.tree_iff.mp front) (TaskRuns.arguments_iff.mp back))
  | bag path depth index schemas rest kind targets =>
    cases schemas with
    | nil =>
      cases rest with
      | none =>
        simp only [expand] at member
        split at member
        next empty =>
          subst targets
          simp only [List.mem_singleton] at member
          subst branch
          obtain ⟨finalEq, traceEq⟩ := workAccepts_empty.mp accepted
          rw [finalEq, traceEq]
          exact .bag .nil
        next => contradiction
      | some name =>
        simp only [expand, List.mem_singleton] at member
        subst branch
        obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
        obtain ⟨rfl, captured⟩ := TaskRuns.restCapture_iff.mp next
        simp only [List.nil_append] at same
        rw [same]
        exact .bag (.rest captured)
    | cons schema schemas =>
      simp only [expand, List.mem_singleton] at member
      subst branch
      obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
      simp only [List.nil_append] at same
      rw [same]
      cases next with
      | bagSelect selected _ within head tail => exact .bag (.cons selected within head tail)
  | bagSelect path depth index schema schemas rest kind targets cursor =>
    cases found : targets[cursor]? with
    | none => simp only [expand, found, List.not_mem_nil] at member
    | some target =>
      have within := (List.getElem?_eq_some_iff.mp found).1
      have targetEq : target = targets[cursor] :=
        Option.some.inj (found.symm.trans (List.getElem?_eq_getElem within))
      simp only [expand, found, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst branch
      · obtain ⟨middle, first, second, front, back, same⟩ := workAccepts_pair.mp accepted
        rw [same]
        exact .bagSelect (middle := middle) (headTrace := first) (tailTrace := second) cursor (Nat.le_refl _) within
          (by simpa only [targetEq] using TaskRuns.tree_iff.mp front) (TaskRuns.bag_iff.mp back)
      · obtain ⟨suffix, next, same⟩ := workAccepts_singleton.mp accepted
        simp only [List.nil_append] at same
        rw [same]
        cases next with
        | bagSelect selected eligible within head tail =>
          exact .bagSelect selected (by omega) within head tail
  | restCapture path depth name kind targets =>
    obtain ⟨final, captured, same⟩ := List.mem_map.mp member
    subst branch
    obtain ⟨finalEq, traceEq⟩ := workAccepts_empty.mp accepted
    rw [finalEq, traceEq]
    exact .restCapture (Option.mem_toList.mp captured)

theorem advance_accepts_iff (request : Request) (work : Work) (answer : Answer)
    (pending : work.tasks ≠ []) :
    (∃ branch ∈ advance request work, WorkAccepts request branch answer) ↔
      WorkAccepts request work answer := by
  cases work with
  | mk initial tasks history =>
    cases tasks with
    | nil => exact False.elim (pending rfl)
    | cons task tasks =>
      constructor
      · rintro ⟨branch, member, suffix, run, same⟩
        simp only [advance, List.mem_map] at member
        obtain ⟨expanded, generated, branchEq⟩ := member
        subst branch
        obtain ⟨middle, first, second, front, back, suffixEq⟩ := TasksRun.append_iff.mp run
        have head := expand_sound generated
          (show WorkAccepts request expanded { assignment := middle, trace := expanded.trace ++ first } from
            ⟨first, front, rfl⟩)
        refine ⟨(expanded.trace ++ first) ++ second, .cons head back, ?_⟩
        simpa only [suffixEq, List.append_assoc] using same
      · rintro ⟨suffix, run, same⟩
        cases run with
        | cons head tail =>
          obtain ⟨expanded, generated, extension, front, headEq⟩ := expand_complete head
          dsimp only at headEq
          refine ⟨{ assignment := expanded.assignment, tasks := expanded.tasks ++ tasks, trace := history ++ expanded.trace },
            ?_, extension ++ _, front.append tail, ?_⟩
          · exact List.mem_map.mpr ⟨expanded, generated, rfl⟩
          · simpa only [headEq, List.append_assoc] using same

theorem workAccepts_nil_iff {request : Request} {work : Work} {answer : Answer}
    (empty : work.tasks = []) :
    WorkAccepts request work answer ↔
      answer = { assignment := work.assignment, trace := work.trace } := by
  cases work with
  | mk initial tasks history =>
    dsimp only at empty
    subst tasks
    constructor
    · intro accepted
      obtain ⟨assignmentEq, traceEq⟩ := workAccepts_empty.mp accepted
      cases answer
      dsimp only at assignmentEq traceEq
      subst_vars
      rfl
    · intro same
      subst answer
      exact workAccepts_empty.mpr ⟨rfl, rfl⟩

def StateAccepts (request : Request) (state : State) (answer : Answer) : Prop :=
  answer ∈ state.answers ∨ ∃ work ∈ state.agenda, WorkAccepts request work answer

theorem tick_accepts_iff (request : Request) (state : State) (answer : Answer) :
    StateAccepts request (tick request state) answer ↔ StateAccepts request state answer := by
  cases agendaEq : state.agenda with
  | nil => simp only [tick, agendaEq]
  | cons work agenda =>
    cases tasksEq : work.tasks with
    | nil =>
      simp only [StateAccepts, tick, agendaEq, tasksEq]
      change (answer ∈ state.answers ++ [{ assignment := work.assignment, trace := work.trace }] ∨
        ∃ branch ∈ agenda, WorkAccepts request branch answer) ↔
        (answer ∈ state.answers ∨ ∃ branch ∈ work :: agenda, WorkAccepts request branch answer)
      constructor
      · rintro (emitted | ⟨branch, member, accepted⟩)
        · rcases List.mem_append.mp emitted with old | fresh
          · exact .inl old
          · have same := List.mem_singleton.mp fresh
            exact .inr ⟨work, List.mem_cons_self, (workAccepts_nil_iff tasksEq).mpr same⟩
        · exact .inr ⟨branch, List.mem_cons_of_mem _ member, accepted⟩
      · rintro (emitted | ⟨branch, member, accepted⟩)
        · exact .inl (List.mem_append_left _ emitted)
        · rcases List.mem_cons.mp member with same | later
          · subst branch
            exact .inl (List.mem_append_right _ (List.mem_singleton.mpr
              ((workAccepts_nil_iff tasksEq).mp accepted)))
          · exact .inr ⟨branch, later, accepted⟩
    | cons task tasks =>
      simp only [StateAccepts, tick, agendaEq, tasksEq]
      change (answer ∈ state.answers ∨
        ∃ branch ∈ advance request work ++ agenda, WorkAccepts request branch answer) ↔
        (answer ∈ state.answers ∨ ∃ branch ∈ work :: agenda, WorkAccepts request branch answer)
      have pending : work.tasks ≠ [] := by rw [tasksEq]; exact List.cons_ne_nil _ _
      constructor
      · rintro (emitted | ⟨branch, member, accepted⟩)
        · exact .inl emitted
        · rcases List.mem_append.mp member with generated | later
          · exact .inr ⟨work, List.mem_cons_self,
              (advance_accepts_iff request work answer pending).mp ⟨branch, generated, accepted⟩⟩
          · exact .inr ⟨branch, List.mem_cons_of_mem _ later, accepted⟩
      · rintro (emitted | ⟨branch, member, accepted⟩)
        · exact .inl emitted
        · rcases List.mem_cons.mp member with same | later
          · subst branch
            obtain ⟨generated, member, accepted⟩ :=
              (advance_accepts_iff request work answer pending).mpr accepted
            exact .inr ⟨generated, List.mem_append_left _ member, accepted⟩
          · exact .inr ⟨branch, List.mem_append_right _ later, accepted⟩

theorem start_accepts_iff (request : Request) (answer : Answer) :
    StateAccepts request (start request) answer ↔ answer.Valid request := by
  simp only [StateAccepts, start, List.not_mem_nil, false_or, List.mem_singleton,
    exists_eq_left, workAccepts_singleton, List.nil_append]
  constructor
  · rintro ⟨suffix, run, same⟩
    unfold Answer.Valid
    rw [same]
    exact TaskRuns.tree_iff.mp run
  · intro valid
    exact ⟨answer.trace, .tree valid, rfl⟩

theorem state_accepts_iff {request : Request} {state : State}
    (reached : Reachable request state) (answer : Answer) :
    StateAccepts request state answer ↔ answer.Valid request := by
  induction reached with
  | start => exact start_accepts_iff request answer
  | tick reached ih => rw [tick_accepts_iff]; exact ih

theorem answers_sound {request : Request} {state : State} (reached : Reachable request state)
    {answer : Answer} (member : answer ∈ state.answers) : answer.Valid request :=
  (state_accepts_iff reached answer).mp (.inl member)

theorem answers_complete {request : Request} {state : State} (reached : Reachable request state)
    (finished : complete state = true) {answer : Answer} (valid : answer.Valid request) :
    answer ∈ state.answers := by
  have empty : state.agenda = [] := List.isEmpty_iff.mp finished
  rcases (state_accepts_iff reached answer).mpr valid with member | ⟨work, member, _⟩
  · exact member
  · simp only [empty, List.not_mem_nil] at member

theorem complete_answers_iff {request : Request} {state : State} (reached : Reachable request state)
    (finished : complete state = true) (answer : Answer) :
    answer ∈ state.answers ↔ answer.Valid request :=
  ⟨answers_sound reached, answers_complete reached finished⟩

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching
open GeneralScopedMatch

theorem matcher_answer_free_within (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) (reached : GeneralScopedMatchMachine.Reachable request state)
    (answer : GeneralScopedMatchMachine.Answer) (member : answer ∈ state.answers)
    (footprint : List String) (before : assignmentFreeWithin footprint request.initial)
    (covered : ∀ name ∈ request.target.freeFvarNames, name ∈ footprint) :
    assignmentFreeWithin footprint answer.assignment :=
  matched_free_within (GeneralScopedMatchMachine.answers_sound reached member).matching footprint before covered

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.matcher_answer_free_within

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

/-! ## Exact ordered projection of completed matching -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

/-- A proof denotation of original machine tasks in the existing recursive matching APIs. -/
def taskAssignments (request : Request) (initial : Assignment) : Task → List Assignment
  | .tree path depth schema target =>
      matchAt request.rule request.spec request.ambient request.site path depth initial schema target
  | .arguments path depth index schemas targets =>
      matchArgsAt request.rule request.spec request.ambient request.site path depth initial index schemas targets
  | .bag path depth index schemas rest kind targets =>
      matchBagAt request.rule request.spec request.ambient request.site path depth initial index schemas rest kind targets
  | .bagSelect path depth index schema schemas rest kind targets selected =>
      (targets.zipIdx.drop selected).flatMap fun (target, physical) =>
        (matchAt request.rule request.spec request.ambient request.site (path ++ [index]) depth
          initial schema target).flatMap fun found =>
            matchBagAt request.rule request.spec request.ambient request.site path depth found (index + 1)
              schemas rest kind (targets.eraseIdx physical)
  | .restCapture path depth name kind targets =>
      (captureRest? request.rule request.spec request.ambient depth request.site path initial name kind targets).toList

def tasksAssignments (request : Request) (initial : Assignment) : List Task → List Assignment
  | [] => [initial]
  | task :: tasks => (taskAssignments request initial task).flatMap fun found => tasksAssignments request found tasks

def workAssignments (request : Request) (work : Work) : List Assignment :=
  tasksAssignments request work.assignment work.tasks

def stateAssignments (request : Request) (state : State) : List Assignment :=
  state.answers.map (·.assignment) ++ state.agenda.flatMap (workAssignments request)

theorem choice_cursor_step {targets : List Pattern} {selected : Nat} {target : Pattern}
    (found : targets[selected]? = some target) :
    targets.zipIdx.drop selected = (target, selected) :: targets.zipIdx.drop (selected + 1) := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  have bounded : selected < targets.zipIdx.length := by simpa using within
  rw [List.drop_eq_getElem_cons bounded, List.getElem_zipIdx]
  simp only [Nat.zero_add, same]

theorem choice_cursor_exhausted {targets : List Pattern} {selected : Nat}
    (absent : targets[selected]? = none) : targets.zipIdx.drop selected = [] := by
  apply List.drop_eq_nil_of_le
  simpa using List.getElem?_eq_none_iff.mp absent

private theorem flatMap_singleton {α : Type} (values : List α) :
    values.flatMap (fun value => [value]) = values := by simp

@[simp] private theorem captured_work_assignments (request : Request) (found : Option Assignment) :
    (found.toList.map fun final => ({ assignment := final, tasks := [] } : Work)).flatMap
      (workAssignments request) = found.toList := by
  cases found <;> rfl

theorem tree_expansion_assignments (request : Request) (initial : Assignment)
    (path : List Nat) (depth : Nat) (schema target : Pattern) :
    taskAssignments request initial (.tree path depth schema target) =
      (expand request initial (.tree path depth schema target)).flatMap (workAssignments request) := by
  cases schema <;> cases target
  case collection.collection kind schemas rest actualKind targets actualRest =>
    cases kind <;> cases actualKind <;> cases rest <;> cases actualRest <;>
      simp [taskAssignments, expand, workAssignments, tasksAssignments,
        matchAt, matchArgsAt, matchBagAt, matchAtWith, List.filterMap_eq_flatMap_toList]
  all_goals simp only [taskAssignments, expand, matchAt, matchAtWith, captureWith?_literal,
    beq_iff_eq, captured_work_assignments]
  all_goals try split_ifs
  all_goals simp [workAssignments, tasksAssignments, taskAssignments, matchAt, matchArgsAt]

theorem arguments_expansion_assignments (request : Request) (initial : Assignment)
    (path : List Nat) (depth index : Nat) (schemas targets : List Pattern) :
    taskAssignments request initial (.arguments path depth index schemas targets) =
      (expand request initial (.arguments path depth index schemas targets)).flatMap (workAssignments request) := by
  cases schemas <;> cases targets <;>
    simp [taskAssignments, expand, workAssignments, tasksAssignments, matchArgsAt, matchArgsAtWith, matchAt]

theorem bag_expansion_assignments (request : Request) (initial : Assignment)
    (path : List Nat) (depth index : Nat) (schemas : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern) :
    taskAssignments request initial (.bag path depth index schemas rest kind targets) =
      (expand request initial (.bag path depth index schemas rest kind targets)).flatMap (workAssignments request) := by
  cases schemas with
  | nil =>
      cases rest with
      | none =>
          cases targets <;>
            simp [taskAssignments, expand, workAssignments, tasksAssignments, matchBagAt, matchBagAtWith]
      | some name =>
          simp [taskAssignments, expand, workAssignments, tasksAssignments, matchBagAt, matchBagAtWith]
  | cons schema schemas =>
      simp [taskAssignments, expand, workAssignments, tasksAssignments, matchBagAt, matchBagAtWith, matchAt]

theorem bag_select_expansion_assignments (request : Request) (initial : Assignment)
    (path : List Nat) (depth index : Nat) (schema : Pattern) (schemas : List Pattern)
    (rest : Option String) (kind : CollType) (targets : List Pattern) (selected : Nat) :
    taskAssignments request initial (.bagSelect path depth index schema schemas rest kind targets selected) =
      (expand request initial (.bagSelect path depth index schema schemas rest kind targets selected)).flatMap
        (workAssignments request) := by
  cases found : targets[selected]? with
  | none =>
      simp only [taskAssignments, expand, found, choice_cursor_exhausted found, List.flatMap_nil]
  | some target =>
      simp [taskAssignments, expand, found, choice_cursor_step found, workAssignments, tasksAssignments]

theorem rest_capture_expansion_assignments (request : Request) (initial : Assignment)
    (path : List Nat) (depth : Nat) (name : String) (kind : CollType) (targets : List Pattern) :
    taskAssignments request initial (.restCapture path depth name kind targets) =
      (expand request initial (.restCapture path depth name kind targets)).flatMap (workAssignments request) := by
  simp only [taskAssignments, expand, captured_work_assignments]

theorem task_expansion_assignments (request : Request) (initial : Assignment) (task : Task) :
    taskAssignments request initial task =
      (expand request initial task).flatMap (workAssignments request) := by
  cases task with
  | tree path depth schema target => exact tree_expansion_assignments request initial path depth schema target
  | arguments path depth index schemas targets => exact arguments_expansion_assignments request initial path depth index schemas targets
  | bag path depth index schemas rest kind targets => exact bag_expansion_assignments request initial path depth index schemas rest kind targets
  | bagSelect path depth index schema schemas rest kind targets selected =>
      exact bag_select_expansion_assignments request initial path depth index schema schemas rest kind targets selected
  | restCapture path depth name kind targets => exact rest_capture_expansion_assignments request initial path depth name kind targets

theorem tasks_assignments_append (request : Request) (initial : Assignment) (left right : List Task) :
    tasksAssignments request initial (left ++ right) =
      (tasksAssignments request initial left).flatMap fun found => tasksAssignments request found right := by
  induction left generalizing initial with
  | nil => simp [tasksAssignments]
  | cons task tasks ih => simp only [List.cons_append, tasksAssignments, ih, List.flatMap_assoc]

theorem advance_assignments (request : Request) (work : Work) (pending : work.tasks ≠ []) :
    workAssignments request work = (advance request work).flatMap (workAssignments request) := by
  cases work with
  | mk initial tasks trace =>
      cases tasks with
      | nil => exact (pending rfl).elim
      | cons task tasks =>
          simp only [workAssignments, advance, tasksAssignments, List.flatMap_map]
          rw [task_expansion_assignments, List.flatMap_assoc]
          simp only [workAssignments, tasks_assignments_append]

theorem tick_assignments (request : Request) (state : State) :
    stateAssignments request (tick request state) = stateAssignments request state := by
  cases state with
  | mk agenda answers =>
      cases agenda with
      | nil => rfl
      | cons work agenda =>
          cases tasks : work.tasks with
          | nil =>
              simp [stateAssignments, tick, tasks, workAssignments, tasksAssignments, List.append_assoc]
          | cons task tasks =>
              have advanced := advance_assignments request work (by simp [tasks])
              simpa only [tick, tasks, stateAssignments, List.flatMap_cons, List.flatMap_append] using
                congrArg (fun pending => answers.map (·.assignment) ++
                  (pending ++ agenda.flatMap (workAssignments request))) advanced.symm

theorem run_assignments (request : Request) (fuel : Nat) (state : State) :
    stateAssignments request (run request fuel state) = stateAssignments request state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run]
      rw [ih, tick_assignments]

theorem start_assignments (request : Request) :
    stateAssignments request (start request) =
      matchAt request.rule request.spec request.ambient request.site request.path request.depth
        request.initial request.schema request.target := by
  simp [stateAssignments, start, workAssignments, tasksAssignments, taskAssignments]

theorem complete_assignments (request : Request) (state : State) (finished : complete state = true) :
    stateAssignments request state = state.answers.map (·.assignment) := by
  have empty : state.agenda = [] := List.isEmpty_iff.mp finished
  simp [stateAssignments, empty]

/-- Completed execution agrees as an exact list, preserving physical choice multiplicity and order. -/
theorem completed_run_assignments (request : Request) (fuel : Nat)
    (finished : complete (run request fuel (start request)) = true) :
    (run request fuel (start request)).answers.map (·.assignment) =
      matchAt request.rule request.spec request.ambient request.site request.path request.depth
        request.initial request.schema request.target := by
  rw [← complete_assignments request (run request fuel (start request)) finished,
    run_assignments, start_assignments]

theorem completed_run_exists (request : Request) :
    ∃ fuel : Nat, complete (run request fuel (start request)) = true ∧
      (run request fuel (start request)).answers.map (·.assignment) =
        matchAt request.rule request.spec request.ambient request.site request.path request.depth
          request.initial request.schema request.target := by
  obtain ⟨fuel, finished⟩ := finiteDrain request (start request)
  exact ⟨fuel, finished, completed_run_assignments request fuel finished⟩


#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.taskAssignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.tasksAssignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.workAssignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.stateAssignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.choice_cursor_step
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.choice_cursor_exhausted
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.tree_expansion_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.arguments_expansion_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.bag_expansion_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.bag_select_expansion_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.rest_capture_expansion_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.task_expansion_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.tasks_assignments_append
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.advance_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.tick_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.run_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.start_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.complete_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.completed_run_assignments
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection.completed_run_exists

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine.OrderedProjection
