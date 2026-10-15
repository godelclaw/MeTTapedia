import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

/-!
# Resumable scoped matcher tasks

A tick inspects one structural task or one residual collection choice. It
never invokes the recursive matcher. Assignment flow, exact schema paths and
residual bag positions are retained through every suspension.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching

structure Request where
  rule : RewriteRule
  spec : RuleBindingSpec
  ambient : Nat
  site : RulePatternSite
  path : List Nat
  depth : Nat
  initial : Assignment
  schema : Pattern
  target : Pattern
  deriving Repr

structure BagChoice where
  path : List Nat
  selected : Nat
  deriving DecidableEq, Repr

mutual
inductive TracedMatches (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    RulePatternSite → List Nat → Nat → Assignment → Pattern → Pattern →
      List BagChoice → Assignment → Prop where
  | capture {site path depth initial name target final} :
      capture? rule spec ambient depth site path initial name target = some final →
      TracedMatches rule spec ambient site path depth initial (.fvar name) target [] final
  | bound {site path depth initial index} :
      TracedMatches rule spec ambient site path depth initial (.bvar index) (.bvar index) [] initial
  | constructor {site path depth initial label patterns targets trace final} :
      TracedArguments rule spec ambient site path depth initial 0 patterns targets trace final →
      TracedMatches rule spec ambient site path depth initial
        (.apply label patterns) (.apply label targets) trace final
  | binder {site path depth initial display actualDisplay pattern target trace final} :
      TracedMatches rule spec ambient site (path ++ [0]) (depth + 1) initial pattern target trace final →
      TracedMatches rule spec ambient site path depth initial
        (.lambda display pattern) (.lambda actualDisplay target) trace final
  | binders {site path depth initial arity display actualDisplay pattern target trace final} :
      TracedMatches rule spec ambient site (path ++ [0]) (depth + arity) initial pattern target trace final →
      TracedMatches rule spec ambient site path depth initial
        (.multiLambda arity display pattern) (.multiLambda arity actualDisplay target) trace final
  | substitution {site path depth initial body targetBody replacement targetReplacement
      middle final bodyTrace replacementTrace} :
      TracedMatches rule spec ambient site (path ++ [0]) (depth + 1)
        initial body targetBody bodyTrace middle →
      TracedMatches rule spec ambient site (path ++ [1]) depth
        middle replacement targetReplacement replacementTrace final →
      TracedMatches rule spec ambient site path depth initial
        (.subst body replacement) (.subst targetBody targetReplacement)
        (bodyTrace ++ replacementTrace) final
  | bag {site path depth initial kind patterns rest targets trace final} :
      kind ≠ .vec →
      TracedBag rule spec ambient site path depth initial 0 patterns rest kind targets trace final →
      TracedMatches rule spec ambient site path depth initial
        (.collection kind patterns rest) (.collection kind targets none) trace final
  | vector {site path depth initial patterns targets trace final} :
      TracedArguments rule spec ambient site path depth initial 0 patterns targets trace final →
      TracedMatches rule spec ambient site path depth initial
        (.collection .vec patterns none) (.collection .vec targets none) trace final
  | vectorRest {site path depth initial patterns name targets middle final trace} :
      TracedArguments rule spec ambient site path depth initial 0 patterns
        (targets.take patterns.length) trace middle →
      captureRest? rule spec ambient depth site (path ++ [patterns.length])
        middle name .vec (targets.drop patterns.length) = some final →
      TracedMatches rule spec ambient site path depth initial
        (.collection .vec patterns (some name)) (.collection .vec targets none) trace final

inductive TracedArguments (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    RulePatternSite → List Nat → Nat → Assignment → Nat → List Pattern →
      List Pattern → List BagChoice → Assignment → Prop where
  | nil {site path depth initial index} :
      TracedArguments rule spec ambient site path depth initial index [] [] [] initial
  | cons {site path depth initial index pattern patterns target targets middle final headTrace tailTrace} :
      TracedMatches rule spec ambient site (path ++ [index]) depth initial pattern target headTrace middle →
      TracedArguments rule spec ambient site path depth middle (index + 1) patterns targets tailTrace final →
      TracedArguments rule spec ambient site path depth initial index
        (pattern :: patterns) (target :: targets) (headTrace ++ tailTrace) final

inductive TracedBag (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) :
    RulePatternSite → List Nat → Nat → Assignment → Nat → List Pattern →
      Option String → CollType → List Pattern → List BagChoice → Assignment → Prop where
  | nil {site path depth initial index kind} :
      TracedBag rule spec ambient site path depth initial index [] none kind [] [] initial
  | rest {site path depth initial index name kind targets final} :
      captureRest? rule spec ambient depth site (path ++ [index]) initial name kind targets = some final →
      TracedBag rule spec ambient site path depth initial index [] (some name) kind targets [] final
  | cons {site path depth initial index pattern patterns rest kind targets middle final headTrace tailTrace}
      (selected : Nat) (within : selected < targets.length) :
      TracedMatches rule spec ambient site (path ++ [index]) depth initial pattern targets[selected] headTrace middle →
      TracedBag rule spec ambient site path depth middle (index + 1) patterns rest kind
        (targets.eraseIdx selected) tailTrace final →
      TracedBag rule spec ambient site path depth initial index (pattern :: patterns) rest kind targets
        ({ path := path ++ [index], selected } :: (headTrace ++ tailTrace)) final
end

structure Answer where
  assignment : Assignment
  trace : List BagChoice
  deriving Repr

def Answer.Valid (request : Request) (answer : Answer) : Prop :=
  TracedMatches request.rule request.spec request.ambient request.site request.path
    request.depth request.initial request.schema request.target answer.trace answer.assignment

mutual
theorem TracedMatches.matching {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {schema target : Pattern} {trace : List BagChoice}
    (matched : TracedMatches rule spec ambient site path depth initial schema target trace final) :
    GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final := by
  cases matched with
  | capture captured => exact .capture captured
  | bound => exact .bound
  | constructor arguments => exact .constructor arguments.matching
  | binder body => exact .binder body.matching
  | binders body => exact .binders body.matching
  | substitution body replacement => exact .substitution body.matching replacement.matching
  | bag notVector bag => exact .bag notVector bag.matching
  | vector arguments => exact .vector arguments.matching
  | vectorRest arguments captured => exact .vectorRest arguments.matching captured
termination_by sizeOf schema

theorem TracedArguments.matching {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {trace : List BagChoice}
    (matched : TracedArguments rule spec ambient site path depth initial index schemas targets trace final) :
    GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final := by
  cases matched with
  | nil => exact .nil
  | cons head tail => exact .cons head.matching tail.matching
termination_by sizeOf schemas

theorem TracedBag.matching {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {schemas targets : List Pattern} {rest : Option String} {kind : CollType} {trace : List BagChoice}
    (matched : TracedBag rule spec ambient site path depth initial index schemas rest kind targets trace final) :
    GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final := by
  cases matched with
  | nil => exact .nil
  | rest captured => exact .rest captured
  | cons selected within head tail => exact .cons selected within head.matching tail.matching
termination_by sizeOf schemas
end

theorem Answer.Valid.matching {request : Request} {answer : Answer} (valid : answer.Valid request) :
    GeneralScopedMatch.Matches request.rule request.spec request.ambient request.site request.path
      request.depth request.initial request.schema request.target answer.assignment := TracedMatches.matching valid

inductive Task where
  | tree (path : List Nat) (depth : Nat) (schema target : Pattern)
  | arguments (path : List Nat) (depth index : Nat) (schemas targets : List Pattern)
  | bag (path : List Nat) (depth index : Nat) (schemas : List Pattern)
      (rest : Option String) (kind : CollType) (targets : List Pattern)
  | bagSelect (path : List Nat) (depth index : Nat) (schema : Pattern)
      (schemas : List Pattern) (rest : Option String) (kind : CollType)
      (targets : List Pattern) (selected : Nat)
  | restCapture (path : List Nat) (depth : Nat) (name : String)
      (kind : CollType) (targets : List Pattern)
  deriving Repr

structure Work where
  assignment : Assignment
  tasks : List Task
  trace : List BagChoice := []
  deriving Repr

structure State where
  agenda : List Work
  answers : List Answer := []
  deriving Repr

def start (request : Request) : State :=
  { agenda := [{ assignment := request.initial, tasks := [.tree request.path request.depth request.schema request.target] }] }

def complete (state : State) : Bool := state.agenda.isEmpty

def expand (request : Request) (initial : Assignment) : Task → List Work
  | .tree path depth schema target =>
    match schema, target with
    | .fvar name, target =>
      (capture? request.rule request.spec request.ambient depth request.site path initial name target).toList.map
        fun final => { assignment := final, tasks := [] }
    | .bvar expected, .bvar actual =>
      if expected = actual then [{ assignment := initial, tasks := [] }] else []
    | .apply label schemas, .apply actualLabel targets =>
      if label = actualLabel then
        [{ assignment := initial, tasks := [.arguments path depth 0 schemas targets] }] else []
    | .lambda _ body, .lambda _ targetBody =>
      [{ assignment := initial, tasks := [.tree (path ++ [0]) (depth + 1) body targetBody] }]
    | .multiLambda arity _ body, .multiLambda actualArity _ targetBody =>
      if arity = actualArity then
        [{ assignment := initial, tasks := [.tree (path ++ [0]) (depth + arity) body targetBody] }] else []
    | .subst body replacement, .subst targetBody targetReplacement =>
      [{ assignment := initial, tasks := [
        .tree (path ++ [0]) (depth + 1) body targetBody,
        .tree (path ++ [1]) depth replacement targetReplacement] }]
    | .collection kind schemas rest, .collection actualKind targets actualRest =>
      if kind = actualKind ∧ actualRest = none then
        if kind = .vec then
          match rest with
          | none => [{ assignment := initial, tasks := [.arguments path depth 0 schemas targets] }]
          | some name => [{ assignment := initial, tasks := [
            .arguments path depth 0 schemas (targets.take schemas.length),
            .restCapture (path ++ [schemas.length]) depth name kind (targets.drop schemas.length)] }]
        else [{ assignment := initial, tasks := [.bag path depth 0 schemas rest kind targets] }]
      else []
    | _, _ => []
  | .arguments path depth index schemas targets =>
    match schemas, targets with
    | [], [] => [{ assignment := initial, tasks := [] }]
    | schema :: schemas, target :: targets => [{ assignment := initial, tasks := [
      .tree (path ++ [index]) depth schema target,
      .arguments path depth (index + 1) schemas targets] }]
    | _, _ => []
  | .bag path depth index schemas rest kind targets =>
    match schemas, rest with
    | [], none => if targets = [] then [{ assignment := initial, tasks := [] }] else []
    | [], some name => [{ assignment := initial, tasks := [.restCapture (path ++ [index]) depth name kind targets] }]
    | schema :: schemas, _ => [{ assignment := initial, tasks := [.bagSelect path depth index schema schemas rest kind targets 0] }]
  | .bagSelect path depth index schema schemas rest kind targets selected =>
    match targets[selected]? with
    | none => []
    | some target => [
      { assignment := initial, tasks := [
          .tree (path ++ [index]) depth schema target,
          .bag path depth (index + 1) schemas rest kind (targets.eraseIdx selected)],
        trace := [{ path := path ++ [index], selected }] },
      { assignment := initial,
        tasks := [.bagSelect path depth index schema schemas rest kind targets (selected + 1)] }]
  | .restCapture path depth name kind targets =>
    (captureRest? request.rule request.spec request.ambient depth request.site path initial name kind targets).toList.map
      fun final => { assignment := final, tasks := [] }

def advance (request : Request) (work : Work) : List Work :=
  match work.tasks with
  | [] => []
  | task :: tasks => (expand request work.assignment task).map fun branch =>
    { assignment := branch.assignment, tasks := branch.tasks ++ tasks,
      trace := work.trace ++ branch.trace }

def tick (request : Request) (state : State) : State :=
  match state.agenda with
  | [] => state
  | work :: agenda =>
    match work.tasks with
    | [] => { agenda, answers := state.answers ++ [{ assignment := work.assignment, trace := work.trace }] }
    | _ :: _ => { agenda := advance request work ++ agenda, answers := state.answers }

def run (request : Request) : Nat → State → State
  | 0, state => state
  | fuel + 1, state => run request fuel (tick request state)

inductive Reachable (request : Request) : State → Prop where
  | start : Reachable request (start request)
  | tick {state : State} : Reachable request state → Reachable request (tick request state)

theorem reachable_tick {request : Request} {state : State}
    (reached : Reachable request state) : Reachable request (tick request state) := .tick reached

theorem reachable_run {request : Request} {state : State} (fuel : Nat)
    (reached : Reachable request state) : Reachable request (run request fuel state) := by
  induction fuel generalizing state with
  | zero => exact reached
  | succ fuel ih => exact ih (.tick reached)

/-- Resuming conserves the complete pending agenda, assignments and emitted trace receipts. -/
theorem run_add (request : Request) (first second : Nat) (state : State) :
    run request (first + second) state = run request second (run request first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (tick request state)

theorem tick_complete {request : Request} {state : State}
    (finished : complete state = true) : tick request state = state := by
  have empty : state.agenda = [] := List.isEmpty_iff.mp finished
  simp only [tick, empty]

theorem run_complete {request : Request} {state : State}
    (finished : complete state = true) (fuel : Nat) : run request fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [run, tick_complete finished, ih]

theorem complete_eq_true_iff (state : State) :
    complete state = true ↔ state.agenda = [] :=
  List.isEmpty_iff

/-- A structural tick emits at most the single finished branch at the head
of its pending agenda. -/
theorem tick_answers_length (request : Request) (state : State) :
    (tick request state).answers.length ≤ state.answers.length + 1 := by
  cases state with
  | mk agenda answers =>
      cases agenda with
      | nil => simp [tick]
      | cons work agenda =>
          cases work with
          | mk assignment tasks trace =>
              cases tasks <;> simp [tick]

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachine
