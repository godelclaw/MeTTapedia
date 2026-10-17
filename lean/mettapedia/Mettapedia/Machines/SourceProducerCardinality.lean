import Mettapedia.Machines.AnswerCardinality
import Mettapedia.Machines.SourceProducerAdmission
import Mettapedia.Machines.OrderedDependencyStore

/-!
# Cardinality derived from the existing recursive equation IR

Analysis follows the source's actual head matches, invocation-local commitment,
branch guards and structurally decreasing calls. It neither runs constructors
nor evaluates a body to discover its answer count. Its result bounds outer
answer occurrences: a returned empty collection is one answer, and equal
collections from distinct equations remain distinct answers.

This is the finite pure, scope-resolved IR of `SourceProducerAdmission`.
`unsupported` keeps an unknown grade and cannot supply execution permission.
Syntax elaboration, native correspondence, effects and open producers have
their own obligations. The no-rule observer retains only a separately supplied
fallback, never a fallback for a matching body that fails.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceProducerCardinality

open AnswerCardinality RecursiveFiniteProducer SourceProducerAdmission

universe u v
variable {Item : Type u} {Value : Type v}

/-- Body analysis over existing instructions and current argument shape.
Recursive summaries come from the smaller list argument, not an annotation. -/
def bodyGrade (tailGrade : Nat → Grade) (items : List Item) (parameter : Nat) :
    Code Value → Grade
  | .empty | .singleton _ => .one
  | .append left right => seq (bodyGrade tailGrade items parameter left)
      (bodyGrade tailGrade items parameter right)
  | .mapHead body => match items with
      | [] => .zero
      | _ :: _ => bodyGrade tailGrade items parameter body
  | .map _ body => bodyGrade tailGrade items parameter body
  | .ifZero yes no => if parameter = 0 then bodyGrade tailGrade items parameter yes
      else bodyGrade tailGrade items parameter no
  | .ifEmpty yes no => if items = [] then bodyGrade tailGrade items parameter yes
      else bodyGrade tailGrade items parameter no
  | .callTail => match items with
      | [] => .zero
      | _ :: _ => tailGrade parameter
  | .callPredecessor => match items, parameter with
      | _ :: _, count + 1 => tailGrade count
      | _, _ => .zero
  | .unsupported => .any

theorem bodyGrade_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (tailGrade : Nat → Grade)
    (tailSound : ∀ count, Allows (tailGrade count) (tailResults count).length)
    (items : List Item) (parameter : Nat) (body : Code Value) :
    Allows (bodyGrade tailGrade items parameter body)
      (bodyResults construct callbackConstruct tailResults items parameter body).length := by
  induction body with
  | empty => rfl
  | singleton value => rfl
  | append left right leftIH rightIH =>
      apply bind_sound _ _ _ _ leftIH
      intro collection _
      simpa only [List.length_map] using rightIH
  | mapHead body ih =>
      cases items with
      | nil => rfl
      | cons head tail => simpa [bodyGrade, bodyResults] using ih
  | map callback body ih => simpa [bodyGrade, bodyResults] using ih
  | ifZero yes no yesIH noIH =>
      by_cases zero : parameter = 0
      · simpa [bodyGrade, bodyResults, zero] using yesIH
      · simpa [bodyGrade, bodyResults, zero] using noIH
  | ifEmpty yes no yesIH noIH =>
      by_cases empty : items = []
      · simpa [bodyGrade, bodyResults, empty] using yesIH
      · simpa [bodyGrade, bodyResults, empty] using noIH
  | callTail => cases items <;> simp_all [bodyGrade, bodyResults, Allows]
  | callPredecessor => cases items <;> cases parameter <;>
      simp_all [bodyGrade, bodyResults, Allows]
  | unsupported => trivial

/-- Every uncommitted matching equation contributes its own occurrences.
An explicit source commit has its existing invocation-local semantics. -/
def equationsGrade (matchesHead : Head → Bool) (gradeBody : Code Value → Grade) :
    List (Equation Value) → Grade
  | [] => .zero
  | equation :: rest =>
      if matchesHead equation.head then
        if equation.commit then gradeBody equation.body
        else choice (gradeBody equation.body) (equationsGrade matchesHead gradeBody rest)
      else equationsGrade matchesHead gradeBody rest

theorem equationsGrade_sound (matchesHead : Head → Bool)
    (gradeBody : Code Value → Grade) (runBody : Code Value → List (List Value))
    (bodySound : ∀ body, Allows (gradeBody body) (runBody body).length)
    (program : List (Equation Value)) :
    Allows (equationsGrade matchesHead gradeBody program)
      (equationsResults matchesHead runBody program).length := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      cases matched : matchesHead equation.head <;> cases committed : equation.commit <;>
        simp only [equationsGrade, equationsResults, matched, committed, Bool.false_eq_true,
          ↓reduceIte]
      · exact ih
      · exact ih
      · exact append_sound _ _ _ _ (bodySound equation.body) ih
      · exact bodySound equation.body

/-- With no explicit source commitment, head enumeration keeps every matching
equation body in its observed order. An earlier failing body cannot suppress a
later answer. This is an equality of occurrence lists, not answer supports. -/
theorem uncommitted_equations_keep_all_occurrences (matchesHead : Head → Bool)
    (runBody : Code Value → List (List Value)) (program : List (Equation Value))
    (uncommitted : ∀ equation ∈ program, equation.commit = false) :
    equationsResults matchesHead runBody program =
      (program.filter fun equation => matchesHead equation.head).flatMap
        (fun equation => runBody equation.body) := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      have here := uncommitted equation (by simp)
      have later := ih (fun other member => uncommitted other (by simp [member]))
      cases matched : matchesHead equation.head <;>
        simp [equationsResults, matched, here, later]

/-- Source analysis descends exactly where source execution descends.
The constructors and callback implementations are absent from this algorithm. -/
def sourceGrade (program : List (Equation Value)) : List Item → Nat → Grade
  | [], parameter => equationsGrade (fun head => head.matches ([] : List Item) parameter)
      (bodyGrade (fun _ => .zero) ([] : List Item) parameter) program
  | head :: tail, parameter =>
      equationsGrade (fun pattern => pattern.matches (head :: tail) parameter)
        (bodyGrade (sourceGrade program tail) (head :: tail) parameter) program

theorem sourceGrade_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    Allows (sourceGrade program items parameter)
      (source construct callbackConstruct program items parameter).length := by
  induction items generalizing parameter with
  | nil =>
      apply equationsGrade_sound
      intro body
      exact bodyGrade_sound construct callbackConstruct (fun _ => []) (fun _ => .zero)
        (fun _ => rfl) [] parameter body
  | cons head tail ih =>
      apply equationsGrade_sound
      intro body
      exact bodyGrade_sound construct callbackConstruct
        (source construct callbackConstruct program tail) (sourceGrade program tail)
        ih (head :: tail) parameter body

/-- The supplied fallback is interpreted only for an empty matching family.
It is not a claim that raw authored syntax is the canonical fallback value. -/
def observedSource (policy : NoRulePolicy) (fallback : List Value)
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    List (List Value) :=
  if noMatch (shape items parameter) program then observeRuleBodies policy fallback []
  else source construct callbackConstruct program items parameter

def observedGrade (policy : NoRulePolicy) (program : List (Equation Value))
    (items : List Item) (parameter : Nat) : Grade :=
  if noMatch (shape items parameter) program then ruleGrade policy []
  else sourceGrade program items parameter

theorem observedGrade_sound (policy : NoRulePolicy) (fallback : List Value)
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    Allows (observedGrade policy program items parameter)
      (observedSource policy fallback construct callbackConstruct program items parameter).length := by
  unfold observedGrade observedSource
  split
  · exact ruleGrade_sound policy fallback [] [] .nil
  · exact sourceGrade_sound construct callbackConstruct program items parameter

/-- The empty-answer observer agrees with the source even on unmatched input.
The source's independent head-matching theorem discharges that boundary. -/
theorem noAnswers_observer_is_source (fallback : List Value)
    (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    observedSource .noAnswers fallback construct callbackConstruct program items parameter =
      source construct callbackConstruct program items parameter := by
  unfold observedSource
  split
  next absent =>
    rw [source_equations_shape, equationsResults_noMatch _ _ _ absent]
    rfl
  next present => rfl

inductive CallingConvention where
  | direct
  | optional
  | nonemptyProducer
  | producer
  deriving DecidableEq, Repr

def convention : Grade → CallingConvention
  | .one => .direct
  | .zero | .optional => .optional
  | .nonempty => .nonemptyProducer
  | .any => .producer

def ConventionAllows : CallingConvention → Nat → Prop
  | .direct, count => count = 1
  | .optional, count => count ≤ 1
  | .nonemptyProducer, count => 1 ≤ count
  | .producer, _ => True

theorem convention_sound (grade : Grade) (count : Nat) (sound : Allows grade count) :
    ConventionAllows (convention grade) count := by
  cases grade <;> simp_all [convention, ConventionAllows, Allows]

/-- Classification follows the complete actual source, including duplicate
matching equations. It is not permission to force, parallelize or run effects. -/
theorem source_convention_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    ConventionAllows (convention (sourceGrade program items parameter))
      (source construct callbackConstruct program items parameter).length :=
  convention_sound _ _ (sourceGrade_sound construct callbackConstruct program items parameter)

/-- The existing admitted recursive compiler constructs an executable witness
for a direct outer answer and all requested prefixes of its inner collection.
Collection items and outer answer occurrences are distinct observations. -/
theorem admitted_cursor_has_direct_answer (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (compiled : Code Value)
    (accepted : compile program = some compiled) (items : List Item) (parameter : Nat) :
    ConventionAllows .direct (source construct callbackConstruct program items parameter).length ∧
      ∃ result, source construct callbackConstruct program items parameter = [result] ∧
        ∀ bound, takePrefix construct callbackConstruct compiled bound
          (initial compiled items parameter) = some (result.take bound) := by
  obtain ⟨result, sourceDone, prefixes⟩ :=
    compile_bounded_correct construct callbackConstruct program compiled accepted items parameter
  refine ⟨?_, result, sourceDone, prefixes⟩
  simp [ConventionAllows, sourceDone]

/-- A constructed worker is different from a cardinality summary.
Without a compiled realization, the source evaluator stays authoritative even
when analysis establishes a narrow count. No source commitment is inserted. -/
inductive SelectedWorker (Value : Type v) where
  | directCode (compiled : Code Value)
  | optionalCode (compiled : ShapeTree (Option (Code Value)))
  | reference (summary : CallingConvention)

/-- Capacity of the receiving native result interface, independently of the
source's inferred answer count. A requested interface is not a source contract. -/
inductive ScalarResultInterface where
  | singleValue
  | optionalValue
  deriving DecidableEq, Repr

/-- The result interface limits the realizations a consumer can receive.
A value-only consumer cannot represent zero answers, so it keeps the source
interpreter when only optional compilation succeeds. This request is neither
a cardinality assertion nor permission to change argument demand. -/
def selectWorker (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) : SelectedWorker Value :=
  match compile program with
  | some compiled => .directCode compiled
  | none =>
      if resultInterface = .singleValue then
        .reference (convention (sourceGrade program items parameter))
      else match compileOptionalTree program with
        | some compiled => .optionalCode compiled
        | none => .reference (convention (sourceGrade program items parameter))

/-- Compiled branches execute their independent workers. An optional empty
result is zero occurrences, while a returned empty collection is one.
The reference branch retains every actual source occurrence. -/
def executeWorker (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    SelectedWorker Value → Option (List (List Value))
  | .directCode compiled =>
      (eager construct callbackConstruct compiled items parameter compiled).map (fun value => [value])
  | .optionalCode compiled =>
      some (optionalRun construct callbackConstruct compiled items parameter).toList
  -- The reference alias stays the authoritative source interpreter.
  -- Equation publication is not installed as a worker.
  | .reference _ => some (source construct callbackConstruct program items parameter)

/-- Selection supplies the executable compiler evidence before execution.
This preserves outer occurrences and their inner collections; constructors
run only in the selected interpreter, never in cardinality analysis. -/
theorem selected_worker_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) :
    executeWorker construct callbackConstruct program items parameter
        (selectWorker program items parameter resultInterface) =
      some (source construct callbackConstruct program items parameter) := by
  cases built : compile program with
  | none =>
      by_cases valueOnly : resultInterface = .singleValue
      · simp [selectWorker, built, valueOnly, executeWorker]
      · cases optional : compileOptionalTree program with
        | none => simp [selectWorker, built, optional, valueOnly, executeWorker]
        | some tree =>
            simp only [selectWorker, built, valueOnly, ↓reduceIte, optional, executeWorker]
            exact congrArg some
              (optionalRun_refines_source construct callbackConstruct program tree optional items parameter)
  | some compiled =>
      obtain ⟨_, result, compiledDone, sourceDone⟩ :=
        compile_source construct callbackConstruct program compiled built items parameter
      simp [selectWorker, built, executeWorker, compiledDone, sourceDone]

/-- A direct worker retains the existing complete cursor, not a probed first
answer. Every prefix is the prefix of its independently evaluated source
collection, including duplicate elements and the zero-demand prefix. -/
theorem selected_direct_cursor (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (compiled : Code Value)
    (selected : selectWorker program items parameter = .directCode compiled) :
    ∃ result, source construct callbackConstruct program items parameter = [result] ∧
      ∀ bound, takePrefix construct callbackConstruct compiled bound
        (initial compiled items parameter) = some (result.take bound) := by
  cases built : compile program with
  | none => cases optional : compileOptionalTree program <;>
      simp [selectWorker, built, optional] at selected
  | some actual =>
      simp only [selectWorker, built, SelectedWorker.directCode.injEq] at selected
      subst actual
      exact compile_bounded_correct construct callbackConstruct program compiled built items parameter

/-- Optional selection supplies a constructed worker, not a demand to probe
a second answer. Its actual completed result bounds the independent source. -/
theorem selected_optional_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (compiled : ShapeTree (Option (Code Value)))
    (selected : selectWorker program items parameter = .optionalCode compiled) :
    (optionalRun construct callbackConstruct compiled items parameter).toList =
      source construct callbackConstruct program items parameter := by
  cases direct : compile program with
  | some code => simp [selectWorker, direct] at selected
  | none =>
      cases optional : compileOptionalTree program with
      | none => simp [selectWorker, direct, optional] at selected
      | some tree =>
          simp [selectWorker, direct, optional] at selected
          subst tree
          exact optionalRun_refines_source construct callbackConstruct program compiled
            optional items parameter

theorem selected_optional_bounds_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (compiled : ShapeTree (Option (Code Value)))
    (selected : selectWorker program items parameter = .optionalCode compiled) :
    ConventionAllows .optional (source construct callbackConstruct program items parameter).length := by
  rw [←selected_optional_refines_source construct callbackConstruct program items parameter compiled selected]
  cases optionalRun construct callbackConstruct compiled items parameter <;>
    simp [ConventionAllows]

/-- A value-only interface cannot accidentally reuse an optional executable.
The evidence comes from the selection algorithm, independently of the body. -/
theorem value_only_selector_refuses_optional (program : List (Equation Value))
    (items : List Item) (parameter : Nat) (tree : ShapeTree (Option (Code Value))) :
    selectWorker program items parameter .singleValue ≠ .optionalCode tree := by
  cases built : compile program <;> simp [selectWorker, built]

section MutableEquations

variable {size : Nat}

/-- Reuse checks the complete ordered equation view, including an empty view.
Arguments are the current invocation's values, not retained old bindings.
Refused evidence keeps the complete source interpreter as the worker. -/
def checkedWorker (before current : OrderedDependencyStore.Store (Equation Value) size)
    (reader : Fin size) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) : SelectedWorker Value :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader)
  then selectWorker (OrderedDependencyStore.query before reader) items parameter resultInterface
  else .reference .producer

/-- Validation transports the constructed worker to the actual updated source.
Failure of validation does not turn that source into an empty producer. -/
theorem checked_worker_refines_current (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (world : OrderedDependencyStore.Store (Equation Value) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (Equation Value) size))
    (reader : Fin size) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) :
    executeWorker construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        items parameter
        (checkedWorker world (OrderedDependencyStore.execute world actions)
          reader items parameter resultInterface) =
      some (source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        items parameter) := by
  unfold checkedWorker
  split
  next valid =>
    rw [← OrderedDependencyStore.validated_query world invariant actions reader valid]
    exact selected_worker_refines_source construct callbackConstruct _ items parameter resultInterface
  next refused => rfl

/-- Checked direct reuse supplies the complete cursor proof for the current
source; a full-view mutation cannot inherit a direct worker from an old view. -/
theorem checked_direct_cursor (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (world : OrderedDependencyStore.Store (Equation Value) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (Equation Value) size))
    (reader : Fin size) (items : List Item) (parameter : Nat) (compiled : Code Value)
    (selected : checkedWorker world (OrderedDependencyStore.execute world actions)
      reader items parameter = .directCode compiled) :
    ∃ result,
      source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader)
        items parameter = [result] ∧
      ∀ bound, takePrefix construct callbackConstruct compiled bound
        (initial compiled items parameter) = some (result.take bound) := by
  unfold checkedWorker at selected
  split at selected
  next valid =>
    rw [OrderedDependencyStore.validated_query world invariant actions reader valid]
    exact selected_direct_cursor construct callbackConstruct _ items parameter compiled selected
  next refused => cases selected

end MutableEquations

/-! ## Read-only completion of an equation frontier

An exhausted frame that has already matched cannot produce a no-rule fallback.
Its continuation has no future body answer to receive. This supplies structural
completion evidence without evaluating an untried equation to learn whether it
fails. Native source-array, binding and continuation correspondence remain the
realization obligations of the frame representation.
-/

structure FrontierFrame (Value : Type v) where
  equations : List (Equation Value)
  next : Nat
  matched : Bool
  input : Shape

def FrontierFrame.quiet (frame : FrontierFrame Value) : Bool :=
  frame.matched && decide (frame.equations.length ≤ frame.next)

def FrontierFrame.answers (frame : FrontierFrame Value) (policy : NoRulePolicy)
    (fallback : List Value) (runBody : Code Value → List (List Value))
    (continuation : List Value → List (List Value)) : List (List Value) :=
  let remaining := frame.equations.drop frame.next
  let answers :=
    if frame.matched || !noMatch frame.input remaining then
      equationsResults (fun head => head.accepts frame.input) runBody remaining
    else observeRuleBodies policy fallback []
  answers.flatMap continuation

/-- Already matching is essential: an exhausted but unmatched frame may still
owe its canonical no-rule observation. A continuation is never called here. -/
theorem quiet_frame_has_no_future (frame : FrontierFrame Value)
    (policy : NoRulePolicy) (fallback : List Value)
    (runBody : Code Value → List (List Value))
    (continuation : List Value → List (List Value))
    (quiet : frame.quiet = true) :
    frame.answers policy fallback runBody continuation = [] := by
  have both := Bool.and_eq_true_iff.mp quiet
  have exhausted : frame.equations.drop frame.next = [] :=
    List.drop_eq_nil_iff.mpr (of_decide_eq_true both.2)
  simp [FrontierFrame.answers, both.1, exhausted, equationsResults]

/-- The scan of the actual retained frames bounds the whole remaining answer
frontier. Distinct frames and duplicate equation occurrences are not merged. -/
theorem quiet_frontier_has_no_future (frames : List (FrontierFrame Value))
    (policy : NoRulePolicy) (fallback : List Value)
    (runBody : Code Value → List (List Value))
    (continuation : List Value → List (List Value))
    (quiet : frames.all FrontierFrame.quiet = true) :
    (frames.flatMap fun frame => frame.answers policy fallback runBody continuation) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  exact quiet_frame_has_no_future frame policy fallback runBody continuation
    ((List.all_eq_true.mp quiet) frame member)

theorem unmatched_exhausted_frame_can_still_answer :
    let frame : FrontierFrame Nat := ⟨[], 0, false, ⟨false, false⟩⟩
    frame.quiet = false ∧
      frame.answers .retainFallback [7] (fun _ => []) (fun answer => [answer]) = [[7]] := by
  decide

namespace Controls

def disjoint : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.cons, .any⟩, false, .singleton 11⟩]

theorem bound_shapes_derive_direct :
    sourceGrade disjoint ([] : List Nat) 0 = .one ∧
      sourceGrade disjoint [3] 0 = .one := by decide

def duplicates : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩]

theorem equal_answers_require_a_producer :
    convention (sourceGrade duplicates ([] : List Nat) 0) = .nonemptyProducer ∧
      source (fun (item value : Nat) => item + value) (fun _ left right => left + right)
        duplicates ([] : List Nat) 0 = [[7], [7]] := by decide

def failingMatch : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .callTail⟩]

theorem matching_failure_is_not_an_empty_collection :
    sourceGrade failingMatch ([] : List Nat) 0 = .zero ∧
      sourceGrade ([⟨⟨.empty, .any⟩, false, .empty⟩] : List (Equation Nat))
        ([] : List Nat) 0 = .one := by decide

theorem a_failing_equation_does_not_commit :
    source (fun (item value : Nat) => item + value) (fun _ left right => left + right)
      [⟨⟨.empty, .any⟩, false, .callTail⟩, ⟨⟨.empty, .any⟩, false, .singleton 7⟩]
      ([] : List Nat) 0 = [[7]] ∧
      sourceGrade [⟨⟨.empty, .any⟩, false, .callTail⟩,
        ⟨⟨.empty, .any⟩, false, .singleton 7⟩] ([] : List Nat) 0 = .one := by decide

def recursive : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .empty⟩,
   ⟨⟨.cons, .any⟩, false, .mapHead .callTail⟩]

theorem recursive_summary_comes_from_descent (items : List Nat) (parameter : Nat) :
    sourceGrade recursive items parameter = .one := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change choice (sourceGrade recursive tail parameter) .zero = .one
      rw [ih]
      rfl

theorem unsupported_keeps_unknown :
    convention (sourceGrade ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat))
      ([] : List Nat) 0) = .producer := by decide

theorem unmatched_and_matching_failure_stay_distinct :
    observedGrade .retainFallback failingMatch ([] : List Nat) 0 = .zero ∧
      observedGrade .retainFallback failingMatch [3] 0 = .one ∧
      observedGrade .noAnswers failingMatch [3] 0 = .zero := by decide

theorem source_commit_is_not_a_determinism_claim :
    sourceGrade (duplicates.map fun equation => {equation with commit := true})
      ([] : List Nat) 0 = .one ∧
      sourceGrade duplicates ([] : List Nat) 0 = .nonempty := by decide

theorem overlapping_equal_equations_keep_the_reference :
    compile duplicates = none ∧
      (match selectWorker duplicates ([] : List Nat) 0 with
        | .reference .nonemptyProducer => true
        | _ => false) = true := by decide

theorem recursive_worker_is_constructed :
    ∃ compiled, compile recursive = some compiled ∧
      ∀ (items : List Nat) parameter,
        selectWorker recursive items parameter = .directCode compiled := by
  refine ⟨?_, ?_, ?_⟩
  · exact (SourceProducerAdmission.DecisionTree.code
      ⟨.empty, .mapHead .callTail, .empty, .mapHead .callTail⟩)
  · rfl
  · intro items parameter
    rfl

def recursiveWorld : OrderedDependencyStore.Store (Equation Nat) 2 :=
  OrderedDependencyStore.initial 914 (fun _ => recursive)

theorem added_equation_refuses_old_direct_code :
    OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn recursiveWorld 0 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
      (OrderedDependencyStore.readStamp recursiveWorld 0) = false ∧
      (match checkedWorker recursiveWorld
          (OrderedDependencyStore.appendOwn recursiveWorld 0 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
          0 ([] : List Nat) 0 with
        | .reference .producer => true
        | _ => false) = true := by decide

theorem unrelated_equation_update_keeps_direct_code :
    OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn recursiveWorld 1 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
      (OrderedDependencyStore.readStamp recursiveWorld 0) = true ∧
      (match checkedWorker recursiveWorld
          (OrderedDependencyStore.appendOwn recursiveWorld 1 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
          0 ([3] : List Nat) 0 with
        | .directCode _ => true
        | _ => false) = true := by decide

end Controls

namespace OptionalControls

def headProgram : List (Equation Nat) :=
  SourceProducerAdmission.OptionalControls.maybeHead

theorem ordinary_source_selects_optional :
    selectWorker headProgram ([] : List Nat) 0 =
      .optionalCode ⟨none, some (.mapHead (.singleton 7)),
        none, some (.mapHead (.singleton 7))⟩ := by rfl

theorem optional_source_keeps_values_and_absence :
    executeWorker Nat.add (fun _ left _ => left) headProgram [] 0
      (selectWorker headProgram ([] : List Nat) 0) = some [] ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [3] 0
      (selectWorker headProgram [3] 0) = some [[10]] := by decide

def recursiveOptional : List (Equation Nat) := [⟨⟨.cons, .any⟩, false,
  .append (.mapHead (.singleton 7)) .callTail⟩]

theorem recursive_empty_propagates :
    executeWorker Nat.add (fun _ left _ => left) recursiveOptional [3, 5] 0
      (selectWorker recursiveOptional [3, 5] 0) = some [] := by decide

def optionalWorld : OrderedDependencyStore.Store (Equation Nat) 2 :=
  OrderedDependencyStore.initial 915 (fun cell => if cell = 0 then headProgram else [])

theorem mutation_restores_every_equation_occurrence :
    let current := OrderedDependencyStore.appendOwn optionalWorld 0
      [⟨⟨.cons, .any⟩, false, .singleton 11⟩]
    executeWorker Nat.add (fun _ left _ => left)
      (OrderedDependencyStore.query current 0) [3] 0
      (checkedWorker optionalWorld current 0 [3] 0) = some [[10], [11]] := by decide

theorem value_only_interface_retains_the_source :
    selectWorker headProgram ([] : List Nat) 0 .singleValue = .reference .optional ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [] 0
      (selectWorker headProgram ([] : List Nat) 0 .singleValue) = some [] ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [3] 0
      (selectWorker headProgram [3] 0 .singleValue) = some [[10]] := by
  exact ⟨rfl, rfl, rfl⟩

theorem interface_does_not_assert_success_or_commit :
    selectWorker Controls.duplicates ([] : List Nat) 0 .singleValue =
      .reference .nonemptyProducer ∧
    executeWorker Nat.add (fun _ left _ => left) Controls.duplicates [] 0
      (selectWorker Controls.duplicates ([] : List Nat) 0 .singleValue) = some [[7], [7]] := by
  exact ⟨rfl, rfl⟩

end OptionalControls

/-! ### Equation publication beside the reference worker

`RetainedFrontier` republishes the source one equation at a time. Each
matched equation is still the eager `bodyResults` list, with `tailResults`
already computed, so this is a reference observation rather than a body or
call worker. `selectWorker` still returns `.reference` for a producer
convention. Direct and optional code stay on their compiled workers. The
four-convention native, world, and effect package is not supplied here.
-/

section RetainedFrontierBoundary

def sourceTail (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value))
    (items : List Item) : Nat → List (List Value) :=
  match items with
  | [] => fun _ => []
  | _ :: tail => source construct callbackConstruct program tail

theorem retained_frontier_eq_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    (driveFrontier construct callbackConstruct (sourceTail construct callbackConstruct program items)
        fallback (program.length + 1)
        (openFrontier program items parameter (.observe .noAnswers))).1 =
      source construct callbackConstruct program items parameter := by
  have stepped := driveFrontier_running_eq construct callbackConstruct
    (sourceTail construct callbackConstruct program items) fallback
    (openFrontier program items parameter (.observe .noAnswers)) rfl rfl
  simp only [openFrontier, List.drop_zero] at stepped
  cases any : matchesAny (fun head => head.matches items parameter) program
  · cases items with
    | nil =>
        have absent := equationsResults_of_no_match
          (fun head => head.matches ([] : List Item) parameter)
          (bodyResults construct callbackConstruct (fun _ => []) ([] : List Item) parameter)
          program any
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail, absent,
          observeRuleBodies] using stepped.1
    | cons head tail =>
        have absent := equationsResults_of_no_match
          (fun pattern => pattern.matches (head :: tail) parameter)
          (bodyResults construct callbackConstruct
            (source construct callbackConstruct program tail) (head :: tail) parameter)
          program any
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail, absent,
          observeRuleBodies] using stepped.1
  · cases items with
    | nil =>
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail] using stepped.1
    | cons head tail =>
        simpa [suffixOccurrences, openFrontier, any, source, sourceTail] using stepped.1

theorem reference_observation_matches_frontier (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (summary : CallingConvention) :
    executeWorker construct callbackConstruct program items parameter (.reference summary) =
      some (driveFrontier construct callbackConstruct
        (sourceTail construct callbackConstruct program items) fallback (program.length + 1)
        (openFrontier program items parameter (.observe .noAnswers))).1 := by
  simp only [executeWorker]
  exact congrArg some
    (retained_frontier_eq_source construct callbackConstruct fallback program items parameter).symm

namespace FrontierControls

def noneHere : List (Equation Nat) := []

def oneHere : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def manyHere : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def committed : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 9⟩]

def captured : List (Equation Nat) := [⟨⟨.cons, .any⟩, false, .mapHead (.singleton 7)⟩]

def failedMatch : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .callTail⟩]

def emptyCollection : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .empty⟩]

def tailOf (program : List (Equation Nat)) (items : List Nat) : Nat → List (List Nat) :=
  sourceTail Nat.add (fun _ left _ => left) program items

theorem zero_budget_is_pending_empty :
    let opened := openFrontier manyHere ([] : List Nat) 0 (.observe .noAnswers)
    driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 0 opened = ([], opened) ∧
      opened.isPending = true ∧ opened.phase = .running := by
  exact ⟨rfl, rfl, rfl⟩

theorem finished_empty_is_not_pending :
    let opened := openFrontier noneHere ([] : List Nat) 0 (.observe .noAnswers)
    let result := driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [] 1 opened
    result.1 = [] ∧ result.2.phase = .finished ∧ result.2.isPending = false ∧
      opened.isPending = false := by
  decide

theorem one_occurrence_then_finishes :
    let opened := openFrontier oneHere ([] : List Nat) 0 (.observe .noAnswers)
    let once := driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 1 opened
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 2 opened
    once.1 = [[7]] ∧ once.2.phase = .running ∧ done.1 = [[7]] ∧ done.2.phase = .finished := by
  decide

theorem many_occurrences_are_not_termination :
    let opened := openFrontier manyHere ([] : List Nat) 0 (.observe .noAnswers)
    let yielded := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 2 opened
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 3 opened
    yielded.1 = [[7], [7]] ∧ yielded.2.phase = .running ∧ yielded.2.isPending = false ∧
      done.1 = [[7], [7]] ∧ done.2.phase = .finished := by
  decide

theorem split_loans_the_prefix_and_resume_keeps_the_rest :
    let opened := openFrontier manyHere ([] : List Nat) 0 (.observe .noAnswers)
    let first := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 1 opened
    let second := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 2 first.2
    first.1 = [[7]] ∧ second.1 = [[7]] ∧ first.1 ++ second.1 = [[7], [7]] ∧
      second.2.phase = .finished ∧ second.2.authored = manyHere := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem resume_of_finished_does_not_replay :
    let opened := openFrontier oneHere ([] : List Nat) 0 (.observe .noAnswers)
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 2 opened
    driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 2 done.2 = ([], done.2) := by
  rfl

theorem commit_retains_the_later_equation_and_does_not_run_it :
    let opened := openFrontier committed ([] : List Nat) 0 (.observe .noAnswers)
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf committed []) [] 2 opened
    done.1 = [[7]] ∧ done.2.phase = .finished ∧ done.2.authored = committed ∧
      done.2.sealed = true ∧ committed.drop 1 = [⟨⟨.any, .any⟩, false, .singleton 9⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem captured_bindings_are_the_ones_retained :
    let three := openFrontier captured [3] 0 (.observe .noAnswers)
    let four := openFrontier captured [4] 0 (.observe .noAnswers)
    (driveFrontier Nat.add (fun _ left _ => left) (tailOf captured [3]) [] 1 three).1 = [[10]] ∧
      (driveFrontier Nat.add (fun _ left _ => left) (tailOf captured [4]) [] 1 four).1 = [[11]] ∧
      three.items = [3] ∧ four.items = [4] := by
  decide

theorem empty_collection_is_one_occurrence :
    let opened := openFrontier emptyCollection ([] : List Nat) 0 (.observe .noAnswers)
    (driveFrontier Nat.add (fun _ left _ => left) (tailOf emptyCollection []) [] 1 opened).1 =
      [[]] := by
  decide

theorem matching_failure_finishes_empty_without_fallback :
    let opened := openFrontier failedMatch ([] : List Nat) 0 (.observe .retainFallback)
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf failedMatch []) [9] 2 opened
    done.1 = [] ∧ done.2.phase = .finished ∧ done.2.matched = true := by
  decide

theorem unmatched_decline_is_not_finished_empty :
    let opened := openFrontier noneHere ([] : List Nat) 0 .decline
    let stopped := driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [9] 1 opened
    stopped.1 = [] ∧ stopped.2.phase = .declined ∧ stopped.2.phase ≠ .finished := by
  decide

theorem unmatched_fallback_is_one_occurrence :
    let opened := openFrontier noneHere ([] : List Nat) 0 (.observe .retainFallback)
    (driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [9] 1 opened).1 = [[9]] ∧
      (driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [9] 1
        (openFrontier noneHere [] 0 (.observe .noAnswers))).1 = [] := by
  decide

theorem producer_convention_is_still_the_reference :
    selectWorker manyHere ([] : List Nat) 0 = .reference .nonemptyProducer ∧
      executeWorker Nat.add (fun _ left _ => left) manyHere [] 0
        (.reference .nonemptyProducer) =
        some (driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) []
          (manyHere.length + 1) (openFrontier manyHere [] 0 (.observe .noAnswers))).1 := by
  exact ⟨rfl, rfl⟩

end FrontierControls

#print axioms retained_frontier_eq_source
#print axioms reference_observation_matches_frontier

end RetainedFrontierBoundary

end Mettapedia.Machines.SourceProducerCardinality
