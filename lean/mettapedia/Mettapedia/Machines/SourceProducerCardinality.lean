import Mettapedia.Machines.AnswerCardinality
import Mettapedia.Machines.SourceProducerAdmission
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.OrderedDependencyStore
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.Cursor.Fold
import Mettapedia.GSLT.Contracts.IndexedAuthority
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog
import Mettapedia.Algebra.SharedCoefficientLedger

/-!
# Cardinality derived from the existing recursive equation IR

Executable admission follows finite authored syntax and the current Shape,
with conservative unknown bounds at recursive calls. It neither follows future
invocations nor runs constructors to discover an answer count. The recursive
`sourceGrade` remains a semantic reference. Grades bound outer occurrences:
a returned empty collection is one answer, and equal collections from distinct
equations remain distinct answers.

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

/-- Semantic reference analysis descends where source execution descends.
Executable admission uses conservative Preparation bounds instead. -/
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

/-- Semantic reference for the observer; executable admission does not use it. -/
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

/-- The worker representation is separate from its cardinality summary.
Supported authored code uses the shared body/call cursor when a scalar
compiler does not apply. No source commitment is inserted. -/
inductive SelectedWorker (Value : Type v) where
  | directCode (compiled : Code Value)
  | optionalCode (compiled : ShapeTree (Option (Code Value)))
  | bodyCall (summary : CallingConvention)
  | reference (summary : CallingConvention)

/-- Admission examines the existing instruction grammar once. A refused
grammar retains the reference interpretation rather than claiming that a
cursor handoff is a completed empty result. -/
def selectSourceWorker (program : List (Equation Value)) (summary : CallingConvention) :
    SelectedWorker Value :=
  if BodyCall.supportedProgram program then .bodyCall summary else .reference summary

/-- The code-only body bound is the existing grade interpretation with an
unknown summary at every admitted recursive edge. No recursive source query
is required to construct this bound. -/
theorem preparation_body_bound (body : Code Value) (items : List Item) (parameter : Nat) :
    (Preparation.analyze body).bounds.branch (shape items parameter) =
      bodyGrade (fun _ => .any) items parameter body := by
  induction body generalizing items parameter with
  | empty | singleton | unsupported =>
      simp only [Preparation.analyze, Preparation.branch_tabulate, bodyGrade]
  | append left right leftIH rightIH =>
      simp only [Preparation.analyze, Preparation.branch_tabulate, bodyGrade]
      rw [leftIH, rightIH]
  | mapHead body ih =>
      cases items with
      | nil => simp [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
      | cons head tail =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using ih (head :: tail) parameter
  | map callback body ih => exact ih items parameter
  | ifZero yes no yesIH noIH =>
      cases parameter with
      | zero =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using yesIH items 0
      | succ count =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using noIH items (count + 1)
  | ifEmpty yes no yesIH noIH =>
      cases items with
      | nil =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using yesIH [] parameter
      | cons head tail =>
          simpa [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
            using noIH (head :: tail) parameter
  | callTail =>
      cases items <;> simp [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]
  | callPredecessor =>
      cases items <;> cases parameter <;>
        simp [Preparation.analyze, Preparation.branch_tabulate, shape, bodyGrade]

/-- The bound is sound for arbitrary recursive answer families, including
empty families and repeated equal answers. -/
theorem preparation_body_bound_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (body : Code Value)
    (items : List Item) (parameter : Nat) :
    Allows ((Preparation.analyze body).bounds.branch (shape items parameter))
      (bodyResults construct callbackConstruct tailResults items parameter body).length := by
  rw [preparation_body_bound]
  exact bodyGrade_sound construct callbackConstruct tailResults (fun _ => .any)
    (fun _ => trivial) items parameter body

theorem preparation_grade_equations (program : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    (Preparation.prepare program).bounds.branch (shape items parameter) =
      equationsGrade (fun head => head.accepts (shape items parameter))
        (bodyGrade (fun _ => .any) items parameter) program := by
  induction program with
  | nil => exact Preparation.bounds_nil _
  | cons equation rest ih =>
      rw [Preparation.bounds_cons, preparation_body_bound, ih]
      rfl

/-- Source soundness needs no guessed completion count or recursive bound:
all recursive result families satisfy the unknown bound. -/
theorem preparation_grade_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    Allows ((Preparation.prepare program).bounds.branch (shape items parameter))
      (source construct callbackConstruct program items parameter).length := by
  rw [preparation_grade_equations, source_equations_shape]
  apply equationsGrade_sound
  intro body
  exact bodyGrade_sound construct callbackConstruct _ (fun _ => .any)
    (fun _ => trivial) items parameter body

theorem preparation_convention_sound (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    ConventionAllows (convention ((Preparation.prepare program).bounds.branch (shape items parameter)))
      (source construct callbackConstruct program items parameter).length :=
  convention_sound _ _ (preparation_grade_sound construct callbackConstruct program items parameter)

#print axioms preparation_body_bound
#print axioms preparation_body_bound_sound
#print axioms preparation_grade_equations
#print axioms preparation_grade_sound
#print axioms preparation_convention_sound

/-- Capacity of the receiving native result interface, independently of the
source's inferred answer count. A requested interface is not a source contract. -/
inductive ScalarResultInterface where
  | singleValue
  | optionalValue
  deriving DecidableEq, Repr

/-- The result interface limits the realizations a consumer can receive.
A value-only consumer cannot represent zero answers, so it keeps the general
authored worker when only optional compilation succeeds. This request is neither
a cardinality assertion nor permission to change argument demand. One shared
family preparation supplies both scalar checks and the source-grammar gate. -/
def selectWorker (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) : SelectedWorker Value :=
  let prepared := Preparation.prepare program
  match Preparation.strictCode prepared with
  | some compiled => .directCode compiled
  | none =>
      if resultInterface = .singleValue then
        if prepared.supported then .bodyCall (convention (prepared.bounds.branch (shape items parameter)))
        else .reference (convention (prepared.bounds.branch (shape items parameter)))
      else match Preparation.optionalTree prepared with
        | some compiled => .optionalCode compiled
        | none =>
            if prepared.supported then .bodyCall (convention (prepared.bounds.branch (shape items parameter)))
            else .reference (convention (prepared.bounds.branch (shape items parameter)))

/-- Scalar compiler priority and receiving-interface restrictions are
unchanged. Fallback uses the conservative code-only bound; its convention may
be weaker than the recursive semantic reference. -/
theorem selectWorker_compiler_projections (program : List (Equation Value)) (items : List Item)
    (parameter : Nat) (resultInterface : ScalarResultInterface) :
    selectWorker program items parameter resultInterface =
      match compile program with
      | some compiled => .directCode compiled
      | none =>
          if resultInterface = .singleValue then
            selectSourceWorker program (convention ((Preparation.prepare program).bounds.branch (shape items parameter)))
          else match compileOptionalTree program with
            | some compiled => .optionalCode compiled
            | none => selectSourceWorker program (convention ((Preparation.prepare program).bounds.branch (shape items parameter))) := by
  simp only [selectWorker, Preparation.strictCode_eq, Preparation.optionalTree_eq,
    Preparation.prepare_supported, selectSourceWorker]

theorem selectWorker_same_shape (program : List (Equation Value))
    (left right : List Item) (leftParameter rightParameter : Nat)
    (interface : ScalarResultInterface)
    (same : shape left leftParameter = shape right rightParameter) :
    selectWorker program left leftParameter interface =
      selectWorker program right rightParameter interface := by
  simp only [selectWorker, same]

#print axioms selectWorker_compiler_projections
#print axioms selectWorker_same_shape

/-- Compiled branches execute their independent workers. An optional empty
result is zero occurrences, while a returned empty collection is one.
Authored workers run the actual total body/call cursor. Handoff is distinct
from completion; only an admitted finished result becomes a result family. -/
def executeWorker (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat) :
    SelectedWorker Value → Option (List (List Value))
  | .directCode compiled =>
      (eager construct callbackConstruct compiled items parameter compiled).map (fun value => [value])
  | .optionalCode compiled =>
      some (optionalRun construct callbackConstruct compiled items parameter).toList
  | .bodyCall _ =>
      let completed := BodyCall.collect construct callbackConstruct (fun _ _ => [])
        (BodyCall.openState program items parameter (.observe .noAnswers))
      if completed.2.phase = .finished then some completed.1 else none
  | .reference _ => some (source construct callbackConstruct program items parameter)

theorem bodyCall_worker_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (summary : CallingConvention) (supported : BodyCall.supportedProgram program = true) :
    executeWorker construct callbackConstruct program items parameter (.bodyCall summary) =
      some (source construct callbackConstruct program items parameter) := by
  have finished := BodyCall.collect_open_finished construct callbackConstruct (fun _ _ => [])
    program items parameter supported
  have correct := BodyCall.collect_open_eq_source construct callbackConstruct (fun _ _ => [])
    program items parameter supported
  simp [executeWorker, finished, correct]

theorem source_worker_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (summary : CallingConvention) :
    executeWorker construct callbackConstruct program items parameter
        (selectSourceWorker program summary) =
      some (source construct callbackConstruct program items parameter) := by
  unfold selectSourceWorker
  split
  next supported =>
    exact bodyCall_worker_refines_source construct callbackConstruct program items parameter
      summary supported
  next refused => rfl

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
      · simpa only [selectWorker_compiler_projections, built, valueOnly, ↓reduceIte] using
          source_worker_refines_source construct callbackConstruct program items parameter _
      · cases optional : compileOptionalTree program with
        | none =>
            simpa only [selectWorker_compiler_projections, built, optional, valueOnly, ↓reduceIte] using
              source_worker_refines_source construct callbackConstruct program items parameter _
        | some tree =>
            simp only [selectWorker_compiler_projections, built, valueOnly, ↓reduceIte, optional, executeWorker]
            exact congrArg some
              (optionalRun_refines_source construct callbackConstruct program tree optional items parameter)
  | some compiled =>
      obtain ⟨_, result, compiledDone, sourceDone⟩ :=
        compile_source construct callbackConstruct program compiled built items parameter
      simp [selectWorker_compiler_projections, built, executeWorker, compiledDone, sourceDone]

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
      cases supported : BodyCall.supportedProgram program <;>
      simp [selectWorker_compiler_projections, built, optional, selectSourceWorker, supported] at selected
  | some actual =>
      simp only [selectWorker_compiler_projections, built, SelectedWorker.directCode.injEq] at selected
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
  | some code => simp [selectWorker_compiler_projections, direct] at selected
  | none =>
      cases optional : compileOptionalTree program with
      | none =>
          cases supported : BodyCall.supportedProgram program <;>
            simp [selectWorker_compiler_projections, direct, optional, selectSourceWorker, supported] at selected
      | some tree =>
          simp [selectWorker_compiler_projections, direct, optional] at selected
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
  cases built : compile program <;> simp [selectWorker_compiler_projections, built]
  cases supported : BodyCall.supportedProgram program <;>
    simp [selectSourceWorker, supported]

section MutableEquations

variable {size : Nat}

/-- Reuse checks the complete ordered equation view, including an empty view.
Arguments are the current invocation's values, not retained old bindings.
Refused evidence selects a fresh authored worker from the current view. -/
def checkedWorker (before current : OrderedDependencyStore.Store (Equation Value) size)
    (reader : Fin size) (items : List Item) (parameter : Nat)
    (resultInterface : ScalarResultInterface := .optionalValue) : SelectedWorker Value :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader)
  then selectWorker (OrderedDependencyStore.query before reader) items parameter resultInterface
  else selectSourceWorker (OrderedDependencyStore.query current reader) .producer

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
  next refused => exact source_worker_refines_source construct callbackConstruct _ items parameter .producer

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
  next refused =>
    cases supported : BodyCall.supportedProgram
      (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader) <;>
      simp [selectSourceWorker, supported] at selected

end MutableEquations

#print axioms bodyCall_worker_refines_source
#print axioms source_worker_refines_source
#print axioms selected_worker_refines_source
#print axioms checked_worker_refines_current

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
      ([] : List Nat) 0) = .producer ∧
    BodyCall.supportedProgram ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat)) = false ∧
    selectSourceWorker ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat)) .producer =
      .reference .producer := by
  exact ⟨by decide, rfl, rfl⟩

theorem unmatched_and_matching_failure_stay_distinct :
    observedGrade .retainFallback failingMatch ([] : List Nat) 0 = .zero ∧
      observedGrade .retainFallback failingMatch [3] 0 = .one ∧
      observedGrade .noAnswers failingMatch [3] 0 = .zero := by decide

theorem source_commit_is_not_a_determinism_claim :
    sourceGrade (duplicates.map fun equation => {equation with commit := true})
      ([] : List Nat) 0 = .one ∧
      sourceGrade duplicates ([] : List Nat) 0 = .nonempty := by decide

theorem overlapping_equal_equations_select_body_cursor :
    compile duplicates = none ∧
      (match selectWorker duplicates ([] : List Nat) 0 with
        | .bodyCall .nonemptyProducer => true
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
        | .bodyCall .producer => true
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
      (checkedWorker optionalWorld current 0 [3] 0) = some [[10], [11]] := by
  dsimp only
  have refused : OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn optionalWorld 0
        [⟨⟨.cons, .any⟩, false, .singleton 11⟩])
      (OrderedDependencyStore.readStamp optionalWorld 0) = false := by decide
  simp only [checkedWorker, refused, Bool.false_eq_true, ↓reduceIte]
  rw [source_worker_refines_source]
  decide

theorem value_only_interface_retains_the_source :
    selectWorker headProgram ([] : List Nat) 0 .singleValue = .bodyCall .optional ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [] 0
      (selectWorker headProgram ([] : List Nat) 0 .singleValue) = some [] ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [3] 0
      (selectWorker headProgram [3] 0 .singleValue) = some [[10]] := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [selected_worker_refines_source Nat.add (fun _ left _ => left)
      headProgram [] 0 .singleValue]
    decide
  · rw [selected_worker_refines_source Nat.add (fun _ left _ => left)
      headProgram [3] 0 .singleValue]
    decide

theorem interface_does_not_assert_success_or_commit :
    selectWorker Controls.duplicates ([] : List Nat) 0 .singleValue =
      .bodyCall .nonemptyProducer ∧
    executeWorker Nat.add (fun _ left _ => left) Controls.duplicates [] 0
      (selectWorker Controls.duplicates ([] : List Nat) 0 .singleValue) = some [[7], [7]] := by
  refine ⟨rfl, ?_⟩
  rw [selected_worker_refines_source Nat.add (fun _ left _ => left)
    Controls.duplicates [] 0 .singleValue]
  decide

end OptionalControls

/-! ### Equation publication beside the reference worker

`RetainedFrontier` republishes the source one equation at a time. Each
matched equation is still the eager `bodyResults` list, with `tailResults`
already computed, so this is a reference observation rather than a body or
call worker. The selected body/call worker instead uses the runnable cursor
and its general source theorem. Native world and effect correspondence are
separate obligations.
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

theorem producer_convention_uses_body_cursor :
    selectWorker manyHere ([] : List Nat) 0 = .bodyCall .nonemptyProducer ∧
      executeWorker Nat.add (fun _ left _ => left) manyHere [] 0
        (selectWorker manyHere ([] : List Nat) 0) =
        some (driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) []
          (manyHere.length + 1) (openFrontier manyHere [] 0 (.observe .noAnswers))).1 := by
  refine ⟨rfl, ?_⟩
  rw [selected_worker_refines_source]
  exact congrArg some (retained_frontier_eq_source Nat.add (fun _ left _ => left)
    [] manyHere [] 0).symm

end FrontierControls

#print axioms retained_frontier_eq_source
#print axioms reference_observation_matches_frontier

end RetainedFrontierBoundary

/-! The body/call cursor supplies a phase-indexed provider for the existing
cursor protocol. Its client requests actual transitions until the first
non-advance reply. Scheduler inspections and provider requests are separate:
returning an already received reply requires no further provider operation. -/

namespace BodyCallProtocol

open Mettapedia.TypeTheory _root_.CategoryTheory

def protocol : IndexedPolynomial.{max u v, max u v, max u v, max u v}
    (ULift.{max u v} Unit) (fun _ => ULift.{max u v} BodyCall.Phase) where
  Shape _ _ := ULift.{max u v} Unit
  Position _ := BodyCall.Move Item Value
  next _ moved := ⟨moved.next.phase⟩

def provider (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) :
    Cursor.Provider (protocol (Item := Item) (Value := Value)) where
  State _ phase := { state : BodyCall.State Item Value // state.phase = phase.down }
  step state _ :=
    let moved := BodyCall.step construct callbackConstruct fallback state.val
    ⟨moved, ⟨moved.next, rfl⟩⟩

def client : Cursor.Client (P := protocol (Item := Item) (Value := Value))
    (Return := fun _ _ => BodyCall.Move Item Value) where
  V _ phase := { moved : BodyCall.Move Item Value // moved.next.phase = phase.down }
  str := fun _ _ => ↾(fun control =>
    match control.val with
    | .advance _ => ⟨.inr ⟨()⟩, fun moved => ⟨moved, rfl⟩⟩
    | .yield _ _ | .finish _ _ | .decline _ | .handoff _ =>
        ⟨.inl control.val, fun impossible => nomatch impossible⟩)

variable (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value)

abbrev Packet := Cursor.Packet (provider construct callbackConstruct fallback)
  (client (Item := Item) (Value := Value)) (⟨()⟩ : ULift.{max u v} Unit)

abbrev Outcome := Cursor.Outcome (provider construct callbackConstruct fallback)
  (client (Item := Item) (Value := Value)) (⟨()⟩ : ULift.{max u v} Unit)

abbrev Finished := Cursor.Finished (provider construct callbackConstruct fallback)
  (Return := fun _ _ => BodyCall.Move Item Value) (⟨()⟩ : ULift.{max u v} Unit)

def replyPacket (moved : BodyCall.Move Item Value) : Packet construct callbackConstruct fallback :=
  ⟨⟨moved.next.phase⟩, ⟨moved, rfl⟩, ⟨moved.next, rfl⟩⟩

def packet (state : BodyCall.State Item Value) : Packet construct callbackConstruct fallback :=
  replyPacket construct callbackConstruct fallback (.advance state)

/-- Count requests of the actual body/call transition, independently of
scheduler inspections and any physical realization's work receipts. -/
def requestCharge : Cursor.Charge (provider construct callbackConstruct fallback) :=
  fun _ _ => 1

def run (fuel : Nat) (state : BodyCall.State Item Value) :
    Nat × Outcome construct callbackConstruct fallback :=
  Cursor.advance (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) fuel
    (packet construct callbackConstruct fallback state)

def resume (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback) :
    Nat × Outcome construct callbackConstruct fallback :=
  Cursor.resume (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) fuel previous

def moveView : Outcome construct callbackConstruct fallback → BodyCall.Move Item Value
  | .paused packet => packet.2.1.val
  | .done result => result.2.1

def stateView : Outcome construct callbackConstruct fallback → BodyCall.State Item Value
  | .paused packet => packet.2.2.val
  | .done result => result.2.2.val

def phaseView : Outcome construct callbackConstruct fallback → BodyCall.Phase
  | .paused packet => packet.1.down
  | .done result => result.1.down

theorem state_phase_is_index (outcome : Outcome construct callbackConstruct fallback) :
    (stateView construct callbackConstruct fallback outcome).phase =
      phaseView construct callbackConstruct fallback outcome := by
  cases outcome with
  | paused packet => exact packet.2.2.property
  | done result => exact result.2.2.property

/-- A paused reply stays in client control until its return is inspected. -/
def emittedRows : Outcome construct callbackConstruct fallback → List (List Value)
  | .paused _ => []
  | .done result => result.2.1.rows

def heldRows : Outcome construct callbackConstruct fallback → List (List Value)
  | .paused packet => packet.2.1.val.rows
  | .done _ => []

theorem rows_view (outcome : Outcome construct callbackConstruct fallback) :
    emittedRows construct callbackConstruct fallback outcome ++
        heldRows construct callbackConstruct fallback outcome =
      (moveView construct callbackConstruct fallback outcome).rows := by
  cases outcome <;> simp [emittedRows, heldRows, moveView]

theorem provider_step {base phase}
    (state : (provider construct callbackConstruct fallback).State base phase)
    (request : (protocol (Item := Item) (Value := Value)).Shape base phase) :
    ((provider construct callbackConstruct fallback).step state request).1 =
        BodyCall.step construct callbackConstruct fallback state.val ∧
      ((provider construct callbackConstruct fallback).step state request).2.val =
        (BodyCall.step construct callbackConstruct fallback state.val).next := ⟨rfl, rfl⟩

theorem run_zero (state : BodyCall.State Item Value) :
    run construct callbackConstruct fallback 0 state =
      (0, .paused (packet construct callbackConstruct fallback state)) := rfl

theorem run_zero_emits_nothing (state : BodyCall.State Item Value) :
    emittedRows construct callbackConstruct fallback
      (run construct callbackConstruct fallback 0 state).2 = [] := rfl

theorem run_succ (fuel : Nat) (state : BodyCall.State Item Value) :
    run construct callbackConstruct fallback (fuel + 1) state =
      let later := Cursor.advance (provider construct callbackConstruct fallback) client
        (requestCharge construct callbackConstruct fallback) fuel
        (replyPacket construct callbackConstruct fallback
          (BodyCall.step construct callbackConstruct fallback state))
      (1 + later.1, later.2) := rfl

theorem advance_boundary (fuel : Nat) (moved : BodyCall.Move Item Value)
    (boundary : ∀ next, moved ≠ .advance next) :
    Cursor.advance (provider construct callbackConstruct fallback) client
        (requestCharge construct callbackConstruct fallback) fuel
        (replyPacket construct callbackConstruct fallback moved) =
      match fuel with
      | 0 => (0, .paused (replyPacket construct callbackConstruct fallback moved))
      | _ + 1 => (0, .done ⟨⟨moved.next.phase⟩, moved, ⟨moved.next, rfl⟩⟩) := by
  cases moved with
  | advance next => exact False.elim (boundary next rfl)
  | yield row next => cases fuel <;> rfl
  | finish rows next => cases fuel <;> rfl
  | decline next => cases fuel <;> rfl
  | handoff next => cases fuel <;> rfl

private theorem advance_done_boundary (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (result : Finished construct callbackConstruct fallback)
    (done : (Cursor.advance (provider construct callbackConstruct fallback) client
      (requestCharge construct callbackConstruct fallback) fuel value).2 = .done result) :
    ∀ next, result.2.1 ≠ .advance next := by
  induction fuel generalizing value result with
  | zero => cases done
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          change (Cursor.advance (provider construct callbackConstruct fallback) client
            (requestCharge construct callbackConstruct fallback) fuel
            (replyPacket construct callbackConstruct fallback
              (BodyCall.step construct callbackConstruct fallback state))).2 = .done result at done
          exact ih _ _ done
      | yield row next =>
          cases done
          intro saved impossible
          cases impossible
      | finish rows next =>
          cases done
          intro saved impossible
          cases impossible
      | decline next =>
          cases done
          intro saved impossible
          cases impossible
      | handoff next =>
          cases done
          intro saved impossible
          cases impossible

/-- `done` means that the client has returned its first yield or terminal
reply. It does not turn a yield into the body's `finished` phase. -/
theorem run_done_boundary (fuel : Nat) (state : BodyCall.State Item Value)
    (result : Finished construct callbackConstruct fallback)
    (done : (run construct callbackConstruct fallback fuel state).2 = .done result) :
    ∀ next, result.2.1 ≠ .advance next :=
  advance_done_boundary construct callbackConstruct fallback fuel _ result done

/-- The held or returned first reply and the complete provider state equal
the actual bounded body/call drive at the number of requests executed. -/
theorem run_eq_drive (fuel : Nat) (state : BodyCall.State Item Value) :
    BodyCall.drive construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).1 state =
      ((moveView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2).rows,
       stateView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [run_succ]
      cases moved : BodyCall.step construct callbackConstruct fallback state with
      | advance next =>
          change BodyCall.drive construct callbackConstruct fallback
              (1 + (run construct callbackConstruct fallback fuel next).1) state = _
          rw [Nat.add_comm 1 _, BodyCall.drive, moved]
          exact ih next
      | yield row next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = ([row], next)
          all_goals simp only [BodyCall.drive, moved]
      | finish rows next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = (rows, next)
          all_goals simp only [BodyCall.drive, moved]
      | decline next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = ([], next)
          all_goals simp only [BodyCall.drive, moved]
      | handoff next =>
          cases fuel <;>
            change BodyCall.drive construct callbackConstruct fallback 1 state = ([], next)
          all_goals simp only [BodyCall.drive, moved]

private def packetCoherent (value : Packet construct callbackConstruct fallback) : Prop :=
  value.2.1.val.next = value.2.2.val

private theorem advance_coherent (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (coherent : packetCoherent construct callbackConstruct fallback value) :
    (moveView construct callbackConstruct fallback
        (Cursor.advance (provider construct callbackConstruct fallback) client
          (requestCharge construct callbackConstruct fallback) fuel value).2).next =
      stateView construct callbackConstruct fallback
        (Cursor.advance (provider construct callbackConstruct fallback) client
          (requestCharge construct callbackConstruct fallback) fuel value).2 := by
  induction fuel generalizing value with
  | zero => exact coherent
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          change (moveView construct callbackConstruct fallback
              (Cursor.advance (provider construct callbackConstruct fallback) client
                (requestCharge construct callbackConstruct fallback) fuel
                (replyPacket construct callbackConstruct fallback
                  (BodyCall.step construct callbackConstruct fallback state))).2).next = _
          exact ih _ rfl
      | yield row next => exact coherent
      | finish rows next => exact coherent
      | decline next => exact coherent
      | handoff next => exact coherent

theorem run_state_coherent (fuel : Nat) (state : BodyCall.State Item Value) :
    (moveView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2).next =
      stateView construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2 :=
  advance_coherent construct callbackConstruct fallback fuel _ rfl

/-- Exact protocol chunking preserves the reply, its client continuation,
the request count, phase index and every saved body/call frame. -/
theorem run_split_resumes (earlier later : Nat) (state : BodyCall.State Item Value) :
    run construct callbackConstruct fallback (earlier + later) state =
      resume construct callbackConstruct fallback later
        (run construct callbackConstruct fallback earlier state) :=
  Cursor.advance_add (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) earlier later _

theorem resume_split (earlier later : Nat)
    (previous : Nat × Outcome construct callbackConstruct fallback) :
    resume construct callbackConstruct fallback (earlier + later) previous =
      resume construct callbackConstruct fallback later
        (resume construct callbackConstruct fallback earlier previous) :=
  Cursor.resume_add (provider construct callbackConstruct fallback) client
    (requestCharge construct callbackConstruct fallback) earlier later previous

/-- Returned and held occurrences together with the exact residual keep
the source answer view in order. A held reply has not yet been emitted. -/
theorem run_preserves_rows (fuel : Nat) (state : BodyCall.State Item Value)
    (readings : BodyCall.sourceReadings state.work) :
    (emittedRows construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2 ++
      heldRows construct callbackConstruct fallback
        (run construct callbackConstruct fallback fuel state).2) ++
      BodyCall.workRows construct callbackConstruct
        (stateView construct callbackConstruct fallback
          (run construct callbackConstruct fallback fuel state).2).work =
      BodyCall.workRows construct callbackConstruct state.work := by
  rw [rows_view]
  have preserved := BodyCall.drive_preserves_rows construct callbackConstruct fallback
    (run construct callbackConstruct fallback fuel state).1 state readings
  simpa only [run_eq_drive] using preserved

theorem run_open_preserves_source (fuel : Nat) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    let result := run construct callbackConstruct fallback fuel
      (BodyCall.openState authored items parameter (.observe .noAnswers))
    (emittedRows construct callbackConstruct fallback result.2 ++
      heldRows construct callbackConstruct fallback result.2) ++
      BodyCall.workRows construct callbackConstruct
        (stateView construct callbackConstruct fallback result.2).work =
      source construct callbackConstruct authored items parameter := by
  exact (run_preserves_rows construct callbackConstruct fallback fuel _
    (by simp [BodyCall.openState, BodyCall.sourceReadings_cons,
      BodyCall.Cursor.sourceReading, openFrontier])).trans
    (BodyCall.openState_rows construct callbackConstruct authored items parameter)

theorem run_eventually_done (state : BodyCall.State Item Value) :
    ∃ fuel result, (run construct callbackConstruct fallback fuel state).2 = .done result := by
  fun_induction BodyCall.collect construct callbackConstruct fallback state
  case case1 state next moved ih =>
    obtain ⟨fuel, result, done⟩ := ih
    refine ⟨fuel + 1, result, ?_⟩
    rw [run_succ, moved]
    exact done
  case case2 state row next moved _later _ih =>
    refine ⟨2, ⟨⟨next.phase⟩, .yield row next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl
  case case3 state rows next moved =>
    refine ⟨2, ⟨⟨next.phase⟩, .finish rows next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl
  case case4 state next moved =>
    refine ⟨2, ⟨⟨next.phase⟩, .decline next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl
  case case5 state next moved =>
    refine ⟨2, ⟨⟨next.phase⟩, .handoff next, ⟨next, rfl⟩⟩, ?_⟩
    rw [run_succ, moved]
    rfl

#print axioms provider_step
#print axioms state_phase_is_index
#print axioms run_zero_emits_nothing
#print axioms advance_boundary
#print axioms run_done_boundary
#print axioms run_eq_drive
#print axioms run_state_coherent
#print axioms run_split_resumes
#print axioms resume_split
#print axioms run_preserves_rows
#print axioms run_open_preserves_source
#print axioms run_eventually_done

/-- The unaccepted view includes a reply held in client control as well as
the complete provider residual. It does not activate the returned values. -/
def unacceptedRows (outcome : Outcome construct callbackConstruct fallback) : List (List Value) :=
  (moveView construct callbackConstruct fallback outcome).rows ++
    BodyCall.workRows construct callbackConstruct
      (stateView construct callbackConstruct fallback outcome).work

def sourceSound (outcome : Outcome construct callbackConstruct fallback) : Prop :=
  (moveView construct callbackConstruct fallback outcome).next =
      stateView construct callbackConstruct fallback outcome ∧
    BodyCall.sourceReadings (stateView construct callbackConstruct fallback outcome).work

private theorem advance_source_view (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (coherent : packetCoherent construct callbackConstruct fallback value)
    (readings : BodyCall.sourceReadings value.2.2.val.work) :
    let outcome := (Cursor.advance (provider construct callbackConstruct fallback) client
      (requestCharge construct callbackConstruct fallback) fuel value).2
    unacceptedRows construct callbackConstruct fallback outcome =
        value.2.1.val.rows ++ BodyCall.workRows construct callbackConstruct value.2.2.val.work ∧
      BodyCall.sourceReadings (stateView construct callbackConstruct fallback outcome).work := by
  induction fuel generalizing value with
  | zero => exact ⟨rfl, readings⟩
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          have one := BodyCall.step_preserves_rows construct callbackConstruct fallback state readings
          have kept := BodyCall.step_preserves_sourceReadings construct callbackConstruct fallback state readings
          have later := ih (replyPacket construct callbackConstruct fallback
            (BodyCall.step construct callbackConstruct fallback state)) rfl kept
          exact ⟨later.1.trans one, later.2⟩
      | yield row next => exact ⟨rfl, readings⟩
      | finish rows next => exact ⟨rfl, readings⟩
      | decline next => exact ⟨rfl, readings⟩
      | handoff next => exact ⟨rfl, readings⟩

theorem resume_source_view (fuel : Nat)
    (previous : Nat × Outcome construct callbackConstruct fallback)
    (sound : sourceSound construct callbackConstruct fallback previous.2) :
    unacceptedRows construct callbackConstruct fallback
        (resume construct callbackConstruct fallback fuel previous).2 =
        unacceptedRows construct callbackConstruct fallback previous.2 ∧
      sourceSound construct callbackConstruct fallback
        (resume construct callbackConstruct fallback fuel previous).2 := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome with
  | done result => exact ⟨rfl, sound⟩
  | paused value =>
      have kept := advance_source_view construct callbackConstruct fallback fuel value sound.1 sound.2
      exact ⟨kept.1, advance_coherent construct callbackConstruct fallback fuel value sound.1, kept.2⟩

#print axioms resume_source_view

def finishedQuiet (state : BodyCall.State Item Value) : Prop :=
  state.phase = .finished → BodyCall.workRows construct callbackConstruct state.work = []

private theorem advance_finishedQuiet (fuel : Nat)
    (value : Packet construct callbackConstruct fallback)
    (quiet : finishedQuiet construct callbackConstruct value.2.2.val) :
    finishedQuiet construct callbackConstruct
      (stateView construct callbackConstruct fallback
        (Cursor.advance (provider construct callbackConstruct fallback) client
          (requestCharge construct callbackConstruct fallback) fuel value).2) := by
  induction fuel generalizing value with
  | zero => exact quiet
  | succ fuel ih =>
      rcases value with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          exact ih (replyPacket construct callbackConstruct fallback
            (BodyCall.step construct callbackConstruct fallback state))
            (BodyCall.step_finished_empty construct callbackConstruct fallback state quiet)
      | yield row next => exact quiet
      | finish rows next => exact quiet
      | decline next => exact quiet
      | handoff next => exact quiet

theorem resume_finishedQuiet (fuel : Nat)
    (previous : Nat × Outcome construct callbackConstruct fallback)
    (quiet : finishedQuiet construct callbackConstruct
      (stateView construct callbackConstruct fallback previous.2)) :
    finishedQuiet construct callbackConstruct
      (stateView construct callbackConstruct fallback
        (resume construct callbackConstruct fallback fuel previous).2) := by
  rcases previous with ⟨spent, outcome⟩
  cases outcome with
  | done result => exact quiet
  | paused value => exact advance_finishedQuiet construct callbackConstruct fallback fuel value quiet

#print axioms resume_finishedQuiet

end BodyCallProtocol

/-!
### Body/call execution

These controls run `SourceProducerAdmission.BodyCall`, the same cursor used by
the selected supported authored worker. Direct and optional scalar compilers
keep their independent fast paths and source correspondence theorems.
-/

namespace BodyCallRun

open SourceProducerAdmission.BodyCall


def paired : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .append (.singleton 1) (.singleton 2)⟩]

def called : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .append .callTail (.singleton 1)⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 8⟩]

def blank : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .empty⟩]

def missed : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .callTail⟩]

def cut : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 9⟩]

def captured : List (Equation Nat) := [⟨⟨.cons, .any⟩, false, .mapHead (.singleton 7)⟩]

/-- `.observe .noAnswers` is the source observer. The list is ignored there. -/
def drive (fuel : Nat) (program : List (Equation Nat)) (items : List Nat) (fallback : List Nat) :=
  BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => fallback) fuel
    (BodyCall.openState program items 0 (.observe .noAnswers))

def driveReading (fuel : Nat) (program : List (Equation Nat)) (items : List Nat)
    (parameter : Nat) (reading : NoRuleReading) (fallback : List Nat → Nat → List Nat) :=
  BodyCall.drive Nat.add (fun _ left _ => left) fallback fuel
    (BodyCall.openState program items parameter reading)

def nestedDecline : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .append .callTail (.singleton 1)⟩,
   ⟨⟨.cons, .any⟩, false, .singleton 9⟩]

def alienAppend : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .append .unsupported (.singleton 1)⟩]

def missedCons : List (Equation Nat) := [⟨⟨.cons, .zero⟩, false, .singleton 1⟩]

def mappedCall : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .append (.mapHead .callTail) (.singleton 1)⟩]

/-- One occurrence, indexed by the failing invocation. -/
def indexedFallback (items : List Nat) (parameter : Nat) : List Nat :=
  [items.length + parameter + 7]

def declineKept (work : List (BodyCall.Cursor Nat Nat)) : Bool :=
  match work with
  | .invoke failed _ (.times (.singleton 1) _ _ _ .emit) :: .invoke caller _ _ :: _ =>
      match failed.phase, caller.phase with
      | .declined, .running => caller.ordinal == 1 && caller.sealed == false
      | _, _ => false
  | _ => false

def handoffKept (work : List (BodyCall.Cursor Nat Nat)) : Bool :=
  match work with
  | .body _ _ frame (.times (.singleton 1) _ _ _ .emit) :: .invoke caller _ _ :: _ =>
      match frame.code, caller.phase with
      | .unsupported, .running => true
      | _, _ => false
  | _ => false

theorem pending_empty_differs_from_the_terminal_stops :
    (drive 0 missed [] []).1 = [] ∧ (drive 0 missed [] []).2.phase = .running ∧
      (drive 8 missed [] []).1 = [] ∧ (drive 8 missed [] []).2.phase = .finished ∧
      (driveReading 16 nestedDecline [0] 0 .decline (fun _ _ => [])).2.phase = .declined ∧
      (drive 8 alienAppend [] []).2.phase = .handoff := by
  decide

theorem pending_resume_finishes_the_append :
    let pending := drive 2 paired [] []
    let resumed := BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 14 pending.2
    pending.1 = [] ∧ pending.2.phase = .running ∧
      resumed.1 = [[1, 2]] ∧ resumed.2.phase = .finished ∧
      resumed.1 = (drive 16 paired [] []).1 ∧
      resumed.2.phase = (drive 16 paired [] []).2.phase := by
  decide

theorem fuel_zero_keeps_the_cursor :
    drive 0 paired [] [] =
      ([], BodyCall.openState paired ([] : List Nat) 0 (.observe .noAnswers)) := by
  rfl

theorem append_streams_one_pair :
    let done := drive 16 paired [] []
    optionalSupported (.append (.singleton 1) (.singleton 2) : Code Nat) = true ∧
      done.1 = [[1, 2]] ∧
      done.1 = source Nat.add (fun _ left _ => left) paired [] 0 ∧
      done.2.phase = .finished ∧
      (BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 4 done.2).1 = [] ∧
      (BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 4 done.2).2.phase =
        .finished := by
  decide

theorem call_streams_the_source_product :
    optionalSupported (.append .callTail (.singleton 1) : Code Nat) = true ∧
      optionalSupported (.singleton 7 : Code Nat) = true ∧
      optionalSupported (.singleton 8 : Code Nat) = true ∧
      (drive 48 called [0] []).1 = [[7, 1], [8, 1]] ∧
      (drive 48 called [0] []).1 =
        source Nat.add (fun _ left _ => left) called [0] 0 ∧
      (drive 48 called [0] []).2.phase = .finished := by
  decide

theorem empty_collection_differs_from_call_failure :
    optionalSupported (.empty : Code Nat) = true ∧
      optionalSupported (.callTail : Code Nat) = true ∧
      (drive 8 blank [] []).1 = [[]] ∧
      (drive 8 blank [] []).1 = source Nat.add (fun _ left _ => left) blank [] 0 ∧
      (drive 8 missed [] []).1 = [] ∧
      (drive 8 missed [] []).1 = source Nat.add (fun _ left _ => left) missed [] 0 := by
  decide

theorem commit_does_not_run_the_later_equation :
    optionalSupported (.singleton 7 : Code Nat) = true ∧
      optionalSupported (.singleton 9 : Code Nat) = true ∧
      (drive 8 cut [] []).1 = [[7]] ∧
      (drive 8 cut [] []).1 = source Nat.add (fun _ left _ => left) cut [] 0 ∧
      (drive 8 cut [] []).2.phase = .finished := by
  decide

theorem captured_head_is_applied :
    optionalSupported (.mapHead (.singleton 7) : Code Nat) = true ∧
      (drive 8 captured [3] []).1 = [[10]] ∧
      (drive 8 captured [3] []).1 = source Nat.add (fun _ left _ => left) captured [3] 0 ∧
      (drive 8 captured [4] []).1 = [[11]] ∧
      (drive 8 captured [4] []).1 = source Nat.add (fun _ left _ => left) captured [4] 0 := by
  decide

theorem nested_decline_keeps_caller_and_choice :
    let stopped := driveReading 16 nestedDecline [0] 0 .decline (fun _ _ => [])
    let later := BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 8 stopped.2
    stopped.1 = [] ∧ stopped.2.phase = .declined ∧ declineKept stopped.2.work = true ∧
      later.1 = [] ∧ later.2.phase = .declined ∧ declineKept later.2.work = true := by
  decide

theorem unsupported_hands_off_with_its_frame :
    optionalSupported (.append .unsupported (.singleton 1) : Code Nat) = false ∧
      source Nat.add (fun _ left _ => left) alienAppend [] 0 = [] ∧
      let stopped := drive 8 alienAppend [] []
      let later := BodyCall.drive Nat.add (fun _ left _ => left) (fun _ _ => []) 4 stopped.2
      stopped.1 = [] ∧ stopped.2.phase = .handoff ∧ handoffKept stopped.2.work = true ∧
        later.1 = [] ∧ later.2.phase = .handoff ∧ handoffKept later.2.work = true := by
  decide

theorem retain_fallback_is_indexed_by_the_invocation :
    (driveReading 8 missedCons [] 1 (.observe .retainFallback) indexedFallback).1 = [[8]] ∧
      (driveReading 8 missedCons [] 2 (.observe .retainFallback) indexedFallback).1 = [[9]] ∧
      (driveReading 8 missedCons [] 1 (.observe .retainFallback) indexedFallback).2.phase =
        .finished := by
  decide

theorem retain_fallback_applies_invocation_maps_before_append :
    optionalSupported (.append (.mapHead .callTail) (.singleton 1) : Code Nat) = true ∧
      (drive 16 mappedCall [3] []).1 = [] ∧
      (drive 16 mappedCall [3] []).1 =
        source Nat.add (fun _ left _ => left) mappedCall [3] 0 ∧
      (driveReading 16 mappedCall [3] 0 (.observe .retainFallback) indexedFallback).1 =
        [[10, 1]] ∧
      (driveReading 16 mappedCall [3] 0 (.observe .retainFallback) indexedFallback).2.phase =
        .finished := by
  decide

#print axioms pending_empty_differs_from_the_terminal_stops
#print axioms pending_resume_finishes_the_append
#print axioms fuel_zero_keeps_the_cursor
#print axioms append_streams_one_pair
#print axioms call_streams_the_source_product
#print axioms empty_collection_differs_from_call_failure
#print axioms commit_does_not_run_the_later_equation
#print axioms captured_head_is_applied
#print axioms nested_decline_keeps_caller_and_choice
#print axioms unsupported_hands_off_with_its_frame
#print axioms retain_fallback_is_indexed_by_the_invocation
#print axioms retain_fallback_applies_invocation_maps_before_append

end BodyCallRun

namespace BodyCallOwned

open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Returned := BodyCallProtocol.Finished construct callbackConstruct fallback

abbrev State := Retained.State (BodyCallProtocol.provider construct callbackConstruct fallback)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩
  (List (List Output) × Context)

def isReturn (returned : Returned construct callbackConstruct fallback) : Bool :=
  match returned.2.1 with
  | .yield _ _ => true
  | .finish rows _ => !rows.isEmpty
  | .advance _ | .decline _ | .handoff _ => false

/-- Only a producer terminal reply certifies a final return. A yield does
not imply exhaustion, even if its written row happens to be the last one. -/
def terminalAfter (returned : Returned construct callbackConstruct fallback) :
    Option (Returned construct callbackConstruct fallback) :=
  match returned.2.1 with
  | .yield _ _ => none
  | _ => some returned

def rearm (returned : Returned construct callbackConstruct fallback) :=
  BodyCallProtocol.packet construct callbackConstruct fallback returned.2.2.val

def consume (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (context : List (List Output) × Context) (returned : Returned construct callbackConstruct fallback) :
    Bool × (List (List Output) × Context) :=
  let decision := accept context.2 returned
  (decision.1, (if decision.1 then context.1 ++ returned.2.1.rows else context.1, decision.2))

/-- The output list contains accepted occurrences only. Future work remains
the real indexed provider/client outcome, including its captured frames. -/
def provider (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context) :=
  Retained.provider (BodyCallProtocol.provider construct callbackConstruct fallback)
    (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩
    (BodyCallProtocol.requestCharge construct callbackConstruct fallback) quantum
    (isReturn construct callbackConstruct fallback) (rearm construct callbackConstruct fallback)
    (consume construct callbackConstruct fallback accept)

def sound (state : State construct callbackConstruct fallback (Context := Context)) : Prop :=
  BodyCallProtocol.sourceSound construct callbackConstruct fallback state.computation.2

def view (state : State construct callbackConstruct fallback (Context := Context)) : List (List Output) :=
  state.context.1 ++ BodyCallProtocol.unacceptedRows construct callbackConstruct fallback state.computation.2

theorem step_preserves_view (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (state : State construct callbackConstruct fallback)
    (request : Request (Returned construct callbackConstruct fallback))
    (safe : sound construct callbackConstruct fallback state) :
    sound construct callbackConstruct fallback
        ((provider construct callbackConstruct fallback quantum accept).step
          (base := ()) (index := ()) state request).2 ∧
      view construct callbackConstruct fallback
        ((provider construct callbackConstruct fallback quantum accept).step
          (base := ()) (index := ()) state request).2 =
        view construct callbackConstruct fallback state := by
  cases request with
  | next =>
      dsimp only [provider]
      rw [Retained.next_retains_outcome]
      have kept := BodyCallProtocol.resume_source_view construct callbackConstruct fallback
        quantum state.computation safe
      exact ⟨kept.2, congrArg (state.context.1 ++ ·) kept.1⟩
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [provider, Retained.provider, ready]
          exact ⟨safe, True.intro⟩
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback returned with
          | false =>
              simp only [provider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨safe, True.intro⟩
          | true =>
              cases decision : (accept state.context.2 returned).1 with
              | false =>
                  simp only [provider, Retained.provider, ready, produced, consume,
                    decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨safe, rfl⟩
              | true =>
                  have readings := safe.2
                  simp only [ready, BodyCallProtocol.stateView] at readings
                  simp only [provider, Retained.provider, ready, produced, consume,
                    decision, ↓reduceIte]
                  constructor
                  · exact ⟨rfl, readings⟩
                  · simp [view, BodyCallProtocol.unacceptedRows, ready, rearm,
                      BodyCallProtocol.packet, BodyCallProtocol.replyPacket,
                      BodyCallProtocol.moveView, BodyCallProtocol.stateView, BodyCall.Move.rows, BodyCall.Move.next,
                      List.append_assoc]

/-- The existing callback sequencer preserves accepted occurrence order and
the independent source residual for every finite acceptance allowance. -/
theorem call_preserves_view (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (pending : Option (Returned construct callbackConstruct fallback))
    (state : State construct callbackConstruct fallback)
    (safe : sound construct callbackConstruct fallback state)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback quantum accept)) :
    let actual := fromCallbacks (provider construct callbackConstruct fallback quantum accept) charge
      allowance pending accepted state (terminalAfter construct callbackConstruct fallback)
    sound construct callbackConstruct fallback actual.2.2 ∧
      view construct callbackConstruct fallback actual.2.2 = view construct callbackConstruct fallback state := by
  refine fromCallbacks_invariant (provider construct callbackConstruct fallback quantum accept) charge
    (fun next => sound construct callbackConstruct fallback next ∧
      view construct callbackConstruct fallback next = view construct callbackConstruct fallback state)
    ?_ allowance accepted pending state ⟨safe, rfl⟩ (terminalAfter construct callbackConstruct fallback)
  · intro next request invariant
    have kept := step_preserves_view construct callbackConstruct fallback quantum accept next request invariant.1
    exact ⟨kept.1, kept.2.trans invariant.2⟩

def openState (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) : State construct callbackConstruct fallback (Context := Context) :=
  ⟨(0, .paused (BodyCallProtocol.packet construct callbackConstruct fallback
    (BodyCall.openState authored items parameter (.observe .noAnswers)))), ([], context)⟩

theorem call_open_preserves_source (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback quantum accept)) :
    view construct callbackConstruct fallback
      (fromCallbacks (provider construct callbackConstruct fallback quantum accept) charge
        allowance none accepted (openState construct callbackConstruct fallback authored items parameter context)
        (terminalAfter construct callbackConstruct fallback)).2.2 =
      source construct callbackConstruct authored items parameter := by
  have preserved := call_preserves_view construct callbackConstruct fallback quantum allowance accepted
    accept none (openState construct callbackConstruct fallback authored items parameter context)
    (by
      constructor
      · rfl
      · simp [openState, BodyCallProtocol.stateView, BodyCallProtocol.packet,
          BodyCallProtocol.replyPacket, BodyCall.Move.next, BodyCall.openState, BodyCall.sourceReadings_cons,
          BodyCall.Cursor.sourceReading, openFrontier]) charge
  exact preserved.2.trans (BodyCall.openState_rows construct callbackConstruct authored items parameter)

#print axioms step_preserves_view
#print axioms call_preserves_view
#print axioms call_open_preserves_source

namespace Controls

def warming (ready : Bool) (_ : Returned Nat.add (fun _ left _ => left) (fun _ _ => [])) :
    Bool × Bool := (ready, true)

abbrev actual (quantum : Nat) :=
  provider Nat.add (fun _ left _ => left) (fun _ _ => []) quantum warming

def initial : State Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  openState Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.paired [] 0 false

def refused := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0 initial
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

/-- A paid pending projection can be retried with no source inspections. -/
def retried := resumeCall (actual 0) (fun _ _ => 1) 1 refused
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def continued := resumeCall (actual 64) (fun _ _ => 1) 1 retried
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem real_return_refusal_and_zero_quantum_retry :
    refused.2.1.pending.isSome = true ∧ refused.2.1.accepted = 0 ∧
      refused.2.2.context = ([], true) ∧
      retried.2.1.pending.isNone = true ∧ retried.2.1.accepted = 1 ∧
      retried.2.2.context = ([[1, 2]], true) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 := by decide

theorem zero_acceptance_allowance_is_inert :
    resumeCall (actual 0) (fun _ _ => 1) 0 refused
      (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => [])) = refused :=
  resumeCall_zero _ _ _ _

theorem accepted_yield_does_not_certify_exhaustion :
    retried.2.1.terminal.isNone = true ∧
      (BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => [])
        retried.2.2.computation.2).phase = .running ∧
      continued.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished ∧
      continued.2.2.context.1 = [[1, 2]] ∧ continued.2.1.accepted = 1 := by decide

def replayed := fromCallbacks (actual 64) (fun _ _ => 1) 1 none retried.2.1.accepted
  { retried.2.2 with computation := initial.computation }
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem restarting_the_source_replays_an_accepted_occurrence :
    replayed.2.2.context.1 = [[1, 2], [1, 2]] ∧
      continued.2.2.context.1 = [[1, 2]] ∧
      replayed.2.2.context.1 ≠ continued.2.2.context.1 := by decide

def atReading (authored : List (Equation Nat)) (reading : NoRuleReading) :
    State Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  ⟨(0, .paused (BodyCallProtocol.packet Nat.add (fun _ left _ => left) (fun _ _ => [])
    (BodyCall.openState authored [] 0 reading))), ([], false)⟩

def declined := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading BodyCallRun.missedCons .decline)
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def handedOff := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading BodyCallRun.alienAppend (.observe .noAnswers))
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def finished := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading BodyCallRun.missedCons (.observe .noAnswers))
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem terminal_records_keep_distinct_producer_phases :
    declined.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .declined ∧
      handedOff.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .handoff ∧
      finished.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished ∧
      declined.2.1.accepted = 0 ∧ handedOff.2.1.accepted = 0 ∧ finished.2.1.accepted = 0 := by decide

def finalRefused := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading [] (.observe .retainFallback))
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def finalRetried := resumeCall (actual 0) (fun _ _ => 1) 1 finalRefused
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem final_return_keeps_its_loan_until_acceptance :
    finalRefused.2.1.pending.isSome = true ∧ finalRefused.2.1.terminal.isNone = true ∧
      finalRefused.2.1.accepted = 0 ∧
      (BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => [])
        finalRefused.2.2.computation.2).phase = .finished ∧
      finalRetried.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished ∧
      finalRetried.2.1.pending.isNone = true ∧ finalRetried.2.1.accepted = 1 ∧
      finalRetried.2.2.context.1 = [[]] ∧
      finalRetried.2.2.computation.1 = finalRefused.2.2.computation.1 := by decide

def recursiveCalls := fromCallbacks (actual 64) (fun _ _ => 1) 3 none 0
  (openState Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.called [0] 0 true)
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem recursive_occurrences_are_accepted_in_source_order :
    recursiveCalls.2.2.context.1 = [[7, 1], [8, 1]] ∧ recursiveCalls.2.1.accepted = 2 ∧
      recursiveCalls.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished := by decide

#print axioms real_return_refusal_and_zero_quantum_retry
#print axioms zero_acceptance_allowance_is_inert
#print axioms accepted_yield_does_not_certify_exhaustion
#print axioms restarting_the_source_replays_an_accepted_occurrence
#print axioms terminal_records_keep_distinct_producer_phases
#print axioms final_return_keeps_its_loan_until_acceptance
#print axioms recursive_occurrences_are_accepted_in_source_order

end Controls

end BodyCallOwned

namespace BodyCallAdmission

open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Call := Nat ×
  (Result (BodyCallOwned.Returned construct callbackConstruct fallback)
      (BodyCallOwned.Returned construct callbackConstruct fallback) ×
    BodyCallOwned.State construct callbackConstruct fallback (Context := Context))

def quiet (state : BodyCallOwned.State construct callbackConstruct fallback (Context := Context)) : Prop :=
  BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback state.computation.2)

theorem step_quiet (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (state : BodyCallOwned.State construct callbackConstruct fallback)
    (request : Request (BodyCallOwned.Returned construct callbackConstruct fallback))
    (initial : quiet construct callbackConstruct fallback state) :
    quiet construct callbackConstruct fallback
      ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
        (base := ()) (index := ()) state request).2 := by
  cases request with
  | next =>
      dsimp only [BodyCallOwned.provider]
      rw [Retained.next_retains_outcome]
      exact BodyCallProtocol.resume_finishedQuiet construct callbackConstruct fallback
        quantum state.computation initial
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet => simpa [BodyCallOwned.provider, Retained.provider, ready] using initial
      | done returned =>
          cases produced : BodyCallOwned.isReturn construct callbackConstruct fallback returned <;>
            cases accepted : (accept state.context.2 returned).1 <;>
            simpa [quiet, BodyCallOwned.provider, Retained.provider, ready, produced,
              BodyCallOwned.consume, accepted, BodyCallOwned.rearm, BodyCallProtocol.packet,
              BodyCallProtocol.replyPacket, BodyCallProtocol.stateView, BodyCall.Move.next] using initial

theorem call_quiet (quantum allowance accepted : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (pending : Option (BodyCallOwned.Returned construct callbackConstruct fallback))
    (state : BodyCallOwned.State construct callbackConstruct fallback)
    (initial : quiet construct callbackConstruct fallback state)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept)) :
    quiet construct callbackConstruct fallback
      (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
        allowance pending accepted state (BodyCallOwned.terminalAfter construct callbackConstruct fallback)).2.2 :=
  fromCallbacks_invariant _ charge (quiet construct callbackConstruct fallback)
    (step_quiet construct callbackConstruct fallback quantum accept) allowance accepted pending state initial _

theorem open_quiet (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) :
    quiet construct callbackConstruct fallback
      (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context) := by
  simp [quiet, BodyCallOwned.openState, BodyCallProtocol.finishedQuiet, BodyCallProtocol.stateView,
    BodyCallProtocol.packet, BodyCallProtocol.replyPacket, BodyCall.Move.next, BodyCall.openState]

/-- Resume the actual callback cut, including its paid accounts, retained
loan, context and indexed provider state. No previous grant is retained. -/
def resume (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    Call construct callbackConstruct fallback (Context := Context) :=
  resumeCall (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
    allowance previous (BodyCallOwned.terminalAfter construct callbackConstruct fallback)

theorem resume_preserves (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (safe : BodyCallOwned.sound construct callbackConstruct fallback previous.2.2)
    (earned : quiet construct callbackConstruct fallback previous.2.2) :
    let later := resume construct callbackConstruct fallback quantum allowance accept charge previous
    BodyCallOwned.sound construct callbackConstruct fallback later.2.2 ∧
      quiet construct callbackConstruct fallback later.2.2 ∧
      BodyCallOwned.view construct callbackConstruct fallback later.2.2 =
        BodyCallOwned.view construct callbackConstruct fallback previous.2.2 := by
  unfold resume resumeCall
  cases previous.2.1.terminal with
  | some reason => exact ⟨safe, earned, rfl⟩
  | none =>
      have kept := BodyCallOwned.call_preserves_view construct callbackConstruct fallback
        quantum allowance previous.2.1.accepted accept previous.2.1.pending previous.2.2 safe charge
      exact ⟨kept.1, call_quiet construct callbackConstruct fallback quantum allowance
        previous.2.1.accepted accept previous.2.1.pending previous.2.2 earned charge, kept.2⟩

theorem resume_zero (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    resume construct callbackConstruct fallback quantum 0 accept charge previous = previous :=
  resumeCall_zero _ _ _ _

theorem resume_accounts (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context)) :
    let later := resume construct callbackConstruct fallback quantum allowance accept charge previous
    previous.1 ≤ later.1 ∧ previous.2.1.accepted ≤ later.2.1.accepted ∧
      later.2.1.accepted ≤ previous.2.1.accepted + allowance :=
  ⟨resumeCall_charge_mono (BodyCallOwned.provider construct callbackConstruct fallback quantum accept)
      charge allowance previous _,
    resumeCall_acceptance_bound (BodyCallOwned.provider construct callbackConstruct fallback quantum accept)
      charge allowance previous _⟩

/-- One held-loan attempt performs exactly the existing accept operation.
There is no next request, including when the callback changes its context. -/
theorem pending_resume_accept_only (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback)
    (running : previous.2.1.terminal = none) (pending : previous.2.1.pending = some loan) :
    let later := resume construct callbackConstruct fallback quantum 1 accept charge previous
    later.1 = previous.1 + charge (base := ()) (index := ()) previous.2.2 (.accept loan) ∧
      later.2.2 = ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
        (base := ()) (index := ()) previous.2.2 (.accept loan)).2 := by
  cases decision : ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
    (base := ()) (index := ()) previous.2.2 (.accept loan)).1 <;>
    cases final : BodyCallOwned.terminalAfter construct callbackConstruct fallback loan <;>
    simp [resume, resumeCall, running, fromCallbacks, pending, decision, final] <;> rfl

theorem acknowledgment_keeps_source (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (state : BodyCallOwned.State construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback) :
    let later := ((BodyCallOwned.provider construct callbackConstruct fallback quantum accept).step
      (base := ()) (index := ()) state (.accept loan)).2
    later.computation.1 = state.computation.1 ∧
      BodyCallProtocol.stateView construct callbackConstruct fallback later.computation.2 =
        BodyCallProtocol.stateView construct callbackConstruct fallback state.computation.2 := by
  cases ready : state.computation.2 with
  | paused packet => simp [BodyCallOwned.provider, Retained.provider, ready]
  | done returned =>
      cases produced : BodyCallOwned.isReturn construct callbackConstruct fallback returned <;>
        cases accepted : (accept state.context.2 returned).1 <;>
        simp [BodyCallOwned.provider, Retained.provider, ready, produced, BodyCallOwned.consume,
          accepted, BodyCallOwned.rearm, BodyCallProtocol.stateView, BodyCallProtocol.packet,
          BodyCallProtocol.replyPacket, BodyCall.Move.next]

theorem pending_resume_keeps_source (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback)
    (running : previous.2.1.terminal = none) (pending : previous.2.1.pending = some loan) :
    let later := resume construct callbackConstruct fallback quantum 1 accept charge previous
    later.2.2.computation.1 = previous.2.2.computation.1 ∧
      BodyCallProtocol.stateView construct callbackConstruct fallback later.2.2.computation.2 =
        BodyCallProtocol.stateView construct callbackConstruct fallback previous.2.2.computation.2 := by
  have only := pending_resume_accept_only construct callbackConstruct fallback quantum accept charge
    previous loan running pending
  dsimp only
  rw [only.2]
  exact acknowledgment_keeps_source construct callbackConstruct fallback quantum accept previous.2.2 loan

/-- A rejected final loan keeps the exact retained computation. Only the
consumer context and the paid callback account may change. -/
theorem pending_refusal (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (loan : BodyCallOwned.Returned construct callbackConstruct fallback) (context : Context)
    (running : previous.2.1.terminal = none) (pending : previous.2.1.pending = some loan)
    (ready : previous.2.2.computation.2 = .done loan)
    (produced : BodyCallOwned.isReturn construct callbackConstruct fallback loan = true)
    (refused : accept previous.2.2.context.2 loan = (false, context)) :
    resume construct callbackConstruct fallback quantum (allowance+1) accept charge previous =
      (previous.1 + charge (base := ()) (index := ()) previous.2.2 (.accept loan),
        ⟨none, some loan, previous.2.1.accepted⟩,
        ⟨previous.2.2.computation, (previous.2.2.context.1, context)⟩) := by
  simp [resume, resumeCall, fromCallbacks, running, pending, BodyCallOwned.provider,
    Retained.provider, ready, produced, BodyCallOwned.consume, refused]

def openCall (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) : Call construct callbackConstruct fallback (Context := Context) :=
  (0, ⟨none, none, 0⟩, BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)

/-- The source account includes the accepted prefix and the actual retained
reply and frames. Completion is not assumed by this invariant. -/
def captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context)) : Prop :=
  BodyCallOwned.sound construct callbackConstruct fallback call.2.2 ∧
    quiet construct callbackConstruct fallback call.2.2 ∧
    BodyCallOwned.view construct callbackConstruct fallback call.2.2 =
      source construct callbackConstruct authored items parameter

theorem open_captured (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) :
    captured construct callbackConstruct fallback authored items parameter
      (openCall construct callbackConstruct fallback authored items parameter context) := by
  refine ⟨?_, open_quiet construct callbackConstruct fallback authored items parameter context, ?_⟩
  · constructor
    · rfl
    · simp [openCall, BodyCallOwned.openState, BodyCallProtocol.stateView,
        BodyCallProtocol.packet, BodyCallProtocol.replyPacket, BodyCall.Move.next,
        BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]
  · exact BodyCall.openState_rows construct callbackConstruct authored items parameter

theorem resume_captured (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (previous : Call construct callbackConstruct fallback (Context := Context))
    (initial : captured construct callbackConstruct fallback authored items parameter previous) :
    captured construct callbackConstruct fallback authored items parameter
      (resume construct callbackConstruct fallback quantum allowance accept charge previous) := by
  have kept := resume_preserves construct callbackConstruct fallback quantum allowance accept charge previous
    initial.1 initial.2.1
  exact ⟨kept.1, kept.2.1, kept.2.2.trans initial.2.2⟩

/-- An external schedule supplies a source inspection quantum, a successful
return allowance and a possibly different callback at each resumption. -/
abbrev Grant := Nat × Nat ×
  (Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)

def schedule
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (initial : Call construct callbackConstruct fallback (Context := Context)) :
    Call construct callbackConstruct fallback (Context := Context) :=
  grants.foldl (fun previous grant => resume construct callbackConstruct fallback
    grant.1 grant.2.1 grant.2.2 (charge grant.1 grant.2.2) previous) initial

theorem schedule_captured
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (initial : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback authored items parameter initial) :
    captured construct callbackConstruct fallback authored items parameter
      (schedule construct callbackConstruct fallback charge grants initial) := by
  induction grants generalizing initial with
  | nil => exact safe
  | cons grant grants ih =>
      exact ih _ (resume_captured construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) authored items parameter initial safe)

theorem schedule_open_captured
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    captured construct callbackConstruct fallback authored items parameter
      (schedule construct callbackConstruct fallback charge grants
        (openCall construct callbackConstruct fallback authored items parameter context)) :=
  schedule_captured construct callbackConstruct fallback charge grants authored items parameter _
    (open_captured construct callbackConstruct fallback authored items parameter context)

theorem schedule_accounts
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (initial : Call construct callbackConstruct fallback (Context := Context)) :
    initial.1 ≤ (schedule construct callbackConstruct fallback charge grants initial).1 ∧
      initial.2.1.accepted ≤ (schedule construct callbackConstruct fallback charge grants initial).2.1.accepted := by
  induction grants generalizing initial with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons grant grants ih =>
      have first := resume_accounts construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) initial
      have rest := ih (resume construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) initial)
      exact ⟨first.1.trans rest.1, first.2.1.trans rest.2⟩

/-- Completion reads only the earned terminal record and retained loan cut.
The proof of quiet finished work is supplied by the actual cursor invariant. -/
def complete (call : Call construct callbackConstruct fallback (Context := Context)) : Bool :=
  call.2.1.pending.isNone &&
    match call.2.1.terminal with
    | none => false
    | some returned => match returned.2.1 with
      | .finish _ _ =>
          decide ((BodyCallProtocol.stateView construct callbackConstruct fallback call.2.2.computation.2).phase =
            .finished) &&
          (BodyCallProtocol.moveView construct callbackConstruct fallback call.2.2.computation.2).rows.isEmpty
      | _ => false

def readout (call : Call construct callbackConstruct fallback (Context := Context))
    (_quiet : quiet construct callbackConstruct fallback call.2.2) :
    Option (List (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  (if complete construct callbackConstruct fallback call then some call.2.2.context.1 else none, call)

theorem readout_retains_call (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    (readout construct callbackConstruct fallback call earned).2 = call := rfl

theorem complete_cut (call : Call construct callbackConstruct fallback (Context := Context))
    (completed : complete construct callbackConstruct fallback call = true) :
    (BodyCallProtocol.stateView construct callbackConstruct fallback call.2.2.computation.2).phase = .finished ∧
      (BodyCallProtocol.moveView construct callbackConstruct fallback call.2.2.computation.2).rows = [] := by
  unfold complete at completed
  have stopped := (Bool.and_eq_true_iff.mp completed).2
  cases terminal : call.2.1.terminal with
  | none => simp [terminal] at stopped
  | some returned =>
      cases moved : returned.2.1 <;> simp only [terminal, moved] at stopped
      all_goals first
        | contradiction
        | exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp stopped).1,
            List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp stopped).2⟩

theorem completed_view (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (completed : complete construct callbackConstruct fallback call = true) :
    BodyCallOwned.view construct callbackConstruct fallback call.2.2 = call.2.2.context.1 := by
  obtain ⟨finished, noLoan⟩ := complete_cut construct callbackConstruct fallback call completed
  simp [BodyCallOwned.view, BodyCallProtocol.unacceptedRows, noLoan, earned finished]

/-- A completed cut cannot invoke either the producer or a replacement
consumer. It keeps even the original terminal record and paid accounts. -/
theorem completed_resume_inert (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (completed : complete construct callbackConstruct fallback call = true) :
    resume construct callbackConstruct fallback quantum allowance accept charge call = call := by
  unfold complete at completed
  cases stopped : call.2.1.terminal with
  | none => simp [stopped] at completed
  | some returned => simp [resume, resumeCall, stopped]

theorem readout_call_eq_source (quantum allowance accepted : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (completed : complete construct callbackConstruct fallback
      (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
        allowance none accepted (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)
        (BodyCallOwned.terminalAfter construct callbackConstruct fallback)) = true) :
    (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
      allowance none accepted (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)
      (BodyCallOwned.terminalAfter construct callbackConstruct fallback)).2.2.context.1 =
      source construct callbackConstruct authored items parameter := by
  have preserved := BodyCallOwned.call_open_preserves_source construct callbackConstruct fallback
    quantum allowance accepted accept authored items parameter context charge
  have quiet := call_quiet construct callbackConstruct fallback quantum allowance accepted accept none _
    (open_quiet construct callbackConstruct fallback authored items parameter context) charge
  rw [completed_view construct callbackConstruct fallback _ quiet completed] at preserved
  exact preserved

#print axioms step_quiet
#print axioms call_quiet
#print axioms complete_cut
#print axioms completed_view
#print axioms readout_call_eq_source

def workerMode : SelectedWorker Output → CallingConvention
  | .directCode _ => .direct
  | .optionalCode _ => .optional
  | .bodyCall summary | .reference summary => summary

theorem selectSourceWorker_mode (authored : List (Equation Output)) (summary : CallingConvention) :
    workerMode (selectSourceWorker authored summary) = summary := by
  unfold selectSourceWorker
  split <;> rfl

theorem selected_mode_sound (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (interface : ScalarResultInterface) :
    ConventionAllows (workerMode (selectWorker authored items parameter interface))
      (source construct callbackConstruct authored items parameter).length := by
  cases built : compile authored with
  | some code =>
      obtain ⟨result, sourceDone, _⟩ := compile_bounded_correct construct callbackConstruct authored code built items parameter
      simp [selectWorker_compiler_projections, built, workerMode, sourceDone, ConventionAllows]
  | none =>
      by_cases single : interface = .singleValue
      · simpa only [selectWorker_compiler_projections, built, single, ↓reduceIte, selectSourceWorker_mode] using
          preparation_convention_sound construct callbackConstruct authored items parameter
      · cases optional : compileOptionalTree authored with
        | none =>
            simpa only [selectWorker_compiler_projections, built, single, ↓reduceIte, optional, selectSourceWorker_mode] using
              preparation_convention_sound construct callbackConstruct authored items parameter
        | some tree =>
            simp only [selectWorker_compiler_projections, built, single, ↓reduceIte, optional, workerMode]
            rw [← optionalRun_refines_source construct callbackConstruct authored tree optional items parameter]
            cases optionalRun construct callbackConstruct tree items parameter <;> simp [ConventionAllows]

/-- A receiving calling mode may represent a stronger inferred convention.
The optional scalar interface is still required to represent absence. -/
def modeEligible (requested inferred : CallingConvention) (interface : ScalarResultInterface) : Bool :=
  match requested, inferred, interface with
  | .direct, .direct, _ => true
  | .optional, .direct, .optionalValue | .optional, .optional, .optionalValue => true
  | .nonemptyProducer, .direct, _ | .nonemptyProducer, .nonemptyProducer, _ => true
  | .producer, _, _ => true
  | _, _, _ => false

theorem modeEligible_sound (requested inferred : CallingConvention) (interface : ScalarResultInterface)
    (count : Nat) (eligible : modeEligible requested inferred interface = true)
    (bounded : ConventionAllows inferred count) : ConventionAllows requested count := by
  cases requested <;> cases inferred <;> cases interface <;>
    simp_all [modeEligible, ConventionAllows]

def admit (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (List (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  match (readout construct callbackConstruct fallback call earned).1 with
  | none => (none, call)
  | some answers =>
      if modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface then
        (some answers, call) else (none, call)

theorem admit_retains_call (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    (admit construct callbackConstruct fallback requested interface authored items parameter call earned).2 = call := by
  unfold admit
  split
  · rfl
  · split <;> rfl

theorem admit_some_iff (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) (answers : List (List Output)) :
    (admit construct callbackConstruct fallback requested interface authored items parameter call earned).1 = some answers ↔
      complete construct callbackConstruct fallback call = true ∧
      modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface = true ∧
      call.2.2.context.1 = answers := by
  cases done : complete construct callbackConstruct fallback call <;>
    cases eligible : modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface <;>
    simp [admit, readout, done, eligible]

theorem admit_license (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (captured : BodyCallOwned.view construct callbackConstruct fallback call.2.2 =
      source construct callbackConstruct authored items parameter)
    (answers : List (List Output))
    (admitted : (admit construct callbackConstruct fallback requested interface authored items parameter call earned).1 =
      some answers) :
    answers = source construct callbackConstruct authored items parameter ∧ ConventionAllows requested answers.length := by
  obtain ⟨done, eligible, same⟩ := (admit_some_iff construct callbackConstruct fallback requested interface
    authored items parameter call earned answers).mp admitted
  have actual : answers = source construct callbackConstruct authored items parameter := by
    rw [completed_view construct callbackConstruct fallback call earned done] at captured
    exact same.symm.trans captured
  refine ⟨actual, ?_⟩
  rw [actual]
  exact modeEligible_sound _ _ _ _ eligible (selected_mode_sound construct callbackConstruct authored items parameter interface)

/-- This license is obtained from the actual owned callback computation,
not an assumption that its accepted rows already equal the source. -/
theorem actual_call_license (quantum allowance accepted : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let call := fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum accept) charge
      allowance none accepted (BodyCallOwned.openState construct callbackConstruct fallback authored items parameter context)
      (BodyCallOwned.terminalAfter construct callbackConstruct fallback)
    let earned := call_quiet construct callbackConstruct fallback quantum allowance accepted accept none _
      (open_quiet construct callbackConstruct fallback authored items parameter context) charge
    ∀ answers, (admit construct callbackConstruct fallback requested interface authored items parameter call earned).1 =
      some answers → answers = source construct callbackConstruct authored items parameter ∧
      ConventionAllows requested answers.length := by
  intro call earned answers admitted
  exact admit_license construct callbackConstruct fallback requested interface authored items parameter call earned
    (BodyCallOwned.call_open_preserves_source construct callbackConstruct fallback quantum allowance accepted accept
      authored items parameter context charge) answers admitted

/-- Every finite sequence of actual resumptions earns the same four calling
mode licenses. Callback changes and refused grants are included in the
schedule induction; no accepted-source equality is an input. -/
theorem resumed_call_license
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let call := schedule construct callbackConstruct fallback charge grants
      (openCall construct callbackConstruct fallback authored items parameter context)
    let safe := schedule_open_captured construct callbackConstruct fallback charge grants authored items parameter context
    ∀ answers, (admit construct callbackConstruct fallback requested interface authored items parameter call safe.2.1).1 =
      some answers → answers = source construct callbackConstruct authored items parameter ∧
      ConventionAllows requested answers.length := by
  intro call safe answers admitted
  exact admit_license construct callbackConstruct fallback requested interface authored items parameter call
    safe.2.1 safe.2.2 answers admitted

theorem resumed_completed_admission
    (charge : ∀ (quantum : Nat)
      (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let call := schedule construct callbackConstruct fallback charge grants
      (openCall construct callbackConstruct fallback authored items parameter context)
    let safe := schedule_open_captured construct callbackConstruct fallback charge grants authored items parameter context
    complete construct callbackConstruct fallback call = true →
      modeEligible requested (workerMode (selectWorker authored items parameter interface)) interface = true →
      admit construct callbackConstruct fallback requested interface authored items parameter call safe.2.1 =
        (some (source construct callbackConstruct authored items parameter), call) := by
  intro call safe completed eligible
  apply Prod.ext
  · apply (admit_some_iff construct callbackConstruct fallback requested interface authored items parameter
      call safe.2.1 _).mpr
    refine ⟨completed, eligible, ?_⟩
    have independent := safe.2.2
    rw [completed_view construct callbackConstruct fallback call safe.2.1 completed] at independent
    exact independent
  · exact admit_retains_call construct callbackConstruct fallback requested interface authored items parameter call safe.2.1

theorem direct_license (answers : List (List Output)) (licensed : ConventionAllows .direct answers.length) :
    ∃ answer, answers = [answer] := List.length_eq_one_iff.mp licensed

theorem optional_license (answers : List (List Output)) (licensed : ConventionAllows .optional answers.length) :
    ∃ answer : Option (List Output), answers = answer.toList := by
  cases answers with
  | nil => exact ⟨none, rfl⟩
  | cons answer rest =>
      cases rest with
      | nil => exact ⟨some answer, rfl⟩
      | cons next rest => simp [ConventionAllows] at licensed

theorem nonempty_license (answers : List (List Output))
    (licensed : ConventionAllows .nonemptyProducer answers.length) : answers ≠ [] := by
  intro empty
  simp [ConventionAllows, empty] at licensed

def directValue (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (List Output) × Call construct callbackConstruct fallback (Context := Context) :=
  ((admit construct callbackConstruct fallback .direct .singleValue authored items parameter call earned).1.bind
    (fun answers => match answers with | [answer] => some answer | _ => none), call)

def optionalValue (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (Option (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  ((admit construct callbackConstruct fallback .optional .optionalValue authored items parameter call earned).1.bind
    (fun answers => match answers with | [] => some none | [answer] => some (some answer) | _ => none), call)

theorem directValue_of_admitted (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) (answer : List Output)
    (admitted : (admit construct callbackConstruct fallback .direct .singleValue
      authored items parameter call earned).1 = some [answer]) :
    directValue construct callbackConstruct fallback authored items parameter call earned = (some answer, call) := by
  simp [directValue, admitted]

theorem optionalValue_of_admitted (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) (answer : Option (List Output))
    (admitted : (admit construct callbackConstruct fallback .optional .optionalValue
      authored items parameter call earned).1 = some answer.toList) :
    optionalValue construct callbackConstruct fallback authored items parameter call earned = (some answer, call) := by
  cases answer <;> simp [optionalValue, admitted]

/-- Freshness gates new dispatch eligibility. It does not alter the earned
captured-world readout or its full original call. -/
def liveAdmission {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size)
    (reader : Fin size) (requested : CallingConvention) (interface : ScalarResultInterface)
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2) :
    Option (List (List Output)) × Call construct callbackConstruct fallback (Context := Context) :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) then
    admit construct callbackConstruct fallback requested interface (OrderedDependencyStore.query before reader)
      items parameter call earned
  else (none, call)

theorem stale_refuses_new_admission {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (requested : CallingConvention) (interface : ScalarResultInterface) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (stale : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = false) :
    liveAdmission construct callbackConstruct fallback before current reader requested interface items parameter call earned =
      (none, call) := by simp [liveAdmission, stale]

theorem fresh_live_license {size : Nat}
    (world : OrderedDependencyStore.Store (Equation Output) size)
    (invariant : OrderedDependencyStore.ObserverInvariant world)
    (actions : List (OrderedDependencyStore.Action (Equation Output) size)) (reader : Fin size)
    (requested : CallingConvention) (interface : ScalarResultInterface) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (earned : quiet construct callbackConstruct fallback call.2.2)
    (captured : BodyCallOwned.view construct callbackConstruct fallback call.2.2 =
      source construct callbackConstruct (OrderedDependencyStore.query world reader) items parameter)
    (answers : List (List Output))
    (admitted : (liveAdmission construct callbackConstruct fallback world
      (OrderedDependencyStore.execute world actions) reader requested interface items parameter call earned).1 = some answers) :
    answers = source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute world actions) reader) items parameter ∧
      ConventionAllows requested answers.length := by
  unfold liveAdmission at admitted
  split at admitted
  next valid =>
    have licensed := admit_license construct callbackConstruct fallback requested interface
      (OrderedDependencyStore.query world reader) items parameter call earned captured answers admitted
    constructor
    · rw [OrderedDependencyStore.validated_query world invariant actions reader valid]
      exact licensed.1
    · exact licensed.2
  next stale => cases admitted

#print axioms open_quiet
#print axioms readout_retains_call
#print axioms selectSourceWorker_mode
#print axioms admit_retains_call
#print axioms admit_some_iff
#print axioms directValue_of_admitted
#print axioms optionalValue_of_admitted
#print axioms fresh_live_license
#print axioms selected_mode_sound
#print axioms modeEligible_sound
#print axioms admit_license
#print axioms actual_call_license
#print axioms direct_license
#print axioms optional_license
#print axioms nonempty_license
#print axioms stale_refuses_new_admission

#print axioms resume_preserves
#print axioms resume_zero
#print axioms resume_accounts
#print axioms pending_resume_accept_only
#print axioms acknowledgment_keeps_source
#print axioms pending_resume_keeps_source
#print axioms pending_refusal
#print axioms open_captured
#print axioms resume_captured
#print axioms schedule_captured
#print axioms schedule_open_captured
#print axioms schedule_accounts
#print axioms completed_resume_inert
#print axioms resumed_call_license
#print axioms resumed_completed_admission

namespace CurrentAuthority

open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open _root_.CategoryTheory
open scoped Mettapedia.GSLT.SeparationAlgebra

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)

/-- Admission to new source work checks both the captured dependency stamp
and the current resource conversion. The flag reports admission, not progress
or producer completion. Denial preserves the whole retained call. Authority
is not updated here: this tests eligibility, not consumption or arbitration. -/
def resume {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context)) :
    Bool × Call construct callbackConstruct fallback (Context := Context) :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) then
    if FrameUpdate point.authority required then
      (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call)
    else (false, call)
  else (false, call)

theorem granted {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true)
    (permission : FrameUpdate point.authority required) :
    resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call =
      (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call) := by
  simp [resume, fresh, permission]

theorem refused {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (denied : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = false ∨
      ¬ FrameUpdate point.authority required) :
    resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call = (false, call) := by
  rcases denied with stale | revoked
  · simp [resume, stale]
  · simp [resume, revoked]

theorem admitted_iff {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context)) :
    (resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call).1 = true ↔
      OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true ∧
        FrameUpdate point.authority required := by
  cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) <;>
    by_cases permitted : FrameUpdate point.authority required <;> simp [resume, fresh, permitted]

theorem preserves_captured {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter call) :
    captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter
      (resume construct callbackConstruct fallback authority before current reader point required
        quantum allowance accept charge call).2 := by
  unfold resume
  split
  · split
    · exact resume_captured construct callbackConstruct fallback quantum allowance accept charge _ items parameter call safe
    · exact safe
  · exact safe

theorem admitted_current_source {size : Nat}
    (before : OrderedDependencyStore.Store (Equation Output) size)
    (observers : OrderedDependencyStore.ObserverInvariant before)
    (actions : List (OrderedDependencyStore.Action (Equation Output) size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter call)
    (admitted : (resume construct callbackConstruct fallback authority before
      (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge call).1 = true) :
    BodyCallOwned.view construct callbackConstruct fallback
      (resume construct callbackConstruct fallback authority before (OrderedDependencyStore.execute before actions)
        reader point required quantum allowance accept charge call).2.2.2 =
      source construct callbackConstruct
        (OrderedDependencyStore.query (OrderedDependencyStore.execute before actions) reader) items parameter := by
  have current := (admitted_iff construct callbackConstruct fallback authority before
    (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge call).mp admitted
  have kept := preserves_captured construct callbackConstruct fallback authority before
    (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge items parameter call safe
  rw [OrderedDependencyStore.validated_query before observers actions reader current.1]
  exact kept.2.2

/-- The existing calling-mode readout is licensed against the current
authored query after an actually admitted retained resumption. -/
theorem current_mode_license {size : Nat}
    (before : OrderedDependencyStore.Store (Equation Output) size)
    (observers : OrderedDependencyStore.ObserverInvariant before)
    (actions : List (OrderedDependencyStore.Action (Equation Output) size)) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : captured construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter call)
    (requested : CallingConvention) (interface : ScalarResultInterface) :
    let actual := resume construct callbackConstruct fallback authority before
      (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge call
    let kept := preserves_captured construct callbackConstruct fallback authority before
      (OrderedDependencyStore.execute before actions) reader point required quantum allowance accept charge items parameter call safe
    actual.1 = true → ∀ answers,
      (admit construct callbackConstruct fallback requested interface
        (OrderedDependencyStore.query (OrderedDependencyStore.execute before actions) reader)
        items parameter actual.2 kept.2.1).1 = some answers →
      answers = source construct callbackConstruct
          (OrderedDependencyStore.query (OrderedDependencyStore.execute before actions) reader) items parameter ∧
        ConventionAllows requested answers.length := by
  intro actual kept admitted answers read
  exact admit_license construct callbackConstruct fallback requested interface _ items parameter actual.2 kept.2.1
    (admitted_current_source construct callbackConstruct fallback authority before observers actions reader point required
      quantum allowance accept charge items parameter call safe admitted) answers read

theorem completed_call_kept {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (completed : complete construct callbackConstruct fallback call = true) :
    (resume construct callbackConstruct fallback authority before current reader point required
      quantum allowance accept charge call).2 = call := by
  have inert := completed_resume_inert construct callbackConstruct fallback quantum allowance accept charge call completed
  unfold resume
  split
  · split
    · exact inert
    · rfl
  · rfl

/-- Legal updates and world transport compose before the actual entry test.
The target must still hold the required current right. -/
theorem composite_granted {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (first middle last : IndexedAuthority.Point authority) (left : first ⟶ middle) (right : middle ⟶ last)
    (required : authority.Fibre last.world)
    [permissionDecidable : Decidable (FrameUpdate (authority.transport (left.1 ≫ right.1) first.authority) required)]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true)
    (permission : FrameUpdate last.authority required) :
    resume construct callbackConstruct fallback authority before current reader
      (IndexedAuthority.push first (left.1 ≫ right.1)) required quantum allowance accept charge call =
      (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call) := by
  have route : FrameUpdate (authority.transport (left.1 ≫ right.1) first.authority) last.authority :=
    (left ≫ right).2
  exact granted construct callbackConstruct fallback authority before current reader
    (IndexedAuthority.push first (left.1 ≫ right.1)) required
    quantum allowance accept charge call fresh (route.trans permission)

theorem framed_granted {size : Nat}
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required frame : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate (point.authority + frame) (required + frame))]
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true)
    (permission : FrameUpdate point.authority required) (separate : point.authority ## frame) :
    required ## frame ∧
      resume construct callbackConstruct fallback authority before current reader
        ⟨point.world, point.authority + frame⟩ (required + frame) quantum allowance accept charge call =
        (true, BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance accept charge call) := by
  have framed := permission.add_right separate
  exact ⟨framed.1, granted construct callbackConstruct fallback authority before current reader _ _
    quantum allowance accept charge call fresh framed.2⟩

/-- Duplicable evidence cannot become an exclusive execution right, even
after a lawful transport that erases other resources. -/
theorem selfSeparate_refuses_exclusive {size : Nat} {earlier later : World}
    (change : earlier ⟶ later) (held : authority.Fibre earlier) (required : authority.Fibre later)
    [permissionDecidable : Decidable (FrameUpdate (authority.transport change held) required)]
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (call : Call construct callbackConstruct fallback (Context := Context))
    (duplicable : held ## held) (exclusive : Exclusive required) :
    resume construct callbackConstruct fallback authority before current reader
      ⟨later, authority.transport change held⟩ required quantum allowance accept charge call = (false, call) := by
  apply refused construct callbackConstruct fallback authority before current reader
    ⟨later, authority.transport change held⟩ required
    quantum allowance accept charge call
  right
  intro permission
  have self := (authority.transport change).map_separate duplicable
  have against := permission _ self
  exact not_exclusive_of_selfSeparate
    (permission _ (SepAlgebra.separate_symm against)) exclusive

theorem exclusive_claims_conflict {world : World}
    (left right required : authority.Fibre world)
    (leftPermission : FrameUpdate left required) (rightPermission : FrameUpdate right required)
    (exclusive : Exclusive required) : ¬ left ## right := by
  intro separate
  have first := leftPermission _ separate
  exact not_exclusive_of_selfSeparate
    (rightPermission _ (SepAlgebra.separate_symm first)) exclusive

#print axioms granted
#print axioms refused
#print axioms admitted_iff
#print axioms preserves_captured
#print axioms admitted_current_source
#print axioms current_mode_license
#print axioms completed_call_kept
#print axioms composite_granted
#print axioms framed_granted
#print axioms selfSeparate_refuses_exclusive
#print axioms exclusive_claims_conflict

namespace Controls

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

local instance (held required : Access) : Decidable (FrameUpdate held required) :=
  inferInstanceAs (Decidable (∀ frame : Access, held ## frame → required ## frame))

local instance (held required : Access × Access) : Decidable (FrameUpdate held required) :=
  inferInstanceAs (Decidable (∀ frame : Access × Access,
    (held.1 ## frame.1 ∧ held.2 ## frame.2) → (required.1 ## frame.1 ∧ required.2 ## frame.2)))

def revocationDecision (world : Bool) (held required : revocationWorlds.Fibre world) :
    Decidable (@FrameUpdate (revocationWorlds.Fibre world) (revocationWorlds.zero world)
      (revocationWorlds.add world) (revocationWorlds.sep world) held required) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate held frame = true → Access.separate required frame = true))

def world : OrderedDependencyStore.Store (Equation Nat) 3 :=
  OrderedDependencyStore.link
    (OrderedDependencyStore.initial 131 (fun member => if member = 1 then BodyCallRun.blank else [])) 0 1

def newEquation : Equation Nat := ⟨⟨.any, .any⟩, false, .singleton 8⟩
def related := OrderedDependencyStore.appendOwn world 1 [newEquation]
def unrelated := OrderedDependencyStore.appendOwn world 2 [newEquation]

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked := IndexedAuthority.push held (homOfLE (by decide) : false ⟶ true)
def readOnly : IndexedAuthority.Point revocationWorlds := ⟨false, .read⟩

def initial : Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  openCall Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 true

abbrev charges (quantum : Nat) :=
  fun (_ : (BodyCallOwned.provider Nat.add (fun _ left _ => left) (fun _ _ => [])
    quantum BodyCallOwned.Controls.warming).State () ())
    (_ : Request (BodyCallOwned.Returned Nat.add (fun _ left _ => left) (fun _ _ => []))) => 1

def run (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point revocationWorlds)
    (call : Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool)) :=
  resume (permissionDecidable := revocationDecision point.world point.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world current 0 point .consume
    64 1 BodyCallOwned.Controls.warming (charges _) call

def first := run unrelated held initial
def finished := run unrelated held first.2

theorem revoked_right_refuses_unchanged_data_and_preserves_the_call :
    revoked.authority = .none ∧
      OrderedDependencyStore.checkRead world (OrderedDependencyStore.readStamp world 0) = true ∧
      run world revoked initial = (false, initial) := by
  refine ⟨rfl, by decide, ?_⟩
  exact refused (permissionDecidable := revocationDecision revoked.world revoked.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world world 0 revoked .consume
    64 1 BodyCallOwned.Controls.warming (charges _) initial (Or.inr (by change ¬ FrameUpdate Access.none Access.consume; decide))

theorem stale_data_refuses_a_current_exclusive_right :
    held.authority = .consume ∧
      OrderedDependencyStore.checkRead related (OrderedDependencyStore.readStamp world 0) = false ∧
      run related held initial = (false, initial) := by
  refine ⟨rfl, by decide, ?_⟩
  exact refused (permissionDecidable := revocationDecision held.world held.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world related 0 held .consume
    64 1 BodyCallOwned.Controls.warming (charges _) initial (Or.inl (by decide))

theorem unrelated_change_permits_real_retained_advancement :
    OrderedDependencyStore.checkRead unrelated (OrderedDependencyStore.readStamp world 0) = true ∧
      first.1 = true ∧ first.2.2.2.context.1 = [[]] ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) first.2 = false ∧
      finished.1 = true ∧ complete Nat.add (fun _ left _ => left) (fun _ _ => []) finished.2 = true := by decide

theorem initial_captured :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 initial :=
  open_captured Nat.add (fun _ left _ => left) (fun _ _ => []) _ [] 0 true

theorem first_captured :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 first.2 :=
  preserves_captured (permissionDecidable := revocationDecision held.world held.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world unrelated 0
    held .consume 64 1 BodyCallOwned.Controls.warming (charges _) [] 0 initial initial_captured

theorem finished_captured :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 finished.2 :=
  preserves_captured (permissionDecidable := revocationDecision held.world held.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world unrelated 0
    held .consume 64 1 BodyCallOwned.Controls.warming (charges _) [] 0 first.2 first_captured

theorem captured_completion_outlives_revocation_and_staleness :
    run related revoked finished.2 = (false, finished.2) ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) finished.2 finished_captured.2.1).1 = some [[]] := by
  refine ⟨?_, by decide⟩
  exact refused (permissionDecidable := revocationDecision revoked.world revoked.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world related 0 revoked .consume
    64 1 BodyCallOwned.Controls.warming (charges _) finished.2 (Or.inr (by change ¬ FrameUpdate Access.none Access.consume; decide))

theorem duplicated_read_evidence_cannot_advance :
    Access.read ## Access.read ∧ Access.read + Access.read = Access.read ∧
      run world readOnly initial = (false, initial) := by
  refine ⟨Access.read_selfSeparate, rfl, ?_⟩
  exact selfSeparate_refuses_exclusive
    (permissionDecidable := revocationDecision false (revocationWorlds.transport (𝟙 false) Access.read) Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds
    (𝟙 false) Access.read Access.consume world world 0 64 1 BodyCallOwned.Controls.warming
    (charges _) initial Access.read_selfSeparate Access.consume_exclusive

abbrev pairedAuthority := IndexedAuthority.still Bool (Access × Access)
def pairedDecision (world : Bool) (held required : pairedAuthority.Fibre world) :
    Decidable (@FrameUpdate (pairedAuthority.Fibre world) (pairedAuthority.zero world)
      (pairedAuthority.add world) (pairedAuthority.sep world) held required) :=
  inferInstanceAs (Decidable (∀ frame : Access × Access,
    (Access.separate held.1 frame.1 = true ∧ Access.separate held.2 frame.2 = true) →
      (Access.separate required.1 frame.1 = true ∧ Access.separate required.2 frame.2 = true)))

def pairedOwner : IndexedAuthority.Point pairedAuthority := ⟨false, (.consume, .none)⟩
def otherWork : pairedAuthority.Fibre pairedOwner.world := (.none, .read)

theorem unrelated_authority_frame_composes_with_execution :
    ((Access.consume, Access.none) : Access × Access) ## otherWork ∧
      resume (permissionDecidable := pairedDecision pairedOwner.world
        (pairedOwner.authority + otherWork) (pairedOwner.authority + otherWork))
        Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority world unrelated 0
        ⟨pairedOwner.world, pairedOwner.authority + otherWork⟩
        (pairedOwner.authority + otherWork)
        64 1 BodyCallOwned.Controls.warming (charges _) initial = (true, first.2) := by
  have framed := framed_granted (permissionDecidable := pairedDecision pairedOwner.world
    (pairedOwner.authority + otherWork) (pairedOwner.authority + otherWork)) Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority
    world unrelated 0 pairedOwner pairedOwner.authority otherWork 64 1 BodyCallOwned.Controls.warming
    (charges _) initial (by decide) (FrameUpdate.refl _) (by constructor <;> decide)
  exact ⟨by constructor <;> decide, framed.2⟩

def bothRights : IndexedAuthority.Point pairedAuthority := ⟨false, (.consume, .consume)⟩
def afterCrossing : IndexedAuthority.Point pairedAuthority := ⟨true, (.consume, .read)⟩
def afterRelease : IndexedAuthority.Point pairedAuthority := ⟨true, (.consume, .none)⟩

def crossing : bothRights ⟶ afterCrossing :=
  IndexedAuthority.homOf (homOfLE (by decide) : false ⟶ true) (by
    intro frame separate
    exact ⟨separate.1, Access.consume_updates_read frame.2 separate.2⟩)

def releaseOther : afterCrossing ⟶ afterRelease :=
  IndexedAuthority.homOf (𝟙 true) (by
    intro frame separate
    exact ⟨separate.1, FrameUpdate.to_zero Access.read frame.2 separate.2⟩)

theorem lawful_world_crossing_and_updates_compose_with_execution :
    resume (permissionDecidable := pairedDecision true
      (pairedAuthority.transport (crossing.1 ≫ releaseOther.1) bothRights.authority) afterRelease.authority)
      Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority world unrelated 0
      (IndexedAuthority.push bothRights (crossing.1 ≫ releaseOther.1)) afterRelease.authority
      64 1 BodyCallOwned.Controls.warming (charges _) initial = (true, first.2) :=
  composite_granted (permissionDecidable := pairedDecision true
    (pairedAuthority.transport (crossing.1 ≫ releaseOther.1) bothRights.authority) afterRelease.authority) Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority world unrelated 0
    bothRights afterCrossing afterRelease crossing releaseOther afterRelease.authority 64 1 BodyCallOwned.Controls.warming
    (charges _) initial (by decide) (FrameUpdate.refl _)

#print axioms revoked_right_refuses_unchanged_data_and_preserves_the_call
#print axioms stale_data_refuses_a_current_exclusive_right
#print axioms unrelated_change_permits_real_retained_advancement
#print axioms initial_captured
#print axioms first_captured
#print axioms finished_captured
#print axioms captured_completion_outlives_revocation_and_staleness
#print axioms duplicated_read_evidence_cannot_advance
#print axioms unrelated_authority_frame_composes_with_execution
#print axioms lawful_world_crossing_and_updates_compose_with_execution

end Controls

end CurrentAuthority

namespace Controls

def start (authored : List (Equation Nat)) (items : List Nat) (reading : NoRuleReading)
    (warm : Bool) : BodyCallOwned.State Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  ⟨(0, .paused (BodyCallProtocol.packet Nat.add (fun _ left _ => left) (fun _ _ => [])
    (BodyCall.openState authored items 0 reading))), ([], warm)⟩

def run (authored : List (Equation Nat)) (items : List Nat) (reading : NoRuleReading)
    (allowance : Nat) (warm : Bool := true) :
    Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  fromCallbacks (BodyCallOwned.Controls.actual 64) (fun _ _ => 1) allowance none 0
    (start authored items reading warm)
    (BodyCallOwned.terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem earned (authored : List (Equation Nat)) (items : List Nat) (reading : NoRuleReading)
    (allowance : Nat) (warm : Bool := true) :
    quiet Nat.add (fun _ left _ => left) (fun _ _ => []) (run authored items reading allowance warm).2.2 := by
  exact call_quiet Nat.add (fun _ left _ => left) (fun _ _ => []) 64 allowance 0
    BodyCallOwned.Controls.warming none _
    (by simp [quiet, start, BodyCallProtocol.finishedQuiet, BodyCallProtocol.stateView,
      BodyCallProtocol.packet, BodyCallProtocol.replyPacket, BodyCall.Move.next, BodyCall.openState]) (fun _ _ => 1)

def failed := run BodyCallRun.missed [] (.observe .noAnswers) 3
def emptyCollection := run BodyCallRun.blank [] (.observe .noAnswers) 3
def duplicateAnswers := run SourceProducerCardinality.Controls.duplicates [] (.observe .noAnswers) 4
def recursiveAnswers := run BodyCallRun.called [0] (.observe .noAnswers) 3
def incomplete := run BodyCallRun.paired [] (.observe .noAnswers) 1
def pendingFinal := run [] [] (.observe .retainFallback) 1 false
def declined := run BodyCallRun.missedCons [] .decline 3
def handedOff := run BodyCallRun.alienAppend [] (.observe .noAnswers) 3

theorem pending_final_and_nonfinished_stops_are_not_completed :
    (readout Nat.add (fun _ left _ => left) (fun _ _ => []) pendingFinal (earned _ _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) incomplete (earned _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) declined (earned _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) handedOff (earned _ _ _ _)).1 = none := by decide

theorem terminal_failure_and_singleton_empty_collection_differ :
    (readout Nat.add (fun _ left _ => left) (fun _ _ => []) failed (earned _ _ _ _)).1 = some [] ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.missed [] 0
        failed (earned _ _ _ _)).1 = some none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) emptyCollection (earned _ _ _ _)).1 = some [[]] ∧
      (directValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0
        emptyCollection (earned _ _ _ _)).1 = some [] ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0
        emptyCollection (earned _ _ _ _)).1 = some (some []) := by decide

theorem equal_occurrences_and_recursive_order_survive_mode_admission :
    (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
      SourceProducerCardinality.Controls.duplicates [] 0 duplicateAnswers (earned _ _ _ _)).1 = some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .producer .optionalValue
        SourceProducerCardinality.Controls.duplicates [] 0 duplicateAnswers (earned _ _ _ _)).1 = some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .producer .optionalValue
        BodyCallRun.called [0] 0 recursiveAnswers (earned _ _ _ _)).1 = some [[7, 1], [8, 1]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
        BodyCallRun.called [0] 0 recursiveAnswers (earned _ _ _ _)).1 = none := by decide

theorem wrong_mode_and_scalar_interface_are_refused :
    (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .direct .singleValue
      SourceProducerCardinality.Controls.duplicates [] 0 duplicateAnswers (earned _ _ _ _)).1 = none ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .optional .singleValue
        BodyCallRun.missed [] 0 failed (earned _ _ _ _)).1 = none ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
        BodyCallRun.missed [] 0 failed (earned _ _ _ _)).1 = none := by decide

def capturedWorld : OrderedDependencyStore.Store (Equation Nat) 1 :=
  OrderedDependencyStore.initial 998 (fun _ => BodyCallRun.blank)

def editedWorld := OrderedDependencyStore.appendOwn capturedWorld 0
  [⟨⟨.any, .any⟩, false, .singleton 8⟩]

theorem stale_dispatch_does_not_unearn_captured_completion :
    OrderedDependencyStore.checkRead editedWorld (OrderedDependencyStore.readStamp capturedWorld 0) = false ∧
      (liveAdmission Nat.add (fun _ left _ => left) (fun _ _ => []) capturedWorld editedWorld 0
        .direct .singleValue [] 0 emptyCollection (earned _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) emptyCollection (earned _ _ _ _)).1 = some [[]] := by decide

def forgedFinished : BodyCall.State Nat Nat :=
  ⟨[.body [] (.observe .noAnswers) ⟨.singleton 7, [], 0, []⟩ .emit], .finished⟩

theorem forged_finished_work_cannot_supply_the_readout_invariant :
    ¬ BodyCallProtocol.finishedQuiet Nat.add (fun _ left _ => left) forgedFinished := by
  intro purported
  have empty := purported rfl
  change [[7]] = [] at empty
  cases empty

#print axioms pending_final_and_nonfinished_stops_are_not_completed
#print axioms terminal_failure_and_singleton_empty_collection_differ
#print axioms equal_occurrences_and_recursive_order_survive_mode_admission
#print axioms wrong_mode_and_scalar_interface_are_refused
#print axioms stale_dispatch_does_not_unearn_captured_completion
#print axioms forged_finished_work_cannot_supply_the_readout_invariant

namespace Resumption

abbrev charges (quantum : Nat)
    (accept : Bool → BodyCallOwned.Returned Nat.add (fun _ left _ => left) (fun _ _ => []) → Bool × Bool) :
    Cursor.Charge (BodyCallOwned.provider Nat.add (fun _ left _ => left) (fun _ _ => []) quantum accept) :=
  fun _ _ => 1

def grant (quantum allowance : Nat) : Grant Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  (quantum, allowance, BodyCallOwned.Controls.warming)

def refuseAndWarm (_ : Bool)
    (_ : BodyCallOwned.Returned Nat.add (fun _ left _ => left) (fun _ _ => [])) : Bool × Bool :=
  (false, true)

def sliced (authored : List (Equation Nat)) (items : List Nat) (warm : Bool)
    (grants : List (Grant Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool))) :=
  schedule Nat.add (fun _ left _ => left) (fun _ _ => []) charges grants
    (openCall Nat.add (fun _ left _ => left) (fun _ _ => []) authored items 0 warm)

theorem sliced_captured (authored : List (Equation Nat)) (items : List Nat) (warm : Bool)
    (grants : List (Grant Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool))) :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) authored items 0
      (sliced authored items warm grants) :=
  schedule_open_captured Nat.add (fun _ left _ => left) (fun _ _ => []) charges grants authored items 0 warm

def pausedOnce := sliced BodyCallRun.blank [] false [grant 1 1]
def pausedTwice := sliced BodyCallRun.blank [] false [grant 1 1, grant 1 1]
def refusedGrants := [grant 1 1, grant 1 1, (64, 1, refuseAndWarm)]
def acceptedGrants := refusedGrants ++ [grant 0 1]
def completedGrants := acceptedGrants ++ [grant 64 1]
def refused := sliced BodyCallRun.blank [] false refusedGrants
def accepted := sliced BodyCallRun.blank [] false acceptedGrants
def completed := sliced BodyCallRun.blank [] false completedGrants

theorem multiple_pauses_keep_actual_progress_without_publishing :
    pausedOnce.2.2.computation.1 < pausedTwice.2.2.computation.1 ∧
      pausedOnce.2.2.context.1 = [] ∧ pausedTwice.2.2.context.1 = [] ∧
      pausedOnce.2.1.terminal.isNone = true ∧ pausedTwice.2.1.terminal.isNone = true ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) pausedTwice = false := by decide

theorem changed_refusal_context_is_used_without_repolling :
    refused.2.1.pending.isSome = true ∧ refused.2.2.context = ([], true) ∧
      accepted.2.1.pending.isNone = true ∧ accepted.2.2.context = ([[]], true) ∧
      accepted.2.2.computation.1 = refused.2.2.computation.1 ∧
      BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => []) accepted.2.2.computation.2 =
        BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => []) refused.2.2.computation.2 ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) accepted = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) completed = true := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, by decide, by decide⟩

theorem completed_sliced_empty_collection_is_a_value :
    (readout Nat.add (fun _ left _ => left) (fun _ _ => []) completed
      (sliced_captured _ _ _ _).2.1).1 = some [[]] ∧
      (directValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0 completed
        (sliced_captured _ _ _ _).2.1).1 = some [] ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0 completed
        (sliced_captured _ _ _ _).2.1).1 = some (some []) := by decide

def duplicateGrants := [grant 1 1, grant 64 1, grant 64 1, grant 64 1]
def duplicates := sliced SourceProducerCardinality.Controls.duplicates [] true duplicateGrants
def failureGrants := [grant 1 1, grant 64 1]
def failure := sliced BodyCallRun.missed [] true failureGrants

theorem resumed_modes_preserve_occurrences_and_completed_failure :
    (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
      SourceProducerCardinality.Controls.duplicates [] 0 duplicates (sliced_captured _ _ _ _).2.1).1 =
        some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .producer .optionalValue
        SourceProducerCardinality.Controls.duplicates [] 0 duplicates (sliced_captured _ _ _ _).2.1).1 =
          some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .direct .singleValue
        SourceProducerCardinality.Controls.duplicates [] 0 duplicates (sliced_captured _ _ _ _).2.1).1 = none ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.missed [] 0 failure
        (sliced_captured _ _ _ _).2.1).1 = some none := by decide

def finalRetried := resume Nat.add (fun _ left _ => left) (fun _ _ => []) 0 1
  BodyCallOwned.Controls.warming (charges _ _) pendingFinal

theorem pending_final_retry_acknowledges_the_original_computation :
    complete Nat.add (fun _ left _ => left) (fun _ _ => []) pendingFinal = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) finalRetried = true ∧
      finalRetried.2.2.computation.1 = pendingFinal.2.2.computation.1 ∧
      finalRetried.2.2.context.1 = [[]] ∧
      finalRetried.2.1.accepted = pendingFinal.2.1.accepted + 1 := by decide

theorem completed_reentry_keeps_the_whole_call (quantum allowance : Nat) :
    resume Nat.add (fun _ left _ => left) (fun _ _ => []) quantum allowance refuseAndWarm
      (charges _ _) completed = completed :=
  completed_resume_inert _ _ _ _ _ _ _ _ (by decide)

theorem zero_acceptance_allowance_keeps_even_a_pending_loan (quantum : Nat) :
    resume Nat.add (fun _ left _ => left) (fun _ _ => []) quantum 0 refuseAndWarm
      (charges _ _) refused = refused := resume_zero _ _ _ _ _ _ _

theorem stale_new_eligibility_does_not_undo_resumed_completion :
    (liveAdmission Nat.add (fun _ left _ => left) (fun _ _ => []) capturedWorld editedWorld 0
      .direct .singleValue [] 0 completed (sliced_captured _ _ _ _).2.1).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) completed
        (sliced_captured _ _ _ _).2.1).1 = some [[]] := by decide

theorem yield_decline_and_handoff_are_not_resumed_completion :
    complete Nat.add (fun _ left _ => left) (fun _ _ => [])
      (resume Nat.add (fun _ left _ => left) (fun _ _ => []) 0 1 BodyCallOwned.Controls.warming
        (charges _ _) declined) = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => [])
        (resume Nat.add (fun _ left _ => left) (fun _ _ => []) 0 1 BodyCallOwned.Controls.warming
          (charges _ _) handedOff) = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) accepted = false := by decide

#print axioms sliced_captured
#print axioms multiple_pauses_keep_actual_progress_without_publishing
#print axioms changed_refusal_context_is_used_without_repolling
#print axioms completed_sliced_empty_collection_is_a_value
#print axioms resumed_modes_preserve_occurrences_and_completed_failure
#print axioms pending_final_retry_acknowledges_the_original_computation
#print axioms completed_reentry_keeps_the_whole_call
#print axioms zero_acceptance_allowance_keeps_even_a_pending_loan
#print axioms stale_new_eligibility_does_not_undo_resumed_completion
#print axioms yield_decline_and_handoff_are_not_resumed_completion

end Resumption

end Controls

end BodyCallAdmission

namespace BodyCallShared

/-- The common cold transfer preserves a Call, seeds its already issued loan
and starts only new reader positions. It performs no provider operation. -/
def retainedAdopt {Loan Saved Stored Context Owner : Type} {clients : Nat}
    (context : Context) (limit : Nat)
    (call : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved)) :
    Cursor.ProducerOccurrenceLog.Configuration
      (Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
      (Nat × Loan) Stored Context Owner Empty Loan clients :=
  ⟨some ⟨call, call.2.1.pending.map (fun loan => (call.2.1.accepted, loan)), 0, .active⟩,
    context, ⟨Cursor.SharedOccurrenceLog.initial limit, ∅⟩⟩

/-- Handback uses the same pending/captured distinction for every retained
loan representation. The supplied action is the existing acknowledgment. -/
def retainedRelease {Loan Saved Stored Context Owner : Type} {clients : Nat}
    (acknowledge : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved) →
      Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
    (state : Cursor.ProducerOccurrenceLog.Configuration
      (Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
      (Nat × Loan) Stored Context Owner Empty Loan clients) :=
  (state.execution.map (fun execution =>
    if execution.pending.isNone && execution.producer.2.1.pending.isSome then
      acknowledge execution.producer else execution.producer),
    (Cursor.ProducerOccurrenceLog.detach state).2)


/-- Common retained-call choice. The existing occurrence-log engine owns
capture/admission/delivery; this only selects terminal, acknowledgment or poll. -/
def retainedStep {Loan Saved : Type}
    (inspect : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved) →
      Cursor.ProducerOccurrenceLog.ProducerOutcome
        (Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved)) (Nat × Loan) Empty Loan)
    (acknowledge poll : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved) →
      Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved))
    (call : Nat × (Cursor.Fold.OwnedSequence.CallbackBoundary.Result Loan Loan × Saved)) :=
  if call.2.1.terminal.isSome then inspect call
  else match call.2.1.pending with
    | some _ => .progress (acknowledge call)
    | none => inspect (poll call)

open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Call := BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context)
abbrev Loan := BodyCallOwned.Returned construct callbackConstruct fallback
abbrev Borrowed := Nat × Loan construct callbackConstruct fallback
abbrev Stored := Nat × List (List Output)
abbrev Move := Cursor.ProducerOccurrenceLog.ProducerOutcome
  (Call construct callbackConstruct fallback (Context := Context))
  (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback)

def refuse (context : Context) (_ : Loan construct callbackConstruct fallback) : Bool × Context :=
  (false, context)

def accept (context : Context) (_ : Loan construct callbackConstruct fallback) : Bool × Context :=
  (true, context)

abbrev charge (quantum : Nat)
    (consumer : Context → Loan construct callbackConstruct fallback → Bool × Context) :
    Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer) :=
  fun _ _ => 1

/-- Read the actual owned callback boundary. A held reply is indexed by its
existing successful-return position; it is not producer exhaustion. -/
def inspect (call : Call construct callbackConstruct fallback (Context := Context)) :
    Move construct callbackConstruct fallback (Context := Context) :=
  if BodyCallAdmission.complete construct callbackConstruct fallback call then .completed call
  else match call.2.1.terminal with
    | some returned => match returned.2.1 with
      | .decline _ => .interrupted call
      | .handoff _ => .handoff returned call
      | _ => .yielded call
    | none => match call.2.1.pending with
      | some returned => .returned (call.2.1.accepted, returned) call
      | none => .yielded call

theorem inspect_next (call : Call construct callbackConstruct fallback (Context := Context)) :
    (inspect construct callbackConstruct fallback call).next = call := by
  unfold inspect
  split
  · rfl
  · cases call.2.1.terminal with
    | some returned => cases mode : returned.2.1 <;> simp [mode, Cursor.ProducerOccurrenceLog.ProducerOutcome.next]
    | none => cases call.2.1.pending <;> rfl

/-- A public loan is the actual retained source reply, before acknowledgment. -/
def Coherent (call : Call construct callbackConstruct fallback (Context := Context)) : Prop :=
  ∀ loan, call.2.1.pending = some loan →
    call.2.1.terminal = none ∧ call.2.2.computation.2 = .done loan ∧
      BodyCallOwned.isReturn construct callbackConstruct fallback loan = true

open Cursor.Fold.OwnedSequence.CallbackBoundary

private theorem retainedCallbacks_coherent
    {Input Output Context : Type}
    (source : Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)))
    (sourceCharge : Cursor.Charge source) (quantum : Nat)
    (isReturn : Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) → Bool)
    (rearm : Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) →
      Cursor.Packet source BodyCallProtocol.client (⟨()⟩ : ULift Unit))
    (consume : Context → Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) → Bool × Context)
    (terminalAfter : Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit) →
      Option (Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)))
    (charges : Cursor.Charge (Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.provider source BodyCallProtocol.client
      ⟨()⟩ sourceCharge quantum isReturn rearm consume))
    (allowance accepted : Nat)
    (held : Option (Cursor.Finished source (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)))
    (state : Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.State source BodyCallProtocol.client ⟨()⟩ Context)
    (aligned : ∀ loan, held = some loan → state.computation.2 = .done loan ∧ isReturn loan = true) :
    let actual := Cursor.Fold.OwnedSequence.CallbackBoundary.fromCallbacks
      (Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.provider source BodyCallProtocol.client
        ⟨()⟩ sourceCharge quantum isReturn rearm consume)
      charges allowance held accepted state terminalAfter
    ∀ loan, actual.2.1.pending = some loan → actual.2.1.terminal = none ∧
      actual.2.2.computation.2 = .done loan ∧ isReturn loan = true := by
  dsimp only
  induction allowance generalizing accepted held state with
  | zero =>
      intro loan pending
      exact ⟨rfl, aligned loan pending⟩
  | succ allowance ih =>
      cases held with
      | some loan =>
          obtain ⟨ready, produced⟩ := aligned loan rfl
          cases decision : (consume state.context loan).1 with
          | false =>
              simp [fromCallbacks, Retained.provider, ready, produced,
                decision]
          | true =>
              cases final : terminalAfter loan with
              | some reason =>
                  simp [fromCallbacks, Retained.provider, ready, produced,
                    decision, final]
              | none =>
                  simpa [fromCallbacks, Retained.provider, ready, produced,
                    decision, final] using
                    ih (accepted + 1) none _ (by intro next impossible; cases impossible)
      | none =>
          cases outcome : (Cursor.resume (source)
              BodyCallProtocol.client (sourceCharge)
              quantum state.computation).2 with
          | paused saved =>
              simp [fromCallbacks, Retained.provider, outcome]
          | done returned =>
              cases produced : isReturn returned with
              | false =>
                  simp [fromCallbacks, Retained.provider, outcome, produced]
              | true =>
                  cases decision : (consume state.context returned).1 with
                  | false =>
                      simp [fromCallbacks, Retained.provider, outcome, produced,
                        decision]
                  | true =>
                      cases final : terminalAfter returned with
                      | some reason =>
                          simp [fromCallbacks, Retained.provider, outcome, produced,
                            decision, final]
                      | none =>
                          simpa [fromCallbacks, Retained.provider, outcome, produced,
                            decision, final] using
                            ih (accepted + 1) none _ (by intro next impossible; cases impossible)

/-- Ordered rows already exposed at the source-to-log boundary. A held loan
is counted once, even before its later zero-source acknowledgment. -/
def publishedRows (call : Call construct callbackConstruct fallback (Context := Context)) : List (List Output) :=
  call.2.2.context.1 ++ call.2.1.pending.toList.flatMap (fun loan => loan.2.1.rows)

def residualRows (call : Call construct callbackConstruct fallback (Context := Context)) : List (List Output) :=
  match call.2.1.pending with
  | some _ => BodyCall.workRows construct callbackConstruct (BodyCallProtocol.stateView
      construct callbackConstruct fallback call.2.2.computation.2).work
  | none => BodyCallProtocol.unacceptedRows construct callbackConstruct fallback call.2.2.computation.2

theorem open_coherent (authored : List (Equation Output)) (items : List Input)
    (parameter : Nat) (context : Context) :
    Coherent construct callbackConstruct fallback
      (BodyCallAdmission.openCall construct callbackConstruct fallback authored items parameter context) := by
  intro loan pending
  cases pending

theorem published_residual_eq_view (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    publishedRows construct callbackConstruct fallback call ++ residualRows construct callbackConstruct fallback call =
      BodyCallOwned.view construct callbackConstruct fallback call.2.2 := by
  cases pending : call.2.1.pending with
  | none => simp [publishedRows, residualRows, pending, BodyCallOwned.view]
  | some loan =>
      have held := coherent loan pending
      simp [publishedRows, residualRows, pending, BodyCallOwned.view, held.2.1,
        BodyCallProtocol.unacceptedRows, BodyCallProtocol.moveView, List.append_assoc]

theorem poll_shape (quantum : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none) :
    let later := BodyCallAdmission.resume construct callbackConstruct fallback quantum 1
      (refuse construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _) call
    later.2.2.context = call.2.2.context ∧ later.2.1.accepted = call.2.1.accepted ∧
      Coherent construct callbackConstruct fallback later := by
  cases outcome : (Cursor.resume (BodyCallProtocol.provider construct callbackConstruct fallback)
      BodyCallProtocol.client (BodyCallProtocol.requestCharge construct callbackConstruct fallback)
      quantum call.2.2.computation).2 with
  | paused packet =>
      simp [BodyCallAdmission.resume, resumeCall, running, empty, fromCallbacks,
        BodyCallOwned.provider, Retained.provider, outcome, Coherent]
  | done returned =>
      cases produced : BodyCallOwned.isReturn construct callbackConstruct fallback returned <;>
        simp [BodyCallAdmission.resume, resumeCall, running, empty, fromCallbacks,
          BodyCallOwned.provider, Retained.provider, outcome, produced, BodyCallOwned.consume,
          refuse, Coherent]

theorem acknowledge_shape (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call)
    (loan : Loan construct callbackConstruct fallback) (pending : call.2.1.pending = some loan) :
    let later := BodyCallAdmission.resume construct callbackConstruct fallback 0 1
      (accept construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _) call
    later.2.1.pending = none ∧ later.2.2.context.1 = call.2.2.context.1 ++ loan.2.1.rows ∧
      later.2.1.accepted = call.2.1.accepted + 1 ∧ Coherent construct callbackConstruct fallback later := by
  have held := coherent loan pending
  cases final : BodyCallOwned.terminalAfter construct callbackConstruct fallback loan <;>
    simp [BodyCallAdmission.resume, resumeCall, held.1, pending, fromCallbacks,
      BodyCallOwned.provider, Retained.provider, held.2.1, held.2.2, BodyCallOwned.consume,
      accept, final, Coherent]

theorem inspect_returns (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    (inspect construct callbackConstruct fallback call).returns =
      call.2.1.pending.toList.map (fun loan => (call.2.1.accepted, loan)) := by
  cases pending : call.2.1.pending with
  | some loan =>
      have held := coherent loan pending
      simp [inspect, BodyCallAdmission.complete, pending, held.1,
        Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
  | none =>
      unfold inspect
      split
      · rfl
      · cases terminal : call.2.1.terminal with
        | none => simp [pending, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
        | some returned =>
            cases mode : returned.2.1 <;>
              simp [mode, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size)
    (reader : Fin size) (point : IndexedAuthority.Point authority)
    (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

/-- One real owned-source action. A captured loan is acknowledged without
another source inspection. Only new production enters the current authority
gate. The enclosing shared-log pump blocks this action while capture waits. -/
def step (quantum : Nat) (call : Call construct callbackConstruct fallback (Context := Context)) :
    Move construct callbackConstruct fallback (Context := Context) :=
  retainedStep (inspect construct callbackConstruct fallback)
    (fun saved => BodyCallAdmission.resume construct callbackConstruct fallback 0 1
      (accept construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _) saved)
    (fun saved => (BodyCallAdmission.CurrentAuthority.resume construct callbackConstruct fallback authority before current reader
      point required quantum 1 (refuse construct callbackConstruct fallback)
      (charge construct callbackConstruct fallback _ _) saved).2) call

def capture (borrowed : Borrowed construct callbackConstruct fallback) : Option (Stored (Output := Output)) :=
  some (borrowed.1, borrowed.2.2.1.rows)

abbrev Configuration (Owner : Type) (clients : Nat) := Cursor.ProducerOccurrenceLog.Configuration
  (Call construct callbackConstruct fallback (Context := Context))
  (Borrowed construct callbackConstruct fallback) (Stored (Output := Output))
  (OrderedDependencyStore.Store (Equation Output) size) Owner Empty
  (Loan construct callbackConstruct fallback) clients

/-- Buffered pure data belongs to its retained capture. New source work has
the separate current-world/authority gate in `step`. -/
def initial (authoredItems : List Input) (parameter : Nat) (context : Context)
    (Owner : Type) (clients limit : Nat) :
    Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients :=
  Cursor.ProducerOccurrenceLog.initial
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) authoredItems parameter context) before limit

theorem step_preserves_captured (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter call) :
    BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter
      (step construct callbackConstruct fallback authority before current reader point required quantum call).next := by
  unfold step retainedStep
  split
  · simpa only [inspect_next] using safe
  · cases call.2.1.pending with
    | some loan =>
        exact BodyCallAdmission.resume_captured construct callbackConstruct fallback 0 1
          (accept construct callbackConstruct fallback) (charge construct callbackConstruct fallback _ _)
          _ items parameter call safe
    | none =>
        rw [inspect_next]
        exact BodyCallAdmission.CurrentAuthority.preserves_captured construct callbackConstruct fallback authority
          before current reader point required quantum 1 (refuse construct callbackConstruct fallback)
          (charge construct callbackConstruct fallback _ _) items parameter call safe

theorem step_preserves_coherent (quantum : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    Coherent construct callbackConstruct fallback
      (step construct callbackConstruct fallback authority before current reader point required quantum call).next := by
  unfold step retainedStep
  split
  · simpa only [inspect_next] using coherent
  · cases pending : call.2.1.pending with
    | some loan => exact (acknowledge_shape construct callbackConstruct fallback call coherent loan pending).2.2.2
    | none =>
        rw [inspect_next]
        unfold BodyCallAdmission.CurrentAuthority.resume
        split
        · split
          · exact (poll_shape construct callbackConstruct fallback quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending).2.2
          · exact coherent
        · exact coherent

/-- The source boundary exposes each actual reply once. A later successful
capture is acknowledged without republishing the reply or requesting source. -/
theorem step_rows (quantum : Nat)
    (call : Call construct callbackConstruct fallback (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback call) :
    publishedRows construct callbackConstruct fallback
        (step construct callbackConstruct fallback authority before current reader point required quantum call).next =
      publishedRows construct callbackConstruct fallback call ++
        (step construct callbackConstruct fallback authority before current reader point required quantum call).returns.flatMap
          (fun borrowed => borrowed.2.2.1.rows) := by
  unfold step retainedStep
  split
  · rw [inspect_next, inspect_returns construct callbackConstruct fallback call coherent]
    have empty : call.2.1.pending = none := by
      cases pending : call.2.1.pending with
      | none => rfl
      | some loan =>
          have held := coherent loan pending
          simp [held.1] at ‹call.2.1.terminal.isSome = true›
    simp [empty]
  · cases pending : call.2.1.pending with
    | some loan =>
        have shape := acknowledge_shape construct callbackConstruct fallback call coherent loan pending
        simp [Cursor.ProducerOccurrenceLog.ProducerOutcome.next,
          Cursor.ProducerOccurrenceLog.ProducerOutcome.returns, publishedRows, shape.1, shape.2.1, pending]
    | none =>
        by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
        · by_cases permitted : FrameUpdate point.authority required
          · simp only [BodyCallAdmission.CurrentAuthority.resume, fresh, permitted, ↓reduceIte]
            have shape := poll_shape construct callbackConstruct fallback quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending
            rw [inspect_next, inspect_returns construct callbackConstruct fallback _ shape.2.2]
            simp [publishedRows, shape.1, shape.2.1, pending, List.flatMap_map]
          · simp only [BodyCallAdmission.CurrentAuthority.resume, fresh, permitted, ↓reduceIte]
            rw [inspect_next, inspect_returns construct callbackConstruct fallback call coherent]
            simp [pending]
        · simp only [BodyCallAdmission.CurrentAuthority.resume, fresh, Bool.false_eq_true, ↓reduceIte]
          rw [inspect_next, inspect_returns construct callbackConstruct fallback call coherent]
          simp [pending]

/-- A path of the actual saved source computation has its exact ordered row
prefix, not an assumed equality between accepted rows and future answers. -/
theorem path_rows (quantum : Nat)
    {first last : Call construct callbackConstruct fallback (Context := Context)}
    {returns : List (Borrowed construct callbackConstruct fallback)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath
      (step construct callbackConstruct fallback authority before current reader point required quantum) first returns last)
    (coherent : Coherent construct callbackConstruct fallback first) :
    Coherent construct callbackConstruct fallback last ∧
      publishedRows construct callbackConstruct fallback last =
        publishedRows construct callbackConstruct fallback first ++ returns.flatMap (fun loan => loan.2.2.1.rows) := by
  induction path with
  | refl => exact ⟨coherent, by simp⟩
  | @next first move later returns transition tail ih =>
      have kept := step_preserves_coherent construct callbackConstruct fallback authority before current reader
        point required quantum first coherent
      have row := step_rows construct callbackConstruct fallback authority before current reader point required
        quantum first coherent
      rw [transition] at kept row
      have rest := ih kept
      refine ⟨rest.1, ?_⟩
      rw [rest.2, row, List.flatMap_append, List.append_assoc]

theorem path_preserves_captured (quantum : Nat) (items : List Input) (parameter : Nat)
    {first last : Call construct callbackConstruct fallback (Context := Context)}
    {returns : List (Borrowed construct callbackConstruct fallback)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath
      (step construct callbackConstruct fallback authority before current reader point required quantum) first returns last)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter first) :
    BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter last := by
  induction path with
  | refl => exact safe
  | next transition tail ih =>
      apply ih
      have kept := step_preserves_captured construct callbackConstruct fallback authority before current reader
        point required quantum items parameter _ safe
      simpa only [transition] using kept

theorem run_keeps_actual_source {Owner : Type} {clients : Nat}
    (quantum ticks : Nat) (capacity : Stored (Output := Output) → Bool)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (execution : Cursor.ProducerOccurrenceLog.Execution
      (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer) :
    ∃ next, (Cursor.ProducerOccurrenceLog.run
        (step construct callbackConstruct fallback authority before current reader point required quantum)
        (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks state).2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer := by
  obtain ⟨next, retained, actual⟩ := Cursor.ProducerOccurrenceLog.run_producer_path
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks state execution attached
  exact ⟨next, retained, path_preserves_captured construct callbackConstruct fallback authority before current reader
    point required quantum items parameter actual safe⟩

/-- Every finite shared-source run exposes an ordered authored-source prefix
and keeps the actual unevaluated residual and the complete captured Call. -/
theorem run_open_source {Owner : Type} {clients : Nat}
    (quantum ticks limit : Nat) (capacity : Stored (Output := Output) → Bool)
    (items : List Input) (parameter : Nat) (context : Context) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let actual := Cursor.ProducerOccurrenceLog.run
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
    ∃ next, actual.2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      (actual.1.flatMap Cursor.ProducerOccurrenceLog.returned).flatMap (fun loan => loan.2.2.1.rows) ++
        residualRows construct callbackConstruct fallback next.producer =
          source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
  obtain ⟨next, retained, path⟩ := Cursor.ProducerOccurrenceLog.run_producer_path
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start _ rfl
  have coherent := open_coherent construct callbackConstruct fallback
    (OrderedDependencyStore.query before reader) items parameter context
  have rows := path_rows construct callbackConstruct fallback authority before current reader point required
    quantum path coherent
  have safe := path_preserves_captured construct callbackConstruct fallback authority before current reader
    point required quantum items parameter path
    (BodyCallAdmission.open_captured construct callbackConstruct fallback _ items parameter context)
  refine ⟨next, retained, safe, ?_⟩
  have view := published_residual_eq_view construct callbackConstruct fallback next.producer rows.1
  rw [rows.2] at view
  simpa [start, initial, Cursor.ProducerOccurrenceLog.initial, publishedRows, BodyCallAdmission.openCall,
    BodyCallOwned.openState, safe.2.2] using view.trans safe.2.2

/-- Actual captured log contents, the borrowed return awaiting admission,
and the actual source residual partition the independent authored answers.
The equation uses the existing append/conservation laws for this concrete
capture; it does not assume an accepted-equals-source oracle. -/
theorem run_open_log_source {Owner : Type} {clients : Nat}
    (quantum ticks limit : Nat) (capacity : Stored (Output := Output) → Bool)
    (items : List Input) (parameter : Nat) (context : Context) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let actual := Cursor.ProducerOccurrenceLog.run
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
    ∃ next, actual.2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      actual.2.delivery.log.rows.flatMap (·.2) ++
        (Cursor.ProducerOccurrenceLog.pending actual.2).toList.flatMap (fun loan => loan.2.2.1.rows) ++
        residualRows construct callbackConstruct fallback next.producer =
          source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
  let actual := Cursor.ProducerOccurrenceLog.run
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
  obtain ⟨next, retained, safe, sourceEq⟩ := run_open_source construct callbackConstruct fallback authority
    before current reader point required quantum ticks limit capacity items parameter context (Owner := Owner) (clients := clients)
  have conservation := Cursor.ProducerOccurrenceLog.run_conservation
    (fun (loan : Borrowed construct callbackConstruct fallback) => loan.2.2.1.rows)
    (fun (stored : Stored (Output := Output)) => stored.2)
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true)
    (by intro loan stored captured; cases captured; rfl) ticks start
  have flat := congrArg (List.flatMap id) conservation
  simp only [List.flatMap_append, List.flatMap_map] at flat
  have stored := Cursor.ProducerOccurrenceLog.run_rows
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) ticks start
  have empty : start.delivery.log.rows = [] := rfl
  have noLoan : Cursor.ProducerOccurrenceLog.pending start = none := rfl
  rw [empty, List.nil_append] at stored
  simp only [noLoan, Option.toList_none, List.flatMap_nil, List.nil_append] at flat
  rw [← stored] at flat
  refine ⟨next, retained, safe, ?_⟩
  exact (congrArg (· ++ residualRows construct callbackConstruct fallback next.producer) flat.symm).trans sourceEq

/-- Arbitrary interleaved producer requests and consumer acknowledgments
retain the real Call, its independent captured-source view, and loan coherence. -/
theorem actions_keep_actual_source {Owner : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (execution : Cursor.ProducerOccurrenceLog.Execution
      (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : Coherent construct callbackConstruct fallback execution.producer) :
    ∃ next, (Cursor.ProducerOccurrenceLog.Accounting.runActions
        (step construct callbackConstruct fallback authority before current reader point required quantum)
        (capture construct callbackConstruct fallback) capacity (fun _ => true) actions state).execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      Coherent construct callbackConstruct fallback next.producer := by
  induction actions generalizing state execution with
  | nil => exact ⟨execution, attached, safe, coherent⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨next, retained, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path
            (step construct callbackConstruct fallback authority before current reader point required quantum)
            (capture construct callbackConstruct fallback) capacity (fun _ => true) state execution attached
          exact ih _ next retained
            (path_preserves_captured construct callbackConstruct fallback authority before current reader point required
              quantum items parameter path safe)
            (path_rows construct callbackConstruct fallback authority before current reader point required
              quantum path coherent).1
      | deliver client owner =>
          apply ih _ execution _ safe coherent
          simpa [Cursor.ProducerOccurrenceLog.deliver] using attached

/-- Cancelling one consumer commutes with any interleaved schedule that does
not deliver to that cancelled consumer. The whole actual source Call and its
captured world, the paid production/delivery account, and the other consumer's
ordered unread values agree. -/
theorem independent_retirement {Owner : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (account : Cursor.ProducerOccurrenceLog.Accounting.ProtocolAccount)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (retired other : Fin clients) (position : Nat) (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : Cursor.ProducerOccurrenceLog.Accounting.sparesRetired retired actions) :
    let original := Cursor.ProducerOccurrenceLog.Accounting.count
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) actions account state
    let cancelled := Cursor.ProducerOccurrenceLog.Accounting.count
      (step construct callbackConstruct fallback authority before current reader point required quantum)
      (capture construct callbackConstruct fallback) capacity (fun _ => true) actions account
      (Cursor.ProducerOccurrenceLog.retireConsumer state retired)
    cancelled.1.execution = original.1.execution ∧ cancelled.1.context = original.1.context ∧
      cancelled.2 = original.2 ∧
      Cursor.SharedOccurrenceLog.peek cancelled.1.delivery.log other =
        Cursor.SharedOccurrenceLog.peek original.1.delivery.log other ∧
      Cursor.SharedOccurrenceLog.unread cancelled.1.delivery.log other =
        Cursor.SharedOccurrenceLog.unread original.1.delivery.log other := by
  dsimp only
  rw [Cursor.ProducerOccurrenceLog.Accounting.count_after_retained_demand
    (step construct callbackConstruct fallback authority before current reader point required quantum)
    (capture construct callbackConstruct fallback) capacity (fun _ => true) actions account state
    retired other position distinct live spares]
  exact ⟨rfl, rfl, rfl,
    (Cursor.ProducerOccurrenceLog.retireConsumer_releases_only_its_retention _ retired).2.2 other distinct⟩

/-- The heap law applies to the other consumer's actual unread payload graph.
Native discovery of that graph and agreement with compiled layout are supplied
services; this statement does not replace them with source syntax. -/
theorem retirement_keeps_payload_graph {Owner Cell : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner]
    (heap : ResourceOwnership.Heap (Stored (Output := Output)) Cell)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (retired other : Fin clients) (valid : Cursor.SharedOccurrenceLog.Valid state.delivery.log)
    (distinct : other ≠ retired) (location : Stored (Output := Output))
    (live : ResourceOwnership.Live heap
      (Cursor.OwnedLifecycle.answerRoots (Sum.inl other : Sum (Fin clients) Owner)
        (Cursor.SharedOccurrenceLog.unread state.delivery.log other)) location) :
    (ResourceOwnership.collect heap
      (Cursor.SharedOccurrenceOwnership.roots
        (Cursor.SharedOccurrenceOwnership.trimLog
          (Cursor.SharedOccurrenceOwnership.cancelConsumer state.delivery retired)))).lookup location =
      heap.lookup location :=
  Cursor.ProducerOccurrenceLog.retireConsumer_retains_other_ready_graph heap state retired other valid distinct location live

namespace Coefficients

open Mettapedia.Algebra.SharedCoefficientLedger

/-- An admission-position observer with a supplied per-return coefficient.
It is distinct from source firing factors in `BodyCallShared.Weighted`.
No execution, delivery journal or alternate account is stored. -/
def ledger {Owner V : Type} {clients : Nat} (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients) :
    Ledger Nat (OrderedDependencyStore.ReadStamp size) V :=
  (state.delivery.log.rows.zipIdx state.delivery.log.base).map fun occurrence =>
    ⟨occurrence.2, OrderedDependencyStore.readStamp state.context reader, coefficient occurrence.1⟩

theorem ledger_valid {Owner V : Type} {clients : Nat} (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients) :
    Valid (ledger construct callbackConstruct fallback reader coefficient state) := by
  simp only [ledger, Valid, identities, List.map_map, Function.comp_def]
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

theorem retirement_keeps_factors {Owner V : Type} {clients : Nat}
    (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (retired : Fin clients) :
    ledger construct callbackConstruct fallback reader coefficient (Cursor.ProducerOccurrenceLog.retireConsumer state retired) =
      ledger construct callbackConstruct fallback reader coefficient state := rfl

theorem delivery_keeps_factors {Owner V : Type} {clients : Nat}
    [DecidableEq Output] [DecidableEq Owner] (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (client : Fin clients) (owner : Owner) :
    ledger construct callbackConstruct fallback reader coefficient
      (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 =
      ledger construct callbackConstruct fallback reader coefficient state := by
  cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
    simp [ledger, Cursor.ProducerOccurrenceLog.deliver, Cursor.SharedOccurrenceOwnership.advance,
      Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceOwnership.acknowledge,
      Cursor.SharedOccurrenceLog.pull, reply, Cursor.SharedOccurrenceLog.setPosition]

/-- Two consumer views merge the one paid production ledger once. Successful
delivery is a separate use and never appends another copy of its factors. -/
theorem shared_factors_once {Owner V : Type} {clients : Nat} [DecidableEq V]
    (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients) :
    merge? (ledger construct callbackConstruct fallback reader coefficient state)
      (ledger construct callbackConstruct fallback reader coefficient state) =
        some (ledger construct callbackConstruct fallback reader coefficient state) :=
  merge_self _ (ledger_valid construct callbackConstruct fallback reader coefficient state)

/-- A repeated delivery does not create another physical production identity,
even if the coefficient and payload of another return happen to be equal. -/
theorem existing_factor_cannot_be_reappended {Owner V : Type} {clients : Nat}
    (coefficient : Stored (Output := Output) → V)
    (state : Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients)
    (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V)
    (present : factor ∈ ledger construct callbackConstruct fallback reader coefficient state) :
    append? (ledger construct callbackConstruct fallback reader coefficient state) factor = none := by
  have member : factor.identity ∈ identities (ledger construct callbackConstruct fallback reader coefficient state) :=
    List.mem_map.mpr ⟨factor, present, rfl⟩
  simp [append?, member]

end Coefficients

namespace Controls

open Mettapedia.GSLT.Contracts
open Cursor.ProducerOccurrenceLog

abbrev sourceAuthority := revocationWorlds
abbrev held := BodyCallAdmission.CurrentAuthority.Controls.held
abbrev revoked := BodyCallAdmission.CurrentAuthority.Controls.revoked
abbrev readOnly := BodyCallAdmission.CurrentAuthority.Controls.readOnly

def world : OrderedDependencyStore.Store (Equation Nat) 3 :=
  OrderedDependencyStore.link
    (OrderedDependencyStore.initial 813 (fun member =>
      if member = 1 then SourceProducerCardinality.Controls.duplicates else [])) 0 1

def changed := OrderedDependencyStore.appendOwn world 1
  [⟨⟨.any, .any⟩, false, .singleton 8⟩]

def unrelated := OrderedDependencyStore.appendOwn world 2
  [⟨⟨.any, .any⟩, false, .singleton 8⟩]

abbrev State := Configuration Nat.add (fun _ left _ => left) (fun _ _ => [])
  (Context := Unit) (size := 3) Nat 2

def initialState : State := initial Nat.add (fun _ left _ => left) (fun _ _ => [])
  world 0 [] 0 () Nat 2 8

def initialCall := BodyCallAdmission.openCall Nat.add (fun _ left _ => left) (fun _ _ => [])
  (OrderedDependencyStore.query world 0) ([] : List Nat) 0 ()

def actualStep (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point sourceAuthority) (quantum : Nat) :=
  step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) sourceAuthority world current 0 point .consume quantum
    (Context := Unit)

def ordinary (ticks : Nat) (state : State) :=
  Cursor.ProducerOccurrenceLog.ordinary (actualStep world held 64)
    (capture Nat.add (fun _ left _ => left) (fun _ _ => [])) (fun _ => true) (fun _ => true) ticks state

def ready := ordinary 16 initialState
def pending := ordinary 1 initialState
def capturedLoan := ordinary 2 initialState
def acknowledgedLoan := ordinary 3 initialState

def first := deliver (fun _ => true) ready 0 100
def retired := retireConsumer first.2 0
def surviving := deliver (fun _ => true) retired 1 101

theorem duplicate_source_is_one_ordered_production_for_both_consumers :
    ready.delivery.log.rows = [(0, [[7]]), (1, [[7]])] ∧ ready.delivery.log.completed = true ∧
      first.1 = .observed (.answer 0 (0, [[7]])) ∧
      surviving.1 = .observed (.answer 0 (0, [[7]])) ∧
      (deliver (fun _ => true) surviving.2 1 101).1 = .observed (.answer 1 (1, [[7]])) ∧
      surviving.2.execution = ready.execution ∧ surviving.2.context = world := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, rfl⟩

theorem cancellation_does_not_restore_or_read_the_retired_consumer :
    (deliver (fun _ => true) retired 0 100).1 = .observed .cancelled ∧
      Cursor.SharedOccurrenceLog.unread retired.delivery.log 0 = [] ∧
      Cursor.SharedOccurrenceLog.unread retired.delivery.log 1 = [(0, [[7]]), (1, [[7]])] ∧
      retired.delivery.published = first.2.delivery.published := by decide

theorem held_source_loan_is_captured_then_acknowledged_without_new_source :
    (pending.execution.bind (·.pending)).isSome = true ∧
      (capturedLoan.execution.bind (fun execution => execution.producer.2.1.pending)).isSome = true ∧
      (acknowledgedLoan.execution.bind (fun execution => execution.producer.2.1.pending)).isNone = true ∧
      capturedLoan.execution.map (fun execution => execution.producer.2.2.computation.1) =
        acknowledgedLoan.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      capturedLoan.execution.map (fun execution => BodyCallProtocol.stateView Nat.add (fun _ left _ => left)
        (fun _ _ => []) execution.producer.2.2.computation.2) =
        acknowledgedLoan.execution.map (fun execution => BodyCallProtocol.stateView Nat.add (fun _ left _ => left)
          (fun _ _ => []) execution.producer.2.2.computation.2) := by
  exact ⟨by decide, by decide, by decide, by decide, rfl⟩

theorem admission_refusal_retains_the_entire_paid_pending_call :
    pump (actualStep world held 64) (capture Nat.add (fun _ left _ => left) (fun _ _ => []))
      (fun _ => false) (fun _ => true) pending = (.admissionRefused, pending) ∧
      ordinary 0 pending = pending := ⟨rfl, rfl⟩

def resumeAfterRevocation := Cursor.ProducerOccurrenceLog.ordinary (actualStep world revoked 64)
  (capture Nat.add (fun _ left _ => left) (fun _ _ => [])) (fun _ => true) (fun _ => true) 3 pending

theorem revoked_authority_does_not_unearn_the_buffered_pure_value :
    resumeAfterRevocation.delivery.log.rows = [(0, [[7]])] ∧
      resumeAfterRevocation.delivery.log.completed = false ∧
      (deliver (fun _ => true) resumeAfterRevocation 1 101).1 = .observed (.answer 0 (0, [[7]])) ∧
      (actualStep world revoked 64 initialCall).next =
        initialCall := by
  exact ⟨by decide, by decide, by decide, rfl⟩

theorem stale_or_read_only_new_work_is_inert_but_unrelated_change_is_admitted :
    (actualStep changed held 64 initialCall).next = initialCall ∧
      (actualStep world readOnly 64 initialCall).next = initialCall ∧
      (actualStep unrelated held 64 initialCall).returns.length = 1 := by
  exact ⟨rfl, rfl, by decide⟩

def programRun (authored : List (Equation Nat)) :
    Configuration Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit) (size := 1) Nat 2 :=
  let captured := OrderedDependencyStore.initial 849 (fun (_ : Fin 1) => authored)
  Cursor.ProducerOccurrenceLog.ordinary
    (step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
      held.world held.authority Access.consume)
      Nat.add (fun _ left _ => left) (fun _ _ => []) sourceAuthority captured captured 0 held .consume 64)
    (capture Nat.add (fun _ left _ => left) (fun _ _ => [])) (fun _ => true) (fun _ => true) 16
    (initial Nat.add (fun _ left _ => left) (fun _ _ => []) captured 0 [] 0 () Nat 2 8)

theorem absence_yield_handoff_and_exhaustion_remain_distinct :
    pending.delivery.log.completed = false ∧ pending.delivery.log.rows = [] ∧
      (programRun BodyCallRun.missed).delivery.log.completed = true ∧
      (programRun BodyCallRun.missed).delivery.log.rows = [] ∧
      (programRun BodyCallRun.blank).delivery.log.rows = [(0, [[]])] ∧
      (programRun BodyCallRun.alienAppend).delivery.log.completed = false ∧
      ((programRun BodyCallRun.alienAppend).execution.map fun execution =>
        match execution.mode with | .handoff _ => true | _ => false) = some true := by decide

theorem retiring_the_entire_cohort_stops_demand_without_finishing :
    let cancelled := retireConsumer (retireConsumer pending 0) 1
    pump (actualStep world held 64) (capture Nat.add (fun _ left _ => left) (fun _ _ => []))
      (fun _ => true) (fun _ => true) cancelled = (.noConsumers, cancelled) ∧
      cancelled.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem factors_follow_production_positions_and_cannot_be_paid_twice :
    let paid := Coefficients.ledger Nat.add (fun _ left _ => left) (fun _ _ => []) 0 (fun _ => (7 : Nat)) ready
    paid.map (·.identity) = [0, 1] ∧ paid.map (·.coefficient) = [7, 7] ∧
      Mettapedia.Algebra.SharedCoefficientLedger.merge? paid paid = some paid ∧
      Mettapedia.Algebra.SharedCoefficientLedger.append? paid
        ⟨0, OrderedDependencyStore.readStamp world 0, 7⟩ = none := by decide

end Controls

#print axioms inspect_next
#print axioms step_preserves_captured
#print axioms actions_keep_actual_source
#print axioms independent_retirement
#print axioms retirement_keeps_payload_graph
#print axioms Coefficients.ledger_valid
#print axioms Coefficients.retirement_keeps_factors
#print axioms Coefficients.delivery_keeps_factors
#print axioms Coefficients.shared_factors_once
#print axioms Coefficients.existing_factor_cannot_be_reappended
#print axioms Controls.duplicate_source_is_one_ordered_production_for_both_consumers
#print axioms Controls.cancellation_does_not_restore_or_read_the_retired_consumer
#print axioms Controls.held_source_loan_is_captured_then_acknowledged_without_new_source
#print axioms Controls.admission_refusal_retains_the_entire_paid_pending_call
#print axioms Controls.revoked_authority_does_not_unearn_the_buffered_pure_value
#print axioms Controls.stale_or_read_only_new_work_is_inert_but_unrelated_change_is_admitted
#print axioms Controls.factors_follow_production_positions_and_cannot_be_paid_twice
#print axioms Controls.absence_yield_handoff_and_exhaustion_remain_distinct
#print axioms Controls.retiring_the_entire_cohort_stops_demand_without_finishing
#print axioms open_coherent
#print axioms published_residual_eq_view
#print axioms poll_shape
#print axioms acknowledge_shape
#print axioms inspect_returns
#print axioms step_preserves_coherent
#print axioms step_rows
#print axioms path_rows
#print axioms run_open_source
#print axioms run_open_log_source
#print axioms path_preserves_captured
#print axioms run_keeps_actual_source

namespace History

open Cursor.ProducerOccurrenceLog
open Cursor.ProducerOccurrenceLog.Accounting
open Mettapedia.GSLT.Core.InferenceControl.Recording

variable {Owner : Type} {clients : Nat} [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)

local notation "sourceStep" => step construct callbackConstruct fallback authority before current reader point required quantum
local notation "sourceCapture" => capture construct callbackConstruct fallback
local notation "Cfg" => Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients
local notation "Action" => Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)

/-- The existing ordinary action runner, with the actual retained source. -/
abbrev execute (actions : List Action) (state : Cfg) :=
  runActions sourceStep sourceCapture capacity (fun _ => true) actions state

/-- A specification word of the actual source path. The bounded recorder
below remains the existing streaming worker and does not construct this word. -/
def events (actions : List Action) (state : Cfg) : List Occurrence :=
  pathOccurrences sourceStep sourceCapture capacity (fun _ => true)
    (actionPath sourceStep sourceCapture capacity (fun _ => true) actions state)

/-- Observer selection reuses the existing entry and its ordinary no-observer
branch. No history or numerical account is added to the source Call. -/
abbrev observe (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :=
  enterActionObservers sourceStep sourceCapture capacity (fun _ => true) history account actions state

theorem observe_erases (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :
    (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
      history account actions state).2.2 =
      execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state :=
  enterActionObservers_erases sourceStep sourceCapture capacity (fun _ => true) history account actions state

/-- Lawful erasure preserves the actual source computation, not just its
written answers or a trace-defined surrogate. -/
theorem observe_keeps_actual_source (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg)
    (execution : Execution (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : Coherent construct callbackConstruct fallback execution.producer) :
    ∃ next, (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        history account actions state).2.2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      Coherent construct callbackConstruct fallback next.producer := by
  rw [observe_erases]
  exact actions_keep_actual_source construct callbackConstruct fallback authority before current reader point required
    quantum capacity actions state execution attached items parameter safe coherent

set_option backward.isDefEq.respectTransparency false in
/-- The maintained path account and chronological occurrence account read the
same actual operations as the joint observer. Scheduler microsteps, source
inspections and successful consumer deliveries remain separate quantities. -/
theorem source_accounts (actions : List Action) (record : Prefix Occurrence)
    (account : ProtocolAccount) (state : Cfg) :
    letI : Quiver.{0} Cfg := actionQuiver (Output := Owner) (clients := clients) sourceStep sourceCapture capacity (fun _ => true)
    observeActions sourceStep sourceCapture capacity (fun _ => true) actions record account state =
      (Prefix.append record
        (events construct callbackConstruct fallback authority before current reader point required quantum capacity actions state),
        execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state,
        account * (splitAccount (Output := Owner) (clients := clients) sourceStep sourceCapture capacity (fun _ => true)).of
          (actionPath sourceStep sourceCapture capacity (fun _ => true) actions state)) :=
  observeActions_eq_source_accounts sourceStep sourceCapture capacity (fun _ => true) actions record account state

/-- From the real open Call, every recorded source occurrence is an ordered
admission or delivery, with the actual source invariant at its retained end. -/
theorem open_history_source (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let word := events construct callbackConstruct fallback authority before current reader point required quantum capacity actions start
    let final := (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
      history account actions start).2.2
    ProtocolSync word final ∧ CausalReceipt.Ordered [] word ∧
      CausalReceipt.WellFormed [] (protocolReceipt word) ∧
      ∃ next, final.execution = some next ∧
        BodyCallAdmission.captured construct callbackConstruct fallback
          (OrderedDependencyStore.query before reader) items parameter next.producer ∧
        Coherent construct callbackConstruct fallback next.producer := by
  dsimp only
  rw [observe_erases]
  have protocol := protocol_from_initial sourceStep sourceCapture capacity (fun _ => true)
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter context) before limit actions
  refine ⟨protocol.1, protocol.2.1, protocol.2.2.1, ?_⟩
  exact actions_keep_actual_source construct callbackConstruct fallback authority before current reader point required
    quantum capacity actions _ _ rfl items parameter
    (BodyCallAdmission.open_captured construct callbackConstruct fallback _ items parameter context)
    (open_coherent construct callbackConstruct fallback _ items parameter context)

/-- Forgetting a bounded diary retains the same actual continuation and paid
account. The reference word is neither replayed nor reconstructed at runtime. -/
theorem forget_history (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback authority before current reader point required quantum capacity none
      (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        (some record) (some account) first state).2.1 second
      (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        (some record) (some account) first state).2.2 =
      (none, some (count sourceStep sourceCapture capacity (fun _ => true) (first ++ second) account state).2,
        execute construct callbackConstruct fallback authority before current reader point required quantum capacity
          (first ++ second) state) := by
  unfold observe execute
  rw [forget_action_history_preserves_account]
  rw [count_erases]

/-- Resuming observation uses its retained capacity, accounts and actual saved
Call. This fixed-context law does not combine grants across authority changes. -/
theorem observe_append (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback authority before current reader point required quantum capacity
      history account (first ++ second) state =
      observe construct callbackConstruct fallback authority before current reader point required quantum capacity
        (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
          history account first state).1
        (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
          history account first state).2.1 second
        (observe construct callbackConstruct fallback authority before current reader point required quantum capacity
          history account first state).2.2 :=
  enterActionObservers_append sourceStep sourceCapture capacity (fun _ => true) history account first second state

/-- A diary occurrence has an actual admission/delivery operation at an actual
saved prefix of this source execution. Membership is not replay permission. -/
theorem event_has_actual_operation (actions : List Action) (state : Cfg) {event : Occurrence}
    (present : event ∈ events construct callbackConstruct fallback authority before current reader point required quantum capacity
      actions state) :
    ∃ done action later, actions = done ++ action :: later ∧
      (actionResult sourceStep sourceCapture capacity (fun _ => true) action
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity done state)).occurrence =
        some event :=
  projected_occurrence_is_a_source_reply sourceStep sourceCapture capacity (fun _ => true) actions state present

set_option backward.isDefEq.respectTransparency false in
/-- The history map retains actual path endpoints and sends composition to
chronological concatenation through the maintained occurrence RunAccount. -/
theorem path_composition {first middle last : Cfg} :
    letI : Quiver.{0} Cfg := actionQuiver (Output := Owner) (clients := clients)
      sourceStep sourceCapture capacity (fun _ => true)
    ∀ (left : Quiver.Path first middle) (right : Quiver.Path middle last),
      pathOccurrences sourceStep sourceCapture capacity (fun _ => true) (left.comp right) =
        pathOccurrences sourceStep sourceCapture capacity (fun _ => true) left ++
          pathOccurrences sourceStep sourceCapture capacity (fun _ => true) right :=
  pathOccurrences_comp sourceStep sourceCapture capacity (fun _ => true)

/-- A resumed diary contains only actual suffix events. Its earlier event
identities are an explicit causal boundary and are not fabricated replay. -/
theorem open_suffix_boundary (first second : List Action) (items : List Input)
    (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    let prefixWord := events construct callbackConstruct fallback authority before current reader point required quantum capacity first start
    let mid := execute construct callbackConstruct fallback authority before current reader point required quantum capacity first start
    let suffix := events construct callbackConstruct fallback authority before current reader point required quantum capacity second mid
    events construct callbackConstruct fallback authority before current reader point required quantum capacity (first ++ second) start =
      prefixWord ++ suffix ∧
      CausalReceipt.WellFormed (prefixWord.map CausalEvent.event) (protocolReceipt suffix) ∧
      (∀ event ∈ prefixWord, event ∉ suffix) := by
  have result := protocol_suffix_boundary sourceStep sourceCapture capacity (fun _ => true)
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter context) before limit first second
  exact ⟨result.1, result.2.1, result.2.2.2.1⟩

theorem execute_context (actions : List Action) (state : Cfg) :
    (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state).context =
      state.context := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | pump =>
          exact (ih (pump sourceStep sourceCapture capacity (fun _ => true) state).2).trans
            (pump_preserves_context_cursors_publications sourceStep sourceCapture capacity (fun _ => true) state).1
      | deliver client owner =>
          exact (ih (deliver (fun _ => true) state client owner).2).trans rfl

namespace Scopes

open Mettapedia.Algebra.SharedCoefficientLedger

variable {V Observer : Type} [DecidableEq V] [DecidableEq Observer]
    (coefficient : Stored (Output := Output) → V)

local notation "sourceLedger" => Coefficients.ledger construct callbackConstruct fallback reader coefficient
local notation "Account" => Scoped Nat (OrderedDependencyStore.ReadStamp size) V Observer

omit [DecidableEq V] in
/-- Actual execution extends the existing factor ledger in order. Dependency
and coefficient fields are retained along with occurrence identity. -/
theorem execute_ledger_extends (actions : List Action) (state : Cfg) :
    ∃ suffix, sourceLedger
      (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state) =
      sourceLedger state ++ suffix := by
  obtain ⟨suffix, rows⟩ := runActions_extends_rows sourceStep sourceCapture capacity (fun _ => true) actions state
  have base := runActions_preserves_base sourceStep sourceCapture capacity (fun _ => true) actions state
  have context := execute_context construct callbackConstruct fallback authority before current reader point required
    quantum capacity actions state
  refine ⟨(suffix.zipIdx (state.delivery.log.base + state.delivery.log.rows.length)).map
    (fun occurrence => ⟨occurrence.2, OrderedDependencyStore.readStamp state.context reader, coefficient occurrence.1⟩), ?_⟩
  simp only [Coefficients.ledger, rows, base, context, List.zipIdx_append, List.map_append]

/-- Start observation of the real buffered account with no acquired claims. -/
def begin (state : Cfg) : Account := ⟨sourceLedger state, fun _ => none⟩

/-- Extend only the production field using the actual reached source state;
previous scope claims are retained, not reissued as execution authority. -/
def carry (entry : Account) (state : Cfg) : Account := ⟨sourceLedger state, entry.claims⟩

def resume (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer) :
    Option (Account × Ledger Nat (OrderedDependencyStore.ReadStamp size) V) × Cfg :=
  if entry.productions = sourceLedger state then
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    (Scoped.handleSince? entry (carry construct callbackConstruct fallback reader coefficient entry actual) observer, actual)
  else (none, state)

theorem carry_extends (actions : List Action) (state : Cfg) (entry : Account)
    (agrees : entry.productions = sourceLedger state) :
    Scoped.extendsOccurrenceCapture entry
      (carry construct callbackConstruct fallback reader coefficient entry
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state)) = true := by
  obtain ⟨suffix, extended⟩ := execute_ledger_extends construct callbackConstruct fallback authority before current reader point required
    quantum capacity coefficient actions state
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    exact ⟨Coefficients.ledger_valid construct callbackConstruct fallback reader coefficient _,
      by change entry.productions.Sublist (sourceLedger _); rw [agrees, extended]; exact List.sublist_append_left _ _⟩
  · apply List.all_eq_true.mpr
    intro factor present
    cases claim : entry.claims factor.identity <;> simp [carry, claim]

/-- The captured ledger is validated against the actual starting source state
before any new source operation. A mismatch cannot reset or replay the source. -/
theorem resume_refused (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (mismatch : entry.productions ≠ sourceLedger state) :
    resume construct callbackConstruct fallback authority before current reader point required quantum capacity coefficient
      actions state entry observer = (none, state) := by
  simp [resume, mismatch]

/-- For a matching captured account, admission follows the actual source
continuation and the existing scoped snapshot claim operation. -/
theorem resume_granted (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (agrees : entry.productions = sourceLedger state) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    resume construct callbackConstruct fallback authority before current reader point required quantum capacity coefficient
      actions state entry observer =
      (some (Scoped.handleSince entry.productions observer world,
        Scoped.selectedSince entry.productions world), actual) := by
  simp only [resume, agrees, ↓reduceIte, Scoped.handleSince?]
  rw [carry_extends construct callbackConstruct fallback authority before current reader point required quantum capacity
    coefficient actions state entry agrees]
  rfl

omit [DecidableEq Output] [DecidableEq Owner] [DecidableEq V] [DecidableEq Observer] in
theorem begin_supported (state : Cfg) :
    (begin construct callbackConstruct fallback reader coefficient state (Observer := Observer)).Supported := by
  intro identity observer claimed
  cases claimed

omit [DecidableEq V] [DecidableEq Observer] in
/-- Supported claims remain attached to actual productions after extension
and after claiming the fresh snapshot. -/
theorem carry_supported (actions : List Action) (state : Cfg) (entry : Account)
    (agrees : entry.productions = sourceLedger state) (supported : entry.Supported) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    world.Supported := by
  dsimp only
  intro identity prior claimed
  have member := supported identity prior claimed
  obtain ⟨suffix, extended⟩ := execute_ledger_extends construct callbackConstruct fallback authority before current reader point required
    quantum capacity coefficient actions state
  have beforeMember : identity ∈ identities (sourceLedger state) := agrees ▸ member
  change identity ∈ identities (sourceLedger _ )
  rw [extended, identities, List.map_append]
  exact List.mem_append_left _ beforeMember

omit [DecidableEq V] [DecidableEq Observer] in
theorem granted_supported (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (agrees : entry.productions = sourceLedger state) (supported : entry.Supported) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    (Scoped.handleSince entry.productions observer world).Supported :=
  Scoped.handleSince_supported _ _ _
    (carry_supported construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry agrees supported)

omit [DecidableEq V] [DecidableEq Observer] in
/-- Selection is by genuine post-capture admission identity, not value
inequality; equal answers can remain distinct fresh factors. -/
theorem selected_is_actual_fresh (actions : List Action) (state : Cfg) (entry : Account)
    (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V) :
    factor ∈ Scoped.selectedSince entry.productions
      (carry construct callbackConstruct fallback reader coefficient entry
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state)) ↔
      factor ∈ sourceLedger (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state) ∧
        entry.claims factor.identity = none ∧ factor.identity ∉ identities entry.productions :=
  Scoped.mem_selectedSince _ _ _

omit [DecidableEq V] [DecidableEq Observer] in
theorem prior_claims_kept (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (identity : Nat) (prior : Observer) (claimed : entry.claims identity = some prior) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    (Scoped.handleSince entry.productions observer
      (carry construct callbackConstruct fallback reader coefficient entry actual)).claims identity = some prior :=
  Scoped.handleSince_prior_claim_preserved _ _ _ claimed

omit [DecidableEq V] [DecidableEq Observer] in
theorem snapshot_not_reselected (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    Scoped.selectedSince entry.productions (Scoped.handleSince entry.productions observer world) = [] :=
  Scoped.selectedSince_after_handle _ _ _

/-- Both account refusal and successful scoped resumption preserve the actual
independent source view and full saved Call. -/
theorem resume_keeps_source (actions : List Action) (state : Cfg) (entry : Account) (observer : Observer)
    (execution : Execution (Call construct callbackConstruct fallback (Context := Context))
      (Borrowed construct callbackConstruct fallback) Empty (Loan construct callbackConstruct fallback))
    (attached : state.execution = some execution) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : Coherent construct callbackConstruct fallback execution.producer) :
    ∃ next, (resume construct callbackConstruct fallback authority before current reader point required quantum capacity coefficient
        actions state entry observer).2.execution = some next ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter next.producer ∧
      Coherent construct callbackConstruct fallback next.producer := by
  by_cases agrees : entry.productions = sourceLedger state
  · rw [resume_granted construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry observer agrees]
    exact actions_keep_actual_source construct callbackConstruct fallback authority before current reader point required
      quantum capacity actions state execution attached items parameter safe coherent
  · rw [resume_refused construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry observer agrees]
    exact ⟨execution, attached, safe, coherent⟩

omit [DecidableEq V] [DecidableEq Observer] in
/-- Every factor of an actual open-source run cites an actual admission edge.
Its origin is obtained from the maintained protocol invariant and source path. -/
theorem factor_has_actual_operation (actions : List Action) (items : List Input) (parameter : Nat)
    (context : Context) (limit : Nat) (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V)
    (present : factor ∈ sourceLedger
      (execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions
        (initial construct callbackConstruct fallback before reader items parameter context Owner clients limit))) :
    let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
    ∃ event done action later,
      event.event = HistoryOccurrence.admission factor.identity ∧
      actions = done ++ action :: later ∧
      (actionResult sourceStep sourceCapture capacity (fun _ => true) action
        (execute construct callbackConstruct fallback authority before current reader point required quantum capacity done start)).occurrence = some event := by
  dsimp only
  let start := initial construct callbackConstruct fallback before reader items parameter context Owner clients limit
  let final := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions start
  let word := events construct callbackConstruct fallback authority before current reader point required quantum capacity actions start
  have protocol := protocol_from_initial sourceStep sourceCapture capacity (fun _ => true)
    (BodyCallAdmission.openCall construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter context) before limit actions
  have identified : identities (sourceLedger final) = List.range final.delivery.log.rows.length := by
    simp only [Coefficients.ledger, identities, List.map_map, Function.comp_def]
    rw [List.zipIdx_map_snd]
    have anchored : final.delivery.log.base = 0 := protocol.1.anchored
    rw [anchored, List.range_eq_range']
  have factorId : factor.identity ∈ List.range final.delivery.log.rows.length := by
    rw [← identified]
    exact List.mem_map.mpr ⟨factor, present, rfl⟩
  have root : HistoryOccurrence.admission factor.identity ∈ (protocolReceipt word).roots := by
    have roots : (protocolReceipt word).roots =
        (List.range final.delivery.log.rows.length).map HistoryOccurrence.admission := protocol.2.2.2
    rw [roots]
    exact List.mem_map.mpr ⟨factor.identity, factorId, rfl⟩
  obtain ⟨event, member, identity⟩ := List.mem_map.mp (admissionIdentity_in_support word root)
  obtain ⟨done, action, later, schedule, actual⟩ := event_has_actual_operation construct callbackConstruct fallback authority
    before current reader point required quantum capacity actions start member
  exact ⟨event, done, action, later, identity, schedule, actual⟩

/-- Read an older scope capture against the current actual source ledger.
This operation never advances the producer; the existing admission validates
captured factors and claims before acquiring the fresh snapshot. -/
def readScope (state : Cfg) (captured currentAccount : Account) (observer : Observer) :
    Option (Account × Ledger Nat (OrderedDependencyStore.ReadStamp size) V) :=
  if currentAccount.productions = sourceLedger state then
    Scoped.handleSince? captured currentAccount observer
  else none

omit [DecidableEq Output] [DecidableEq Owner] in
theorem readScope_refused (state : Cfg) (captured currentAccount : Account) (observer : Observer)
    (mismatch : currentAccount.productions ≠ sourceLedger state) :
    readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer = none := by
  simp [readScope, mismatch]

omit [DecidableEq Output] [DecidableEq Owner] in
/-- Accepted nested observation retains the actual production account and
cannot select the same snapshot again. -/
theorem readScope_spec (state : Cfg) (captured currentAccount result : Account)
    (observer : Observer) (observed : Ledger Nat (OrderedDependencyStore.ReadStamp size) V)
    (accepted : readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer =
      some (result, observed)) :
    result.productions = sourceLedger state ∧
      observed = Scoped.selectedSince captured.productions currentAccount ∧
      Scoped.selectedSince captured.productions result = [] := by
  unfold readScope at accepted
  split at accepted
  · rename_i agrees
    have spec := Scoped.handleSince_spec accepted
    exact ⟨spec.1.trans agrees, spec.2⟩
  · cases accepted

omit [DecidableEq Output] [DecidableEq Owner] in
/-- A stale factor capture or a lost prior claim is a refusal of the existing
scoped admission, even if the current row payloads have not changed. -/
theorem readScope_bad_capture (state : Cfg) (captured currentAccount : Account) (observer : Observer)
    (refused : Scoped.extendsOccurrenceCapture captured currentAccount = false) :
    readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer = none := by
  unfold readScope
  split
  · simp [Scoped.handleSince?, refused]
  · rfl

omit [DecidableEq Output] [DecidableEq Owner] in
theorem readScope_prior_claim (state : Cfg) (captured currentAccount result : Account)
    (observer prior : Observer) (identity : Nat)
    (observed : Ledger Nat (OrderedDependencyStore.ReadStamp size) V)
    (accepted : readScope construct callbackConstruct fallback reader coefficient state captured currentAccount observer =
      some (result, observed))
    (claimed : currentAccount.claims identity = some prior) : result.claims identity = some prior := by
  unfold readScope at accepted
  split at accepted
  · unfold Scoped.handleSince? at accepted
    split at accepted
    · cases accepted
      exact Scoped.handleSince_prior_claim_preserved _ _ _ claimed
    · cases accepted
  · cases accepted

section Transport

variable {Identity' Dependency' Observer' : Type} [DecidableEq Identity']

/-- Transport the existing scoped account using its finite production support.
The claim lookup ranges over actual factors, so unsupported copied labels do
not gain a transported claim. No producer or recorder is executed. -/
def transport (name : Nat → Identity') (dependency : OrderedDependencyStore.ReadStamp size → Dependency')
    (owner : Observer → Observer') (account : Account) : Scoped Identity' Dependency' V Observer' :=
  ⟨rename name dependency account.productions,
    fun identity => (account.productions.find? (fun factor => decide (name factor.identity = identity))).bind
      (fun factor => (account.claims factor.identity).map owner)⟩

omit [DecidableEq V] [DecidableEq Observer] in
theorem transport_claims (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (account : Account) (supported : account.Supported) (names : Function.Injective name) (identity : Nat) :
    (transport name dependency owner account).claims (name identity) = (account.claims identity).map owner := by
  cases found : account.productions.find? (fun factor => decide (name factor.identity = name identity)) with
  | some factor =>
      have predicate : decide (name factor.identity = name identity) = true :=
        List.find?_some (p := fun (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V) =>
          decide (name factor.identity = name identity)) found
      have equal := names (of_decide_eq_true predicate)
      simp [transport, found, equal]
  | none =>
      cases claimed : account.claims identity with
      | none => simp [transport, found]
      | some prior =>
          obtain ⟨factor, present, equal⟩ := List.mem_map.mp (supported identity prior claimed)
          have absent := (List.find?_eq_none.mp found) factor present
          simp [equal] at absent

omit [DecidableEq V] [DecidableEq Observer] in
theorem transport_supported (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (account : Account) : (transport name dependency owner account).Supported := by
  intro identity observer claimed
  cases found : account.productions.find? (fun factor => decide (name factor.identity = identity)) with
  | none => simp [transport, found] at claimed
  | some factor =>
      have predicate : decide (name factor.identity = identity) = true :=
        List.find?_some (p := fun (factor : Factor Nat (OrderedDependencyStore.ReadStamp size) V) =>
          decide (name factor.identity = identity)) found
      have equal := of_decide_eq_true predicate
      have present := List.mem_of_find?_eq_some found
      change identity ∈ identities (rename name dependency account.productions)
      rw [identities_rename]
      exact List.mem_map.mpr ⟨factor.identity, List.mem_map.mpr ⟨factor, present, rfl⟩, equal⟩

omit [DecidableEq V] [DecidableEq Observer] in
/-- Selection of actual post-capture factors commutes with the constructed
transport. Injectivity prevents different production identities coalescing. -/
theorem transport_selection (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (capture : Ledger Nat (OrderedDependencyStore.ReadStamp size) V) (account : Account)
    (supported : account.Supported) (names : Function.Injective name) :
    Scoped.selectedSince (rename name dependency capture) (transport name dependency owner account) =
      rename name dependency (Scoped.selectedSince capture account) :=
  Scoped.selectedSince_transport names dependency owner capture account
    (transport name dependency owner account) rfl (transport_claims name dependency owner account supported names)

omit [DecidableEq V] [DecidableEq Observer] in
theorem transport_handled_claim (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (capture : Ledger Nat (OrderedDependencyStore.ReadStamp size) V) (account : Account)
    (supported : account.Supported) (names : Function.Injective name) (observer : Observer) (identity : Nat) :
    (Scoped.handleSince (rename name dependency capture) (owner observer)
      (transport name dependency owner account)).claims (name identity) =
      ((Scoped.handleSince capture observer account).claims identity).map owner :=
  Scoped.handleSince_claim_transport names dependency owner capture account
    (transport name dependency owner account) rfl (transport_claims name dependency owner account supported names) observer identity

omit [DecidableEq V] [DecidableEq Observer] in
/-- Ordered coefficient readout is unchanged, without commutative or
cancellation assumptions. This does not identify coefficients with native work. -/
theorem transport_denotation [Monoid V] (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (capture : Ledger Nat (OrderedDependencyStore.ReadStamp size) V) (account : Account)
    (supported : account.Supported) (names : Function.Injective name) :
    denote (Scoped.selectedSince (rename name dependency capture) (transport name dependency owner account)) =
      denote (Scoped.selectedSince capture account) := by
  rw [transport_selection name dependency owner capture account supported names, denote_rename]

omit [DecidableEq V] [DecidableEq Observer] in
/-- The constructed transport applies to the actual fresh source factors
before their scoped claim, including noncommutative and zero coefficients. -/
theorem transport_actual_fresh [Monoid V] (name : Nat → Identity')
    (dependency : OrderedDependencyStore.ReadStamp size → Dependency') (owner : Observer → Observer')
    (actions : List Action) (state : Cfg) (entry : Account)
    (agrees : entry.productions = sourceLedger state) (supported : entry.Supported)
    (names : Function.Injective name) :
    let actual := execute construct callbackConstruct fallback authority before current reader point required quantum capacity actions state
    let world := carry construct callbackConstruct fallback reader coefficient entry actual
    denote (Scoped.selectedSince (rename name dependency entry.productions) (transport name dependency owner world)) =
      denote (Scoped.selectedSince entry.productions world) :=
  transport_denotation name dependency owner _ _
    (carry_supported construct callbackConstruct fallback authority before current reader point required quantum capacity
      coefficient actions state entry agrees supported) names

end Transport

#print axioms execute_ledger_extends
#print axioms carry_supported
#print axioms transport_actual_fresh
#print axioms carry_extends
#print axioms readScope_refused
#print axioms readScope_spec
#print axioms readScope_bad_capture
#print axioms readScope_prior_claim
#print axioms transport_claims
#print axioms transport_supported
#print axioms transport_selection
#print axioms transport_handled_claim
#print axioms transport_denotation
#print axioms resume_refused
#print axioms resume_granted
#print axioms begin_supported
#print axioms granted_supported
#print axioms selected_is_actual_fresh
#print axioms prior_claims_kept
#print axioms snapshot_not_reselected
#print axioms resume_keeps_source
#print axioms factor_has_actual_operation

end Scopes

namespace Controls

open Mettapedia.GSLT.Contracts
open Mettapedia.Algebra.SharedCoefficientLedger

local instance : DecidableEq (FreeMonoid Nat) := inferInstanceAs (DecidableEq (List Nat))

abbrev State := BodyCallShared.Controls.State
abbrev SourceAccount := Scoped Nat (OrderedDependencyStore.ReadStamp 3) (FreeMonoid Nat) Nat
abbrev start := BodyCallShared.Controls.initialState

abbrev sourceDecision := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision false Access.consume Access.consume

def observeActual (history : Option (Prefix (CausalEvent (HistoryOccurrence 2))))
    (account : Option ProtocolAccount) (actions : List (Accounting.Action Nat 2)) (state : State) :=
  observe (permissionDecidable := sourceDecision) Nat.add (fun _ left _ => left) (fun _ _ => [])
    BodyCallShared.Controls.sourceAuthority BodyCallShared.Controls.world BodyCallShared.Controls.world 0
    BodyCallShared.Controls.held Access.consume 64 (fun _ => true) history account actions state

def word (actions : List (Accounting.Action Nat 2)) (state : State) :=
  events (permissionDecidable := sourceDecision) Nat.add (fun _ left _ => left) (fun _ _ => [])
    BodyCallShared.Controls.sourceAuthority BodyCallShared.Controls.world BodyCallShared.Controls.world 0
    BodyCallShared.Controls.held Access.consume 64 (fun _ => true) actions state

def coefficient (stored : Stored (Output := Nat)) : FreeMonoid Nat := FreeMonoid.ofList [stored.1 + 5]

def scope (actions : List (Accounting.Action Nat 2)) (state : State) (entry : SourceAccount) (observer : Nat) :=
  Scopes.resume (permissionDecidable := sourceDecision) Nat.add (fun _ left _ => left) (fun _ _ => [])
    BodyCallShared.Controls.sourceAuthority BodyCallShared.Controls.world BodyCallShared.Controls.world 0
    BodyCallShared.Controls.held Access.consume 64 (fun _ => true) coefficient actions state entry observer

def startingAccount : SourceAccount := Scopes.begin Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient start

def firstActions : List (Accounting.Action Nat 2) := List.replicate 2 .pump
def laterActions : List (Accounting.Action Nat 2) := List.replicate 14 .pump ++ [.deliver 0 100, .deliver 1 101]
def allActions := firstActions ++ laterActions

def observed := observeActual (some (Prefix.initial 1)) (some (1, 1)) allActions start
def ordinary := observeActual none none allActions start
def earlier := observeActual (some (Prefix.initial 1)) (some (1, 1)) firstActions start
def forgotten := observeActual none earlier.2.1 laterActions earlier.2.2

def firstClaim := scope firstActions start startingAccount 11
def secondClaim := match firstClaim.1 with
  | some (entry, _) => scope laterActions firstClaim.2 entry 22
  | none => (none, firstClaim.2)

def outerRead := match secondClaim.1 with
  | some (entry, _) => Scopes.readScope Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient
      secondClaim.2 startingAccount entry 33
  | none => none

theorem actual_history_records_admissions_and_independent_deliveries :
    word allActions start = [admissionCausal 0, admissionCausal 1, deliveryCausal 0 0, deliveryCausal 1 0] ∧
      observed.1.map Prefix.items = some [admissionCausal 0] ∧
      observed.1.map (·.omitted) = some 3 ∧
      observed.2.2.delivery.log.rows = [(0, [[7]]), (1, [[7]])] := by decide

theorem producer_return_and_refused_admission_are_not_history_occurrences :
    word [.pump] start = [] ∧
      word [.pump, .pump] start = [admissionCausal 0] ∧
      word [] BodyCallShared.Controls.pending = [] := by decide

theorem erasure_and_forgetting_keep_actual_state_and_paid_account :
    observed.2.2 = ordinary.2.2 ∧ forgotten.2.2 = ordinary.2.2 ∧
      forgotten.2.1 = observed.2.1 ∧ forgotten.1 = none := ⟨rfl, rfl, rfl, rfl⟩

theorem scoped_claims_follow_equal_source_occurrences_without_double_selection :
    firstClaim.1.map (fun result => result.2.map (·.identity)) = some [0] ∧
      secondClaim.1.map (fun result => result.2.map (·.identity)) = some [1] ∧
      secondClaim.1.map (fun result => [result.1.claims 0, result.1.claims 1]) = some [some 11, some 22] ∧
      outerRead.map (fun result => result.2.map (·.identity)) = some [] ∧
      outerRead.map (fun result => [result.1.claims 0, result.1.claims 1]) = some [some 11, some 22] := by decide

def lostClaimRead := match firstClaim.1, secondClaim.1 with
  | some (capture, _), some (entry, _) =>
      Scopes.readScope Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient secondClaim.2 capture
        {entry with claims := fun _ => none} 33
  | _, _ => none

def forgedCaptureRead := match firstClaim.1, secondClaim.1 with
  | some (capture, _), some (entry, _) =>
      Scopes.readScope Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient secondClaim.2
        {capture with productions := capture.productions.map (fun (factor : Factor Nat (OrderedDependencyStore.ReadStamp 3) (FreeMonoid Nat)) =>
          {factor with coefficient := FreeMonoid.ofList [99]})}
        entry 33
  | _, _ => none

theorem erased_claim_or_forged_factor_capture_is_refused :
    lostClaimRead.isNone = true ∧ forgedCaptureRead.isNone = true := by decide

def freshWorld := firstClaim.1.map fun result =>
  Scopes.carry Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient result.1 secondClaim.2

def transportedFresh := match firstClaim.1, freshWorld with
  | some (entry, _), some world =>
      some (Scopes.transport (fun identity => identity + 100) (fun (stamp : OrderedDependencyStore.ReadStamp 3) => stamp.identity) (fun owner => owner + 1000) world,
        rename (fun identity => identity + 100) (fun (stamp : OrderedDependencyStore.ReadStamp 3) => stamp.identity) entry.productions)
  | _, _ => none

theorem constructed_transport_keeps_claims_and_ordered_fresh_coefficient :
    transportedFresh.map (fun result => result.1.claims 100) = some (some 1011) ∧
      transportedFresh.map (fun result => FreeMonoid.toList
        (denote (Scoped.selectedSince result.2 result.1))) = some [6] ∧
      freshWorld.map (fun world => world.productions.map (·.identity)) = some [0, 1] := by decide

def collapsed := secondClaim.1.map fun result => rename (fun (_ : Nat) => 0) id result.1.productions

theorem coalescing_physical_factor_identities_is_not_lawful_transport :
    collapsed.map (fun factors => decide (Valid factors)) = some false ∧
      collapsed.map (fun factors => (Mettapedia.Algebra.SharedCoefficientLedger.merge? factors factors).isNone) = some true := by decide

#print axioms actual_history_records_admissions_and_independent_deliveries
#print axioms producer_return_and_refused_admission_are_not_history_occurrences
#print axioms erasure_and_forgetting_keep_actual_state_and_paid_account
#print axioms scoped_claims_follow_equal_source_occurrences_without_double_selection
#print axioms erased_claim_or_forged_factor_capture_is_refused
#print axioms constructed_transport_keeps_claims_and_ordered_fresh_coefficient
#print axioms coalescing_physical_factor_identities_is_not_lawful_transport

end Controls

#print axioms path_composition
#print axioms open_suffix_boundary
#print axioms execute_context
#print axioms observe_erases
#print axioms observe_keeps_actual_source
#print axioms source_accounts
#print axioms open_history_source
#print axioms forget_history
#print axioms observe_append
#print axioms event_has_actual_operation

end History

end BodyCallShared

/-! Physical equation activation accounts decorate the maintained body/call
provider. The client, replies, phase indices and source instructions are the
existing ones. Proof-only invariants connect saved cursor lineages to paid
activations; neither completion nor valuation runs future source work. -/
namespace BodyCallWeighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (clause : WeighClause Weight (BodyCall.Graded.Activation Input Output))

abbrev CheckedState := { state : BodyCall.Graded.State Input Output Weight //
  BodyCall.Graded.Sound clause state ∧ BodyCall.Graded.Authentic state ∧ BodyCall.Graded.Aligned state }

def provider : Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)) where
  State _ phase := { state : CheckedState clause // state.val.core.phase = phase.down }
  step state _ :=
    let moved := BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val
    ⟨moved.1, ⟨⟨moved.2,
      BodyCall.Graded.step_sound construct callbackConstruct fallback clause _ state.val.property.1,
      BodyCall.Graded.step_authentic construct callbackConstruct fallback clause _ state.val.property.2.1,
      BodyCall.Graded.step_aligned construct callbackConstruct fallback clause _ state.val.property.2.2⟩,
      congrArg BodyCall.State.phase (BodyCall.Graded.step_link construct callbackConstruct fallback clause _)⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Erasing grading preserves every actual reply and exact saved source state. -/
def erase : Cursor.Hom (provider construct callbackConstruct fallback clause)
    (BodyCallProtocol.provider construct callbackConstruct fallback) where
  map state := ⟨state.val.val.core, state.property⟩
  step state request := by
    change (⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).1,
      ⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).2.core, _⟩⟩ :
        Σ moved : BodyCall.Move Input Output, { core : BodyCall.State Input Output // core.phase = moved.next.phase }) =
      ⟨BodyCall.step construct callbackConstruct fallback state.val.val.core,
        ⟨(BodyCall.step construct callbackConstruct fallback state.val.val.core).next, rfl⟩⟩
    calc
      _ = ⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).1,
          ⟨(BodyCall.Graded.step construct callbackConstruct fallback clause state.val.val).1.next, rfl⟩⟩ := by
        apply congrArg (Sigma.mk _)
        exact Subtype.ext (BodyCall.Graded.step_link construct callbackConstruct fallback clause _)
      _ = _ := congrArg (fun moved : BodyCall.Move Input Output =>
        (⟨moved, ⟨moved.next, rfl⟩⟩ : Σ moved : BodyCall.Move Input Output,
          { core : BodyCall.State Input Output // core.phase = moved.next.phase }))
          (BodyCall.Graded.step_move construct callbackConstruct fallback clause _)

abbrev Packet := Cursor.Packet (provider construct callbackConstruct fallback clause)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit)
abbrev Outcome := Cursor.Outcome (provider construct callbackConstruct fallback clause)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit)
abbrev Returned := Cursor.Finished (provider construct callbackConstruct fallback clause)
  (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)

def packet (state : CheckedState clause) : Packet construct callbackConstruct fallback clause :=
  ⟨⟨state.val.core.phase⟩, ⟨.advance state.val.core, rfl⟩, ⟨state, rfl⟩⟩

def openChecked (authored : List (Equation Output)) (items : List Input) (parameter : Nat) : CheckedState clause :=
  ⟨BodyCall.Graded.openState authored items parameter (.observe .noAnswers),
    BodyCall.Graded.open_sound clause authored items parameter _,
    BodyCall.Graded.open_authentic authored items parameter _,
    BodyCall.Graded.open_aligned authored items parameter _⟩

def requestCharge : Cursor.Charge (provider construct callbackConstruct fallback clause) := fun _ _ => 1

def eraseOutcome : Outcome construct callbackConstruct fallback clause →
    BodyCallProtocol.Outcome construct callbackConstruct fallback :=
  (erase construct callbackConstruct fallback clause).outcome
    (BodyCallProtocol.client (Item := Input) (Value := Output))

def stateView : Outcome construct callbackConstruct fallback clause → CheckedState clause
  | .paused packet => packet.2.2.val
  | .done returned => returned.2.2.val

def run (fuel : Nat) (state : CheckedState clause) :=
  Cursor.advance (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) fuel
    (packet construct callbackConstruct fallback clause state)

def resume (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback clause) :=
  Cursor.resume (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) fuel previous

theorem run_zero (state : CheckedState clause) :
    run construct callbackConstruct fallback clause 0 state =
      (0, .paused (packet construct callbackConstruct fallback clause state)) := rfl

theorem resume_done (fuel paid : Nat) (returned : Returned construct callbackConstruct fallback clause) :
    resume construct callbackConstruct fallback clause fuel (paid, .done returned) = (paid, .done returned) := rfl

#print axioms run_zero
#print axioms resume_done

theorem run_projection (fuel : Nat) (state : CheckedState clause) :
    ((run construct callbackConstruct fallback clause fuel state).1,
      eraseOutcome construct callbackConstruct fallback clause
        (run construct callbackConstruct fallback clause fuel state).2) =
      BodyCallProtocol.run construct callbackConstruct fallback fuel state.val.core :=
  (erase construct callbackConstruct fallback clause).advance_account
    BodyCallProtocol.client (requestCharge construct callbackConstruct fallback clause)
    (BodyCallProtocol.requestCharge construct callbackConstruct fallback) (fun _ _ => rfl) fuel _

theorem resume_projection (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback clause) :
    ((resume construct callbackConstruct fallback clause fuel previous).1,
      eraseOutcome construct callbackConstruct fallback clause
        (resume construct callbackConstruct fallback clause fuel previous).2) =
      BodyCallProtocol.resume construct callbackConstruct fallback fuel
        (previous.1, eraseOutcome construct callbackConstruct fallback clause previous.2) :=
  (erase construct callbackConstruct fallback clause).resume_account
    BodyCallProtocol.client (requestCharge construct callbackConstruct fallback clause)
    (BodyCallProtocol.requestCharge construct callbackConstruct fallback) (fun _ _ => rfl) fuel _

theorem run_split (earlier later : Nat) (state : CheckedState clause) :
    run construct callbackConstruct fallback clause (earlier + later) state =
      resume construct callbackConstruct fallback clause later
        (run construct callbackConstruct fallback clause earlier state) :=
  Cursor.advance_add _ _ _ earlier later _

theorem run_open_source (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    let actual := run construct callbackConstruct fallback clause fuel (openChecked clause authored items parameter)
    BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
      (eraseOutcome construct callbackConstruct fallback clause actual.2) =
        source construct callbackConstruct authored items parameter := by
  have projection := congrArg Prod.snd (run_projection construct callbackConstruct fallback clause fuel
    (openChecked clause authored items parameter))
  dsimp only at projection
  dsimp only
  rw [projection]
  simpa only [BodyCallProtocol.unacceptedRows, ← BodyCallProtocol.rows_view, openChecked, BodyCall.Graded.openState] using
    BodyCallProtocol.run_open_preserves_source construct callbackConstruct fallback fuel authored items parameter

/-- Every actual outcome carries valid, licensed branch factors valued at
its captured activation; equal-valued answers do not identify their factors. -/
theorem outcome_source_factors (outcome : Outcome construct callbackConstruct fallback clause) :
    let actual := (stateView construct callbackConstruct fallback clause outcome).val
    Valid actual.paid ∧ Valid actual.loan ∧
      (∀ produced ∈ actual.loan, BodyCall.Graded.Licensed produced.dependency) ∧
      actual.loan.map Factor.coefficient = actual.loan.map (fun produced => WeighClause.eval produced.dependency clause) := by
  let checked := stateView construct callbackConstruct fallback clause outcome
  exact ⟨BodyCall.Graded.paid_valid clause _ checked.property.1,
    BodyCall.Graded.loan_valid clause _ checked.property.1,
    fun produced present => checked.property.2.1 produced (checked.property.1.2.2.2.subset present),
    BodyCall.Graded.loan_source_coefficients clause _ checked.property.1⟩

#print axioms run_projection
#print axioms resume_projection
#print axioms run_split
#print axioms run_open_source
#print axioms outcome_source_factors

namespace Compact

private def packed (result : BodyCall.Move Input Output × BodyCall.Graded.Compact.State Input Output Weight)
    (linked : result.2.core = result.1.next) :
    Σ moved : BodyCall.Move Input Output,
      { state : BodyCall.Graded.Compact.State Input Output Weight // state.core.phase = moved.next.phase } :=
  ⟨result.1, ⟨result.2, congrArg BodyCall.State.phase linked⟩⟩

omit [Semiring Weight] in
private theorem packed_ext
    (first second : BodyCall.Move Input Output × BodyCall.Graded.Compact.State Input Output Weight)
    (firstLink : first.2.core = first.1.next) (secondLink : second.2.core = second.1.next)
    (same : first = second) : packed first firstLink = packed second secondLink := by
  cases same
  rfl

/-- The compact provider shares one optional-attachment transition. -/
def providerWith (attachment : BodyCall.Graded.Activation Input Output → Option Weight) :
    Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)) where
  State _ phase := { state : BodyCall.Graded.Compact.State Input Output Weight // state.core.phase = phase.down }
  step state _ := packed (BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback attachment state.val)
    (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback attachment state.val)

def provider : Cursor.Provider (BodyCallProtocol.protocol (Item := Input) (Value := Output)) :=
  providerWith construct callbackConstruct fallback (fun activation => some (WeighClause.eval activation clause))

/-- The executable cursor needs live lineages and one fresh ordinal, not a
stored ledger of earlier failed activations. -/
def erase : Cursor.Hom (BodyCallWeighted.provider construct callbackConstruct fallback clause)
    (provider construct callbackConstruct fallback clause) where
  map state := ⟨BodyCall.Graded.Compact.erase state.val.val, state.property⟩
  step _state _request :=
    packed_ext _ _ (BodyCall.Graded.step_link construct callbackConstruct fallback clause _)
      (BodyCall.Graded.Compact.step_link construct callbackConstruct fallback clause _)
      (BodyCall.Graded.Compact.step_erases construct callbackConstruct fallback clause _)

theorem advance_erases (fuel : Nat) (value : Packet construct callbackConstruct fallback clause) :
    ((Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback clause) BodyCallProtocol.client
        (requestCharge construct callbackConstruct fallback clause) fuel value).1,
      (erase construct callbackConstruct fallback clause).outcome BodyCallProtocol.client
        (Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback clause) BodyCallProtocol.client
          (requestCharge construct callbackConstruct fallback clause) fuel value).2) =
      Cursor.advance (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
        (fun _ _ => 1) fuel ((erase construct callbackConstruct fallback clause).packet BodyCallProtocol.client value) :=
  (erase construct callbackConstruct fallback clause).advance_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) (fun _ _ => 1) (fun _ _ => rfl) fuel value

theorem resume_erases (fuel : Nat) (previous : Nat × Outcome construct callbackConstruct fallback clause) :
    ((BodyCallWeighted.resume construct callbackConstruct fallback clause fuel previous).1,
      (erase construct callbackConstruct fallback clause).outcome BodyCallProtocol.client
        (BodyCallWeighted.resume construct callbackConstruct fallback clause fuel previous).2) =
      Cursor.resume (provider construct callbackConstruct fallback clause) BodyCallProtocol.client
        (fun _ _ => 1) fuel (previous.1,
          (erase construct callbackConstruct fallback clause).outcome BodyCallProtocol.client previous.2) :=
  (erase construct callbackConstruct fallback clause).resume_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback clause) (fun _ _ => 1) (fun _ _ => rfl) fuel previous

theorem returned_loan_erases (returned : Returned construct callbackConstruct fallback clause) :
    ((erase construct callbackConstruct fallback clause).finished returned).2.2.val.loan =
        returned.2.2.val.val.loan ∧
      denote ((erase construct callbackConstruct fallback clause).finished returned).2.2.val.loan =
        BodyCall.Graded.loanWeight returned.2.2.val.val := ⟨rfl, rfl⟩

#print axioms advance_erases
#print axioms resume_erases
#print axioms returned_loan_erases

namespace Attachment

variable (selection : BodyCall.Graded.Activation Input Output →
  Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)))

def erase : Cursor.Hom
    (Compact.provider construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (providerWith construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.values selection)) where
  map state := ⟨BodyCall.Graded.Compact.Attachment.erase selection state.val, state.property⟩
  step state _request :=
    packed_ext
      ((BodyCall.Graded.Compact.step construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) state.val).1,
        BodyCall.Graded.Compact.Attachment.erase selection
          (BodyCall.Graded.Compact.step construct callbackConstruct fallback
            (BodyCall.Graded.Compact.Attachment.valuation selection) state.val).2)
      _ (BodyCall.Graded.Compact.step_link construct callbackConstruct fallback _ state.val)
      (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback _ _)
      (BodyCall.Graded.Compact.Attachment.step_erases construct callbackConstruct fallback selection state.val)

/-- Compose the existing compact erasure with optional attachment selection.
The result runs one actual source provider, with no failed-history storage. -/
def fromSource :=
  (Compact.erase construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)).comp
    (erase construct callbackConstruct fallback selection)

abbrev SparseProvider := providerWith construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.values selection)
abbrev SourceOutcome := Outcome construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)

theorem advance_erases (fuel : Nat)
    (value : Packet construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) :
    ((Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection)) BodyCallProtocol.client
        (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) fuel value).1,
      (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client
        (Cursor.advance (BodyCallWeighted.provider construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.valuation selection)) BodyCallProtocol.client
          (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) fuel value).2) =
      Cursor.advance (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) fuel ((fromSource construct callbackConstruct fallback selection).packet BodyCallProtocol.client value) :=
  (fromSource construct callbackConstruct fallback selection).advance_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (fun _ _ => 1) (fun _ _ => rfl) fuel value

theorem resume_erases (fuel : Nat) (previous : Nat × SourceOutcome construct callbackConstruct fallback selection) :
    ((BodyCallWeighted.resume construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) fuel previous).1,
      (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client
        (BodyCallWeighted.resume construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.valuation selection) fuel previous).2) =
      Cursor.resume (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) fuel (previous.1,
          (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client previous.2) :=
  (fromSource construct callbackConstruct fallback selection).resume_account BodyCallProtocol.client
    (requestCharge construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (fun _ _ => 1) (fun _ _ => rfl) fuel previous

theorem returned_source_weight
    (returned : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)) :
    denote ((fromSource construct callbackConstruct fallback selection).finished returned).2.2.val.loan =
      BodyCall.Graded.loanWeight returned.2.2.val.val ∧
      Valid ((fromSource construct callbackConstruct fallback selection).finished returned).2.2.val.loan := by
  exact ⟨BodyCall.Graded.Compact.Attachment.loan_denote selection _ returned.2.2.val.property.1,
    BodyCall.Graded.Compact.Attachment.selected_valid selection _
      (BodyCall.Graded.loan_valid _ _ returned.2.2.val.property.1)⟩

/-- Every materialized factor is selected at its actual captured activation;
absence cannot masquerade as an explicit unit annotation. -/
theorem returned_factor_has_attachment
    (returned : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection))
    (produced : Factor Nat (BodyCall.Graded.Activation Input Output) Weight)
    (present : produced ∈ ((fromSource construct callbackConstruct fallback selection).finished returned).2.2.val.loan) :
    BodyCall.Graded.Licensed produced.dependency ∧
      ∃ expression, selection produced.dependency = some expression ∧
        produced.coefficient = WeighClause.eval produced.dependency expression := by
  change produced ∈ BodyCall.Graded.Compact.Attachment.selected selection returned.2.2.val.val.loan at present
  have included := List.mem_filter.mp present
  have paid := returned.2.2.val.property.1.2.2.2.subset included.1
  have coefficient := returned.2.2.val.property.1.2.1 produced paid
  constructor
  · exact returned.2.2.val.property.2.1 produced paid
  · cases attached : selection produced.dependency with
    | none => simp [attached] at included
    | some expression =>
        exact ⟨expression, rfl, by simpa [BodyCall.Graded.Compact.Attachment.valuation,
          BodyCall.Graded.Compact.Attachment.values, WeighClause.eval, attached] using coefficient⟩

#print axioms advance_erases
#print axioms resume_erases
#print axioms returned_source_weight
#print axioms returned_factor_has_attachment

abbrev SparseOutcome := Cursor.Outcome (SparseProvider construct callbackConstruct fallback selection)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit)
abbrev SparseReturned := Cursor.Finished (SparseProvider construct callbackConstruct fallback selection)
  (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)

def forget : SparseOutcome construct callbackConstruct fallback selection →
    BodyCallProtocol.Outcome construct callbackConstruct fallback :=
  Cursor.Outcome.mapState (source := SparseProvider construct callbackConstruct fallback selection)
    (target := BodyCallProtocol.provider construct callbackConstruct fallback)
    BodyCallProtocol.client (fun state => ⟨state.val.core, state.property⟩)

theorem forget_fromSource (outcome : SourceOutcome construct callbackConstruct fallback selection) :
    forget construct callbackConstruct fallback selection
      ((fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client outcome) =
      eraseOutcome construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) outcome := by
  cases outcome <;> rfl

def openPacket (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :=
  (fromSource construct callbackConstruct fallback selection).packet BodyCallProtocol.client
    (packet construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)
      (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter))

def run (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :=
  Cursor.advance (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
    (fun _ _ => 1) fuel (openPacket construct callbackConstruct fallback selection authored items parameter)

theorem run_account (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    ((BodyCallWeighted.run construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
        (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).1,
      (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client
        (BodyCallWeighted.run construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
          (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).2) =
      run construct callbackConstruct fallback selection fuel authored items parameter :=
  advance_erases construct callbackConstruct fallback selection fuel _

/-- The sparse runtime provider keeps the independent authored answer view;
attachment presence neither guesses completion nor runs future source rows. -/
theorem run_open_source (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat) :
    BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
      (forget construct callbackConstruct fallback selection
        (run construct callbackConstruct fallback selection fuel authored items parameter).2) =
      source construct callbackConstruct authored items parameter := by
  have same := congrArg Prod.snd (run_account construct callbackConstruct fallback selection fuel authored items parameter)
  dsimp only at same
  rw [← same, forget_fromSource]
  exact BodyCallWeighted.run_open_source construct callbackConstruct fallback _ fuel authored items parameter

/-- Every actual sparse returned loan has an actual source-run witness, not
just caller-supplied coefficient evidence. The firing ordinal counts all work. -/
theorem run_done_weight (fuel : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (actual : SparseReturned construct callbackConstruct fallback selection)
    (done : (run construct callbackConstruct fallback selection fuel authored items parameter).2 = .done actual) :
    ∃ reference : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection),
      (BodyCallWeighted.run construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
        (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).2 = .done reference ∧
      (fromSource construct callbackConstruct fallback selection).finished reference = actual ∧
      denote actual.2.2.val.loan = BodyCall.Graded.loanWeight reference.2.2.val.val ∧
      actual.2.2.val.nextOrdinal = reference.2.2.val.val.paid.length := by
  have same := congrArg Prod.snd (run_account construct callbackConstruct fallback selection fuel authored items parameter)
  dsimp only at same
  rw [done] at same
  cases observed : (BodyCallWeighted.run construct callbackConstruct fallback
      (BodyCall.Graded.Compact.Attachment.valuation selection) fuel
      (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)).2 with
  | paused held =>
      simp only [observed, Cursor.Hom.outcome, Cursor.Outcome.mapState] at same
      cases same
  | done reference =>
      have found : (fromSource construct callbackConstruct fallback selection).finished reference = actual := by
        simpa only [observed, Cursor.Hom.outcome, Cursor.Hom.finished, Cursor.Outcome.mapState, Cursor.Outcome.done.injEq] using same
      refine ⟨reference, rfl, found, ?_, ?_⟩
      · rw [← found]
        exact (returned_source_weight construct callbackConstruct fallback selection reference).1
      · rw [← found]
        rfl

#print axioms forget_fromSource
#print axioms run_account
#print axioms run_open_source
#print axioms run_done_weight

abbrev OwnedState := Retained.State (SparseProvider construct callbackConstruct fallback selection)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩ (List (List Output) × Context)

def isReturn (returned : SparseReturned construct callbackConstruct fallback selection) : Bool :=
  match returned.2.1 with
  | .yield _ _ => true
  | .finish rows _ => !rows.isEmpty
  | _ => false

def terminalAfter (returned : SparseReturned construct callbackConstruct fallback selection) :
    Option (SparseReturned construct callbackConstruct fallback selection) :=
  match returned.2.1 with | .yield _ _ => none | _ => some returned

def rearm (returned : SparseReturned construct callbackConstruct fallback selection) :
    Cursor.Packet (SparseProvider construct callbackConstruct fallback selection)
      (BodyCallProtocol.client (Item := Input) (Value := Output)) (⟨()⟩ : ULift Unit) :=
  ⟨returned.1, ⟨.advance returned.2.2.val.core, returned.2.2.property⟩, returned.2.2⟩

def consume (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (context : List (List Output) × Context) (returned : SparseReturned construct callbackConstruct fallback selection) :=
  let decision := accept context.2 returned
  (decision.1, (if decision.1 then context.1 ++ returned.2.1.rows else context.1, decision.2))

/-- The same retained adapter executes the sparse provider directly. Its
saved computation contains live lineages and a counter, with no paid history. -/
def ownedProvider (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context) :=
  Retained.provider (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client ⟨()⟩
    (fun _ _ => 1) quantum (isReturn construct callbackConstruct fallback selection)
    (rearm construct callbackConstruct fallback selection) (consume construct callbackConstruct fallback selection accept)

def ownedOpen (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    OwnedState construct callbackConstruct fallback selection (Context := Context) :=
  ⟨(0, .paused (openPacket construct callbackConstruct fallback selection authored items parameter)), ([], context)⟩

theorem refusal_keeps_source (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (item returned : SparseReturned construct callbackConstruct fallback selection)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback selection returned = true)
    (refused : (accept state.context.2 returned).1 = false) :
    ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨state.computation, (state.context.1, (accept state.context.2 returned).2)⟩ := by
  simp [ownedProvider, Retained.provider, ready, produced, consume, refused]

theorem acceptance_keeps_source (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (item returned : SparseReturned construct callbackConstruct fallback selection)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback selection returned = true)
    (accepted : (accept state.context.2 returned).1 = true) :
    ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨(state.computation.1, .paused (rearm construct callbackConstruct fallback selection returned)),
        (state.context.1 ++ returned.2.1.rows, (accept state.context.2 returned).2)⟩ := by
  simp [ownedProvider, Retained.provider, ready, produced, consume, accepted]

#print axioms refusal_keeps_source
#print axioms acceptance_keeps_source

set_option backward.isDefEq.respectTransparency false in
def forgetHom : Cursor.Hom (SparseProvider construct callbackConstruct fallback selection)
    (BodyCallProtocol.provider construct callbackConstruct fallback) where
  map state := ⟨state.val.core, state.property⟩
  step state _request := by
    change (⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
      (BodyCall.Graded.Compact.Attachment.values selection) state.val).1,
      ⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
        (BodyCall.Graded.Compact.Attachment.values selection) state.val).2.core, _⟩⟩ :
        Σ moved : BodyCall.Move Input Output, { core : BodyCall.State Input Output // core.phase = moved.next.phase }) =
      ⟨BodyCall.step construct callbackConstruct fallback state.val.core,
        ⟨(BodyCall.step construct callbackConstruct fallback state.val.core).next, rfl⟩⟩
    calc
      _ = ⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
          (BodyCall.Graded.Compact.Attachment.values selection) state.val).1,
          ⟨(BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
            (BodyCall.Graded.Compact.Attachment.values selection) state.val).1.next, rfl⟩⟩ := by
        apply congrArg (Sigma.mk _)
        exact Subtype.ext (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback _ _)
      _ = _ := congrArg (fun moved : BodyCall.Move Input Output =>
        (⟨moved, ⟨moved.next, rfl⟩⟩ : Σ moved : BodyCall.Move Input Output,
          { core : BodyCall.State Input Output // core.phase = moved.next.phase }))
          (BodyCall.Graded.Compact.stepWith_move construct callbackConstruct fallback _ _)

theorem resume_forget (quantum : Nat) (previous : Nat × SparseOutcome construct callbackConstruct fallback selection) :
    forget construct callbackConstruct fallback selection
      (Cursor.resume (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) quantum previous).2 =
      (BodyCallProtocol.resume construct callbackConstruct fallback quantum
        (previous.1, forget construct callbackConstruct fallback selection previous.2)).2 :=
  congrArg Prod.snd ((forgetHom construct callbackConstruct fallback selection).resume_account
    BodyCallProtocol.client (fun _ _ => 1) (BodyCallProtocol.requestCharge construct callbackConstruct fallback)
    (fun _ _ => rfl) quantum previous)

def sound (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  BodyCallProtocol.sourceSound construct callbackConstruct fallback
    (forget construct callbackConstruct fallback selection state.computation.2)

def quiet (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (forget construct callbackConstruct fallback selection state.computation.2))

def view (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) : List (List Output) :=
  state.context.1 ++ BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
    (forget construct callbackConstruct fallback selection state.computation.2)

theorem owned_step_view (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (request : Request (SparseReturned construct callbackConstruct fallback selection))
    (safe : sound construct callbackConstruct fallback selection state) :
    sound construct callbackConstruct fallback selection
        ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
          (base := ()) (index := ()) state request).2 ∧
      view construct callbackConstruct fallback selection
        ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
          (base := ()) (index := ()) state request).2 = view construct callbackConstruct fallback selection state := by
  cases request with
  | next =>
      dsimp only [ownedProvider]
      rw [Retained.next_retains_outcome]
      have kept := BodyCallProtocol.resume_source_view construct callbackConstruct fallback quantum
        (state.computation.1, forget construct callbackConstruct fallback selection state.computation.2) safe
      constructor
      · simpa only [sound, ← resume_forget] using kept.2
      · simpa only [view, ← resume_forget] using congrArg (state.context.1 ++ ·) kept.1
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [ownedProvider, Retained.provider, ready]
          exact ⟨safe, True.intro⟩
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback selection returned with
          | false =>
              simp only [ownedProvider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨safe, True.intro⟩
          | true =>
              cases decision : (accept state.context.2 returned).1 with
              | false =>
                  simp only [ownedProvider, Retained.provider, ready, produced, consume, decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨safe, rfl⟩
              | true =>
                  have readings := safe.2
                  simp only [ready, forget, Cursor.Outcome.mapState, BodyCallProtocol.stateView] at readings
                  simp only [ownedProvider, Retained.provider, ready, produced, consume, decision, ↓reduceIte]
                  constructor
                  · exact ⟨rfl, readings⟩
                  · simp [view, BodyCallProtocol.unacceptedRows, ready, rearm, forget, Cursor.Outcome.mapState,
                      BodyCallProtocol.moveView, BodyCallProtocol.stateView, BodyCall.Move.rows, BodyCall.Move.next,
                      List.append_assoc]

theorem owned_step_quiet (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (request : Request (SparseReturned construct callbackConstruct fallback selection))
    (safe : quiet construct callbackConstruct fallback selection state) :
    quiet construct callbackConstruct fallback selection
      ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
        (base := ()) (index := ()) state request).2 := by
  cases request with
  | next =>
      dsimp only [ownedProvider]
      rw [Retained.next_retains_outcome]
      have kept := BodyCallProtocol.resume_finishedQuiet construct callbackConstruct fallback quantum
        (state.computation.1, forget construct callbackConstruct fallback selection state.computation.2) safe
      simpa only [quiet, ← resume_forget] using kept
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet => simpa [ownedProvider, Retained.provider, ready] using safe
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback selection returned <;>
            cases accepted : (accept state.context.2 returned).1 <;>
            simpa [quiet, ownedProvider, Retained.provider, ready, produced, consume, accepted, rearm,
              forget, Cursor.Outcome.mapState, BodyCallProtocol.stateView, BodyCall.Move.next] using safe

abbrev Call := Nat × (Result (SparseReturned construct callbackConstruct fallback selection)
  (SparseReturned construct callbackConstruct fallback selection) ×
    OwnedState construct callbackConstruct fallback selection (Context := Context))

def openCall (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Call construct callbackConstruct fallback selection (Context := Context) :=
  (0, ⟨none, none, 0⟩, ownedOpen construct callbackConstruct fallback selection authored items parameter context)

def resumeCallSource (quantum allowance : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (previous : Call construct callbackConstruct fallback selection (Context := Context)) :=
  resumeCall (ownedProvider construct callbackConstruct fallback selection quantum accept) (fun _ _ => 1)
    allowance previous (terminalAfter construct callbackConstruct fallback selection)

def Captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  sound construct callbackConstruct fallback selection call.2.2 ∧
    quiet construct callbackConstruct fallback selection call.2.2 ∧
    view construct callbackConstruct fallback selection call.2.2 = source construct callbackConstruct authored items parameter

theorem open_captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Captured construct callbackConstruct fallback selection authored items parameter
      (openCall construct callbackConstruct fallback selection authored items parameter context) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rfl
    · change BodyCall.sourceReadings (BodyCall.openState authored items parameter (.observe .noAnswers)).work
      simp [BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]
  · change BodyCall.Phase.running = .finished → _
    intro impossible
    cases impossible
  · exact BodyCall.openState_rows construct callbackConstruct authored items parameter

theorem resume_captured (quantum allowance : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (previous : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter previous) :
    Captured construct callbackConstruct fallback selection authored items parameter
      (resumeCallSource construct callbackConstruct fallback selection quantum allowance accept previous) := by
  unfold resumeCallSource resumeCall
  cases previous.2.1.terminal with
  | some reason => exact safe
  | none =>
      refine fromCallbacks_invariant (ownedProvider construct callbackConstruct fallback selection quantum accept) (fun _ _ => 1)
        (fun (state : OwnedState construct callbackConstruct fallback selection (Context := Context)) => sound construct callbackConstruct fallback selection state ∧
          quiet construct callbackConstruct fallback selection state ∧
          view construct callbackConstruct fallback selection state = source construct callbackConstruct authored items parameter)
        ?_ allowance previous.2.1.accepted previous.2.1.pending previous.2.2 safe _
      intro state request invariant
      have kept := owned_step_view construct callbackConstruct fallback selection quantum accept state request invariant.1
      exact ⟨kept.1, owned_step_quiet construct callbackConstruct fallback selection quantum accept state request invariant.2.1,
        kept.2.trans invariant.2.2⟩

abbrev Grant := Nat × Nat × (Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)

def schedule (grants : List (Grant construct callbackConstruct fallback selection (Context := Context)))
    (initial : Call construct callbackConstruct fallback selection (Context := Context)) :=
  grants.foldl (fun previous grant => resumeCallSource construct callbackConstruct fallback selection
    grant.1 grant.2.1 grant.2.2 previous) initial

theorem schedule_captured (grants : List (Grant construct callbackConstruct fallback selection (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (initial : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter initial) :
    Captured construct callbackConstruct fallback selection authored items parameter
      (schedule construct callbackConstruct fallback selection grants initial) := by
  induction grants generalizing initial with
  | nil => exact safe
  | cons grant rest ih =>
      exact ih _ (resume_captured construct callbackConstruct fallback selection grant.1 grant.2.1 grant.2.2
        authored items parameter initial safe)

def eraseCall (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context) :=
  (call.1, ⟨⟨call.2.1.terminal.map ((forgetHom construct callbackConstruct fallback selection).finished
      (Return := fun _ _ => BodyCall.Move Input Output)),
    call.2.1.pending.map ((forgetHom construct callbackConstruct fallback selection).finished
      (Return := fun _ _ => BodyCall.Move Input Output)), call.2.1.accepted⟩,
    ⟨(call.2.2.computation.1, forget construct callbackConstruct fallback selection call.2.2.computation.2), call.2.2.context⟩⟩)

def complete (call : Call construct callbackConstruct fallback selection (Context := Context)) : Bool :=
  BodyCallAdmission.complete construct callbackConstruct fallback (eraseCall construct callbackConstruct fallback selection call)

theorem completed_source (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter call)
    (finished : complete construct callbackConstruct fallback selection call = true) :
    call.2.2.context.1 = source construct callbackConstruct authored items parameter := by
  have erased := BodyCallAdmission.completed_view construct callbackConstruct fallback
    (eraseCall construct callbackConstruct fallback selection call) safe.2.1 finished
  exact erased.symm.trans safe.2.2

def admit (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter call) :
    Option (List (List Output)) × Call construct callbackConstruct fallback selection (Context := Context) :=
  ((BodyCallAdmission.admit construct callbackConstruct fallback requested interface authored items parameter
    (eraseCall construct callbackConstruct fallback selection call) safe.2.1).1, call)

theorem mode_license (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Captured construct callbackConstruct fallback selection authored items parameter call)
    (answers : List (List Output))
    (admitted : (admit construct callbackConstruct fallback selection requested interface authored items parameter call safe).1 = some answers) :
    answers = source construct callbackConstruct authored items parameter ∧ ConventionAllows requested answers.length :=
  BodyCallAdmission.admit_license construct callbackConstruct fallback requested interface authored items parameter
    (eraseCall construct callbackConstruct fallback selection call) safe.2.1 safe.2.2 answers admitted

#print axioms resume_forget
#print axioms owned_step_view
#print axioms owned_step_quiet
#print axioms open_captured
#print axioms resume_captured
#print axioms schedule_captured
#print axioms completed_source
#print axioms mode_license

/-- A proof-only witness in the established all-attached source. The sparse
runtime state stores no witness, paid ledger or previous computation. -/
def Origin (outcome : SparseOutcome construct callbackConstruct fallback selection) : Prop :=
  ∃ reference : SourceOutcome construct callbackConstruct fallback selection,
    (fromSource construct callbackConstruct fallback selection).outcome BodyCallProtocol.client reference = outcome

def LoanOrigin (loan : SparseReturned construct callbackConstruct fallback selection) : Prop :=
  ∃ reference : Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection),
    (fromSource construct callbackConstruct fallback selection).finished reference = loan

theorem open_origin (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Origin construct callbackConstruct fallback selection
      (openCall construct callbackConstruct fallback selection authored items parameter context).2.2.computation.2 :=
  ⟨.paused (packet construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection)
    (openChecked (BodyCall.Graded.Compact.Attachment.valuation selection) authored items parameter)), rfl⟩

theorem source_resume_origin (quantum : Nat) (previous : Nat × SparseOutcome construct callbackConstruct fallback selection)
    (origin : Origin construct callbackConstruct fallback selection previous.2) :
    Origin construct callbackConstruct fallback selection
      (Cursor.resume (SparseProvider construct callbackConstruct fallback selection) BodyCallProtocol.client
        (fun _ _ => 1) quantum previous).2 := by
  obtain ⟨reference, same⟩ := origin
  refine ⟨(BodyCallWeighted.resume construct callbackConstruct fallback
    (BodyCall.Graded.Compact.Attachment.valuation selection) quantum (previous.1, reference)).2, ?_⟩
  have projected := congrArg Prod.snd (resume_erases construct callbackConstruct fallback selection quantum (previous.1, reference))
  dsimp only at projected
  simpa only [same] using projected

theorem owned_step_origin (quantum : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (state : OwnedState construct callbackConstruct fallback selection)
    (request : Request (SparseReturned construct callbackConstruct fallback selection))
    (origin : Origin construct callbackConstruct fallback selection state.computation.2) :
    Origin construct callbackConstruct fallback selection
      ((ownedProvider construct callbackConstruct fallback selection quantum accept).step
        (base := ()) (index := ()) state request).2.computation.2 := by
  cases request with
  | next =>
      dsimp only [ownedProvider]
      rw [Retained.next_retains_outcome]
      exact source_resume_origin construct callbackConstruct fallback selection quantum state.computation origin
  | accept item =>
      cases ready : state.computation.2 with
      | paused held => simpa [ownedProvider, Retained.provider, ready] using origin
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback selection returned with
          | false => simpa [ownedProvider, Retained.provider, ready, produced] using origin
          | true =>
              cases accepted : (accept state.context.2 returned).1 with
              | false => simpa [ownedProvider, Retained.provider, ready, produced, consume, accepted] using origin
              | true =>
                  obtain ⟨reference, same⟩ := origin
                  rw [ready] at same
                  cases reference with
                  | paused held => cases same
                  | done reference =>
                      have found : (fromSource construct callbackConstruct fallback selection).finished reference = returned := by
                        simpa only [Cursor.Hom.outcome, Cursor.Hom.finished, Cursor.Outcome.mapState, Cursor.Outcome.done.injEq] using same
                      simp only [ownedProvider, Retained.provider, ready, produced, consume, accepted, ↓reduceIte]
                      refine ⟨.paused ⟨reference.1,
                        ⟨.advance reference.2.2.val.val.core, reference.2.2.property⟩, reference.2.2⟩, ?_⟩
                      rw [← found]
                      rfl

theorem resume_origin (quantum allowance : Nat)
    (accept : Context → SparseReturned construct callbackConstruct fallback selection → Bool × Context)
    (previous : Call construct callbackConstruct fallback selection (Context := Context))
    (origin : Origin construct callbackConstruct fallback selection previous.2.2.computation.2) :
    Origin construct callbackConstruct fallback selection
      (resumeCallSource construct callbackConstruct fallback selection quantum allowance accept previous).2.2.computation.2 := by
  unfold resumeCallSource resumeCall
  cases previous.2.1.terminal with
  | some reason => exact origin
  | none =>
      exact fromCallbacks_invariant (ownedProvider construct callbackConstruct fallback selection quantum accept)
        (fun _ _ => 1) (fun state => Origin construct callbackConstruct fallback selection state.computation.2)
        (owned_step_origin construct callbackConstruct fallback selection quantum accept)
        allowance previous.2.1.accepted previous.2.1.pending previous.2.2 origin _

theorem held_loan_origin (state : OwnedState construct callbackConstruct fallback selection (Context := Context))
    (loan : SparseReturned construct callbackConstruct fallback selection)
    (origin : Origin construct callbackConstruct fallback selection state.computation.2)
    (held : state.computation.2 = .done loan) : LoanOrigin construct callbackConstruct fallback selection loan := by
  obtain ⟨reference, same⟩ := origin
  rw [held] at same
  cases reference with
  | paused saved => cases same
  | done reference =>
      exact ⟨reference, by simpa only [Cursor.Hom.outcome, Cursor.Hom.finished, Cursor.Outcome.mapState,
        Cursor.Outcome.done.injEq] using same⟩

theorem origin_loan_valid (loan : SparseReturned construct callbackConstruct fallback selection)
    (origin : LoanOrigin construct callbackConstruct fallback selection loan) : Valid loan.2.2.val.loan := by
  obtain ⟨reference, same⟩ := origin
  rw [← same]
  exact (returned_source_weight construct callbackConstruct fallback selection reference).2

#print axioms open_origin
#print axioms source_resume_origin
#print axioms owned_step_origin
#print axioms resume_origin
#print axioms held_loan_origin
#print axioms origin_loan_valid

end Attachment

end Compact

namespace Owned

abbrev State := Retained.State (provider construct callbackConstruct fallback clause)
  (BodyCallProtocol.client (Item := Input) (Value := Output)) ⟨()⟩ (List (List Output) × Context)

def isReturn (returned : Returned construct callbackConstruct fallback clause) : Bool :=
  match returned.2.1 with
  | .yield _ _ => true
  | .finish rows _ => !rows.isEmpty
  | _ => false

def terminalAfter (returned : Returned construct callbackConstruct fallback clause) :
    Option (Returned construct callbackConstruct fallback clause) :=
  match returned.2.1 with | .yield _ _ => none | _ => some returned

def rearm (returned : Returned construct callbackConstruct fallback clause) :=
  packet construct callbackConstruct fallback clause returned.2.2.val

def consume (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (context : List (List Output) × Context) (returned : Returned construct callbackConstruct fallback clause) :=
  let decision := accept context.2 returned
  (decision.1, (if decision.1 then context.1 ++ returned.2.1.rows else context.1, decision.2))

def provider (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context) :=
  Retained.provider (BodyCallWeighted.provider construct callbackConstruct fallback clause)
    BodyCallProtocol.client ⟨()⟩ (requestCharge construct callbackConstruct fallback clause) quantum
    (isReturn construct callbackConstruct fallback clause) (rearm construct callbackConstruct fallback clause)
    (consume construct callbackConstruct fallback clause accept)

def sound (state : State construct callbackConstruct fallback clause (Context := Context)) :=
  BodyCallProtocol.sourceSound construct callbackConstruct fallback
    (eraseOutcome construct callbackConstruct fallback clause state.computation.2)

def view (state : State construct callbackConstruct fallback clause (Context := Context)) :=
  state.context.1 ++ BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
    (eraseOutcome construct callbackConstruct fallback clause state.computation.2)

private theorem resume_source (quantum : Nat)
    (state : State construct callbackConstruct fallback clause (Context := Context))
    (safe : sound construct callbackConstruct fallback clause state) :
    let next := BodyCallWeighted.resume construct callbackConstruct fallback clause quantum state.computation
    BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
        (eraseOutcome construct callbackConstruct fallback clause next.2) =
      BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
        (eraseOutcome construct callbackConstruct fallback clause state.computation.2) ∧
      BodyCallProtocol.sourceSound construct callbackConstruct fallback
        (eraseOutcome construct callbackConstruct fallback clause next.2) := by
  have same := congrArg Prod.snd (resume_projection construct callbackConstruct fallback clause quantum state.computation)
  dsimp only at same
  dsimp only
  rw [same]
  exact BodyCallProtocol.resume_source_view construct callbackConstruct fallback quantum _ safe

theorem step_preserves_view (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause)
    (request : Request (Returned construct callbackConstruct fallback clause))
    (safe : sound construct callbackConstruct fallback clause state) :
    sound construct callbackConstruct fallback clause
        ((provider construct callbackConstruct fallback clause quantum accept).step
          (base := ()) (index := ()) state request).2 ∧
      view construct callbackConstruct fallback clause
        ((provider construct callbackConstruct fallback clause quantum accept).step
          (base := ()) (index := ()) state request).2 =
        view construct callbackConstruct fallback clause state := by
  cases request with
  | next =>
      dsimp only [provider]
      rw [Retained.next_retains_outcome]
      have kept := resume_source construct callbackConstruct fallback clause quantum state safe
      exact ⟨kept.2, congrArg (state.context.1 ++ ·) kept.1⟩
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [provider, Retained.provider, ready]
          exact ⟨safe, True.intro⟩
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback clause returned with
          | false =>
              simp only [provider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨safe, True.intro⟩
          | true =>
              cases decision : (accept state.context.2 returned).1 with
              | false =>
                  simp only [provider, Retained.provider, ready, produced, consume,
                    decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨safe, rfl⟩
              | true =>
                  have readings := safe.2
                  simp only [ready, eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState,
                    BodyCallProtocol.stateView] at readings
                  simp only [provider, Retained.provider, ready, produced, consume, decision, ↓reduceIte]
                  constructor
                  · exact ⟨rfl, readings⟩
                  · simp [view, BodyCallProtocol.unacceptedRows, ready, rearm, packet,
                      eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState,
                      BodyCallProtocol.moveView, BodyCallProtocol.stateView, BodyCall.Move.rows, BodyCall.Move.next,
                      List.append_assoc]

/-- Stateful consumer refusals preserve the real captured source view. The
callback owns the same typed, source-valued loan until acknowledgment. -/
theorem call_preserves_view (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (pending : Option (Returned construct callbackConstruct fallback clause))
    (state : State construct callbackConstruct fallback clause)
    (safe : sound construct callbackConstruct fallback clause state)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept)) :
    let actual := fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
      allowance pending accepted state (terminalAfter construct callbackConstruct fallback clause)
    sound construct callbackConstruct fallback clause actual.2.2 ∧
      view construct callbackConstruct fallback clause actual.2.2 =
        view construct callbackConstruct fallback clause state := by
  refine fromCallbacks_invariant (provider construct callbackConstruct fallback clause quantum accept) charge
    (fun next => sound construct callbackConstruct fallback clause next ∧
      view construct callbackConstruct fallback clause next = view construct callbackConstruct fallback clause state)
    ?_ allowance accepted pending state ⟨safe, rfl⟩ (terminalAfter construct callbackConstruct fallback clause)
  intro next request invariant
  have kept := step_preserves_view construct callbackConstruct fallback clause quantum accept next request invariant.1
  exact ⟨kept.1, kept.2.trans invariant.2⟩

def openState (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    State construct callbackConstruct fallback clause (Context := Context) :=
  ⟨(0, .paused (packet construct callbackConstruct fallback clause (openChecked clause authored items parameter))),
    ([], context)⟩

theorem call_open_source (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept)) :
    view construct callbackConstruct fallback clause
      (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
        allowance none accepted (openState construct callbackConstruct fallback clause authored items parameter context)
        (terminalAfter construct callbackConstruct fallback clause)).2.2 =
      source construct callbackConstruct authored items parameter := by
  have kept := call_preserves_view construct callbackConstruct fallback clause quantum allowance accepted accept none
    (openState construct callbackConstruct fallback clause authored items parameter context)
    (by
      constructor
      · rfl
      · simp [openState, eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState, packet, openChecked,
          BodyCallProtocol.stateView, BodyCall.Graded.openState, BodyCall.openState,
          BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]) charge
  exact kept.2.trans (BodyCall.openState_rows construct callbackConstruct authored items parameter)

def quiet (state : State construct callbackConstruct fallback clause (Context := Context)) :=
  BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (eraseOutcome construct callbackConstruct fallback clause state.computation.2))

private theorem step_quiet (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause)
    (request : Request (Returned construct callbackConstruct fallback clause))
    (initial : quiet construct callbackConstruct fallback clause state) :
    quiet construct callbackConstruct fallback clause
      ((provider construct callbackConstruct fallback clause quantum accept).step
        (base := ()) (index := ()) state request).2 := by
  cases request with
  | next =>
      dsimp only [provider]
      rw [Retained.next_retains_outcome]
      have same := congrArg Prod.snd (resume_projection construct callbackConstruct fallback clause quantum state.computation)
      dsimp only at same
      unfold quiet
      change BodyCallProtocol.finishedQuiet construct callbackConstruct
        (BodyCallProtocol.stateView construct callbackConstruct fallback
          (eraseOutcome construct callbackConstruct fallback clause
            (BodyCallWeighted.resume construct callbackConstruct fallback clause quantum state.computation).2))
      rw [same]
      exact BodyCallProtocol.resume_finishedQuiet construct callbackConstruct fallback quantum _ initial
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet => simpa [provider, Retained.provider, ready] using initial
      | done returned =>
          cases produced : isReturn construct callbackConstruct fallback clause returned <;>
            cases accepted : (accept state.context.2 returned).1 <;>
            simpa [quiet, provider, Retained.provider, ready, produced, consume, accepted, rearm, packet,
              eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState,
              BodyCallProtocol.stateView, BodyCall.Move.next] using initial

theorem call_quiet (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (pending : Option (Returned construct callbackConstruct fallback clause))
    (state : State construct callbackConstruct fallback clause)
    (initial : quiet construct callbackConstruct fallback clause state)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept)) :
    quiet construct callbackConstruct fallback clause
      (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
        allowance pending accepted state (terminalAfter construct callbackConstruct fallback clause)).2.2 :=
  fromCallbacks_invariant _ charge (quiet construct callbackConstruct fallback clause)
    (step_quiet construct callbackConstruct fallback clause quantum accept) allowance accepted pending state initial _

theorem open_quiet (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    quiet construct callbackConstruct fallback clause
      (openState construct callbackConstruct fallback clause authored items parameter context) := by
  simp [quiet, openState, packet, openChecked, BodyCall.Graded.openState, BodyCall.openState,
    eraseOutcome, erase, Cursor.Hom.outcome, Cursor.Outcome.mapState, BodyCallProtocol.stateView,
    BodyCallProtocol.finishedQuiet]

abbrev Call := Nat × (Result (Returned construct callbackConstruct fallback clause)
  (Returned construct callbackConstruct fallback clause) ×
    State construct callbackConstruct fallback clause (Context := Context))

def eraseCall (call : Call construct callbackConstruct fallback clause (Context := Context)) :
    BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context) :=
  (call.1, ⟨⟨call.2.1.terminal.map ((erase construct callbackConstruct fallback clause).finished
      (Return := fun _ _ => BodyCall.Move Input Output)),
    call.2.1.pending.map ((erase construct callbackConstruct fallback clause).finished
      (Return := fun _ _ => BodyCall.Move Input Output)),
    call.2.1.accepted⟩,
    ⟨(call.2.2.computation.1, eraseOutcome construct callbackConstruct fallback clause call.2.2.computation.2),
      call.2.2.context⟩⟩)

def complete (call : Call construct callbackConstruct fallback clause (Context := Context)) : Bool :=
  BodyCallAdmission.complete construct callbackConstruct fallback
    (eraseCall construct callbackConstruct fallback clause call)

/-- A producer-finished, acknowledged cut has exactly the independent
source rows. The empty residual follows from the actual transition invariant. -/
theorem completed_source (quantum allowance accepted : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (charge : Cursor.Charge (provider construct callbackConstruct fallback clause quantum accept))
    (completed :
      complete construct callbackConstruct fallback clause
        (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
          allowance none accepted (openState construct callbackConstruct fallback clause authored items parameter context)
          (terminalAfter construct callbackConstruct fallback clause)) = true) :
    (fromCallbacks (provider construct callbackConstruct fallback clause quantum accept) charge
      allowance none accepted (openState construct callbackConstruct fallback clause authored items parameter context)
      (terminalAfter construct callbackConstruct fallback clause)).2.2.context.1 =
        source construct callbackConstruct authored items parameter := by
  have kept := call_open_source construct callbackConstruct fallback clause quantum allowance accepted accept
    authored items parameter context charge
  have earned := call_quiet construct callbackConstruct fallback clause quantum allowance accepted accept none
    (openState construct callbackConstruct fallback clause authored items parameter context)
    (open_quiet construct callbackConstruct fallback clause authored items parameter context) charge
  have finished := BodyCallAdmission.completed_view construct callbackConstruct fallback
    (eraseCall construct callbackConstruct fallback clause _) earned completed
  exact finished.symm.trans kept

/-- Consumer refusal changes only its private context. The exact pending
source state, lineages, paid account and valued loan are retained. -/
theorem refused_retains_whole_computation (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause) (item returned : Returned construct callbackConstruct fallback clause)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback clause returned = true)
    (refused : (accept state.context.2 returned).1 = false) :
    ((provider construct callbackConstruct fallback clause quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨state.computation, (state.context.1, (accept state.context.2 returned).2)⟩ := by
  simp [provider, Retained.provider, ready, produced, consume, refused]

/-- Acknowledgment rearms the same actual graded source state. It neither
creates a factor nor makes another provider request, for any source quantum. -/
theorem accepted_keeps_whole_source (quantum : Nat)
    (accept : Context → Returned construct callbackConstruct fallback clause → Bool × Context)
    (state : State construct callbackConstruct fallback clause) (item returned : Returned construct callbackConstruct fallback clause)
    (ready : state.computation.2 = .done returned)
    (produced : isReturn construct callbackConstruct fallback clause returned = true)
    (accepted : (accept state.context.2 returned).1 = true) :
    ((provider construct callbackConstruct fallback clause quantum accept).step
      (base := ()) (index := ()) state (.accept item)).2 =
      ⟨(state.computation.1, .paused (rearm construct callbackConstruct fallback clause returned)),
        (state.context.1 ++ returned.2.1.rows, (accept state.context.2 returned).2)⟩ := by
  simp [provider, Retained.provider, ready, produced, consume, accepted]

#print axioms call_quiet
#print axioms open_quiet
#print axioms refused_retains_whole_computation
#print axioms accepted_keeps_whole_source

#print axioms step_preserves_view
#print axioms call_preserves_view
#print axioms call_open_source
#print axioms completed_source

end Owned

namespace Controls

abbrev build := Nat.add
def callback (tag left right : Nat) := tag + left + right
def noFallback (_ : List Nat) (_ : Nat) : List Nat := []

def valuation : WeighClause Nat (BodyCall.Graded.Activation Nat Nat) :=
  .observe (fun activation => if activation.frontier.ordinal = 0 then 11
    else if activation.frontier.ordinal = 1 then 3 else 5)

def attempted : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .mapHead (.singleton 9)⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def acceptWeights (weights : List Nat) (returned : Returned build callback noFallback valuation) : Bool × List Nat :=
  (true, weights ++ [BodyCall.Graded.loanWeight returned.2.2.val.val])

def runProgram (clause : WeighClause Nat (BodyCall.Graded.Activation Nat Nat))
    (program : List (Equation Nat)) (items : List Nat) (allowance : Nat)
    (accept : List Nat → Returned build callback noFallback clause → Bool × List Nat) :=
  fromCallbacks (Owned.provider build callback noFallback clause 64 accept) (fun _ _ => 1) allowance none 0
    (Owned.openState build callback noFallback clause program items 0 [])
    (Owned.terminalAfter build callback noFallback clause)

def completed := runProgram valuation attempted [] 3 acceptWeights

def paidWeights (call : Owned.Call build callback noFallback valuation (Context := List Nat)) :=
  (stateView build callback noFallback valuation call.2.2.computation.2).val.paid.map Factor.coefficient

/-- A failed activation is physical work, but it contributes no later branch
coefficient. Equal source values retain their distinct activation factors. -/
theorem failed_activation_and_equal_answers :
    completed.2.2.context = ([[7], [7]], [3, 5]) ∧
      paidWeights completed = [11, 3, 5] ∧ completed.2.1.accepted = 2 ∧
      Owned.complete build callback noFallback valuation completed = true := by decide

def warming (context : Bool × List Nat) (returned : Returned build callback noFallback valuation) :
    Bool × (Bool × List Nat) :=
  (context.1, (true, if context.1 then context.2 ++ [BodyCall.Graded.loanWeight returned.2.2.val.val] else context.2))

def refused := fromCallbacks (Owned.provider build callback noFallback valuation 64 warming) (fun _ _ => 1) 1 none 0
  (Owned.openState build callback noFallback valuation attempted [] 0 (false, []))
  (Owned.terminalAfter build callback noFallback valuation)

def retried := resumeCall (Owned.provider build callback noFallback valuation 0 warming) (fun _ _ => 1) 1 refused
  (Owned.terminalAfter build callback noFallback valuation)

theorem refusal_and_zero_source_retry_keep_the_actual_paid_loan :
    refused.2.1.pending.isSome = true ∧ refused.2.2.context = ([], true, []) ∧
      refused.2.1.pending.map (fun loan => BodyCall.Graded.loanWeight loan.2.2.val.val) = some 3 ∧
      retried.2.2.context = ([[7]], true, [3]) ∧ retried.2.1.accepted = 1 ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      (stateView build callback noFallback valuation retried.2.2.computation.2).val.paid.map Factor.coefficient = [11, 3] := by decide

theorem zero_acceptance_allowance_retains_pending_factor :
    resumeCall (Owned.provider build callback noFallback valuation 0 warming) (fun _ _ => 1) 0 refused
      (Owned.terminalAfter build callback noFallback valuation) = refused := resumeCall_zero _ _ _ _

def cartesian : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false,
      .append (.map (.constructor 10 .argument (.value 1)) .callTail) .callTail⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def cartesianValuation : WeighClause Nat (BodyCall.Graded.Activation Nat Nat) :=
  .observe (fun activation => if activation.frontier.ordinal = 0 then 2
    else if activation.frontier.ordinal = 1 then 3 else 5)

def acceptCartesian (weights : List Nat) (returned : Returned build callback noFallback cartesianValuation) : Bool × List Nat :=
  (true, weights ++ [BodyCall.Graded.loanWeight returned.2.2.val.val])

def cartesianCompleted := runProgram cartesianValuation cartesian [0] 5 acceptCartesian

theorem recursive_cartesian_lineage_and_callback_capture :
    cartesianCompleted.2.2.context = ([[18, 7], [18, 7], [18, 7], [18, 7]], [18, 30, 30, 50]) ∧
      (stateView build callback noFallback cartesianValuation cartesianCompleted.2.2.computation.2).val.paid.map Factor.coefficient =
        [2, 3, 3, 5, 5, 3, 5] ∧
      Owned.complete build callback noFallback cartesianValuation cartesianCompleted = true := by decide

def zeroValuation : WeighClause Nat (BodyCall.Graded.Activation Nat Nat) := .scalar 0

def acceptZero (weights : List Nat) (returned : Returned build callback noFallback zeroValuation) : Bool × List Nat :=
  (true, weights ++ [BodyCall.Graded.loanWeight returned.2.2.val.val])

def emptyCompleted := runProgram zeroValuation BodyCallRun.blank [] 2 acceptZero

theorem zero_factor_and_empty_collection_remain_physical :
    emptyCompleted.2.2.context = ([[]], [0]) ∧ emptyCompleted.2.1.accepted = 1 ∧
      (stateView build callback noFallback zeroValuation emptyCompleted.2.2.computation.2).val.paid.length = 1 ∧
      Owned.complete build callback noFallback zeroValuation emptyCompleted = true := by decide

def handedOff := runProgram valuation BodyCallRun.alienAppend [] 2 acceptWeights

theorem handoff_and_unacknowledged_loan_are_not_completion :
    Owned.complete build callback noFallback valuation handedOff = false ∧
      Owned.complete build callback noFallback valuation refused = false ∧
      handedOff.2.1.terminal.map (fun loan => loan.2.2.val.val.core.phase) = some .handoff := by decide

#print axioms failed_activation_and_equal_answers
#print axioms refusal_and_zero_source_retry_keep_the_actual_paid_loan
#print axioms zero_acceptance_allowance_retains_pending_factor
#print axioms recursive_cartesian_lineage_and_callback_capture
#print axioms zero_factor_and_empty_collection_remain_physical
#print axioms handoff_and_unacknowledged_loan_are_not_completion

end Controls

namespace AttachmentControls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls

abbrev Activation := BodyCall.Graded.Activation Nat Nat
abbrev Selection := Activation → Option (WeighClause Nat Activation)

def absent : Selection := fun _ => none
def unit : Selection := fun _ => some (.scalar 1)
def scalarProgram : List (Equation Nat) := [⟨⟨.any, .any⟩, false, .singleton 7⟩]

def accept (selection : Selection) (context : List (Nat × List Nat))
    (returned : Compact.Attachment.SparseReturned build callback noFallback selection) :
    Bool × List (Nat × List Nat) :=
  (true, context ++ [(denote returned.2.2.val.loan, identities returned.2.2.val.loan)])

def call (selection : Selection) (program : List (Equation Nat)) (items : List Nat) (allowance : Nat) :=
  fromCallbacks (Compact.Attachment.ownedProvider build callback noFallback selection 64 (accept selection))
    (fun _ _ => 1) allowance none 0 (Compact.Attachment.ownedOpen build callback noFallback selection program items 0 [])
    (Compact.Attachment.terminalAfter build callback noFallback selection)

def absentCompleted := call absent scalarProgram [] 2
def unitCompleted := call unit scalarProgram [] 2

def ordinal (selection : Selection) (outcome : Compact.Attachment.SparseOutcome build callback noFallback selection) : Nat :=
  match outcome with
  | .paused saved => saved.2.2.val.nextOrdinal
  | .done returned => returned.2.2.val.nextOrdinal

theorem absent_and_explicit_unit_are_physically_distinct :
    absentCompleted.2.2.context = ([[7]], [(1, [])]) ∧
      unitCompleted.2.2.context = ([[7]], [(1, [0])]) ∧
      ordinal absent absentCompleted.2.2.computation.2 = 1 ∧
      ordinal unit unitCompleted.2.2.computation.2 = 1 ∧
      absentCompleted.2.2.computation.1 = unitCompleted.2.2.computation.1 := by decide

def mixed : Selection := fun activation =>
  if activation.frontier.ordinal = 0 then none
  else if activation.frontier.ordinal = 1 then some (.scalar 11)
  else if activation.frontier.ordinal = 2 then some (.scalar 3) else some (.scalar 5)

def mixedProgram : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false,
      .append (.map (.constructor 10 .argument (.value 1)) .callTail) .callTail⟩,
   ⟨⟨.empty, .any⟩, false, .mapHead (.singleton 99)⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def mixedCompleted := call mixed mixedProgram [0] 5

/-- The unannotated wrapper has no factor. Failed graded activations leave
firing-identity gaps and never contaminate either saved Cartesian branch. -/
theorem mixed_failed_cartesian_and_captured_callback :
    mixedCompleted.2.2.context =
      ([[18, 7], [18, 7], [18, 7], [18, 7]],
        [(9, [2, 4]), (15, [2, 5]), (15, [6, 8]), (25, [6, 9])]) ∧
      ordinal mixed mixedCompleted.2.2.computation.2 = 10 ∧ mixedCompleted.2.1.accepted = 4 ∧
      mixedCompleted.2.1.terminal.map (fun returned => returned.2.2.val.core.phase) = some .finished := by decide

def warming (context : Bool × List (Nat × List Nat))
    (returned : Compact.Attachment.SparseReturned build callback noFallback unit) :
    Bool × (Bool × List (Nat × List Nat)) :=
  (context.1, (true, if context.1 then context.2 ++ [(denote returned.2.2.val.loan, identities returned.2.2.val.loan)] else context.2))

def refused := fromCallbacks (Compact.Attachment.ownedProvider build callback noFallback unit 64 warming)
  (fun _ _ => 1) 1 none 0 (Compact.Attachment.ownedOpen build callback noFallback unit scalarProgram [] 0 (false, []))
  (Compact.Attachment.terminalAfter build callback noFallback unit)

def retried := resumeCall (Compact.Attachment.ownedProvider build callback noFallback unit 0 warming)
  (fun _ _ => 1) 1 refused (Compact.Attachment.terminalAfter build callback noFallback unit)

theorem sparse_refusal_retry_keeps_unit_factor_and_firing_counter :
    refused.2.1.pending.map (fun returned => identities returned.2.2.val.loan) = some [0] ∧
      refused.2.2.context = ([], true, []) ∧ retried.2.2.context = ([[7]], true, [(1, [0])]) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      ordinal unit retried.2.2.computation.2 = ordinal unit refused.2.2.computation.2 ∧
      retried.2.1.accepted = 1 := by decide

theorem sparse_zero_acceptance_allowance_is_inert :
    resumeCall (Compact.Attachment.ownedProvider build callback noFallback unit 0 warming)
      (fun _ _ => 1) 0 refused (Compact.Attachment.terminalAfter build callback noFallback unit) = refused :=
  resumeCall_zero _ _ _ _

#print axioms absent_and_explicit_unit_are_physically_distinct
#print axioms mixed_failed_cartesian_and_captured_callback
#print axioms sparse_refusal_retry_keeps_unit_factor_and_firing_counter
#print axioms sparse_zero_acceptance_allowance_is_inert

end AttachmentControls

end BodyCallWeighted

/-! Shared weighted returns in one fixed pure captured source world. Numeric
factor identities are local to that producer instance. Cross-instance naming,
Need-world compatibility and effectful authority are separate contracts. -/
namespace BodyCallShared.Weighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output) (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (selection : BodyCall.Graded.Activation Input Output → Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)))

abbrev Call := BodyCallWeighted.Compact.Attachment.Call construct callbackConstruct fallback selection (Context := Context)
abbrev Loan := BodyCallWeighted.Compact.Attachment.SparseReturned construct callbackConstruct fallback selection
abbrev Borrowed := Nat × Loan construct callbackConstruct fallback selection
/-- The immutable return image stores no producer residual or IR continuation.
Its two numeric factor fields name the one-factor-per-activation source profile. -/
abbrev Stored := Nat × List (List Output) × Ledger Nat Nat Weight
abbrev Move := Cursor.ProducerOccurrenceLog.ProducerOutcome
  (Call construct callbackConstruct fallback selection (Context := Context))
  (Borrowed construct callbackConstruct fallback selection) Empty (Loan construct callbackConstruct fallback selection)

def projectLedger (ledger : Ledger Nat (BodyCall.Graded.Activation Input Output) Weight) : Ledger Nat Nat Weight :=
  ledger.map (fun produced => produced.rename id (fun _ => produced.identity))

omit [Semiring Weight] in
theorem project_identities (ledger : Ledger Nat (BodyCall.Graded.Activation Input Output) Weight) :
    identities (projectLedger ledger) = identities ledger := by
  simp [projectLedger, identities, Factor.rename, List.map_map]

theorem project_denote (ledger : Ledger Nat (BodyCall.Graded.Activation Input Output) Weight) :
    denote (projectLedger ledger) = denote ledger := by
  simp only [projectLedger, Mettapedia.Algebra.SharedCoefficientLedger.denote, List.map_map, Function.comp_def, Factor.rename]

def image (borrowed : Borrowed construct callbackConstruct fallback selection) : Stored (Output := Output) (Weight := Weight) :=
  (borrowed.1, borrowed.2.2.1.rows, projectLedger borrowed.2.2.2.val.loan)

def capture (borrowed : Borrowed construct callbackConstruct fallback selection) :
    Option (Stored (Output := Output) (Weight := Weight)) := some (image construct callbackConstruct fallback selection borrowed)

def Authentic (stored : Stored (Output := Output) (Weight := Weight)) : Prop :=
  ∃ borrowed : Borrowed construct callbackConstruct fallback selection,
    BodyCallWeighted.Compact.Attachment.LoanOrigin construct callbackConstruct fallback selection borrowed.2 ∧
      image construct callbackConstruct fallback selection borrowed = stored

theorem image_valid (borrowed : Borrowed construct callbackConstruct fallback selection)
    (origin : BodyCallWeighted.Compact.Attachment.LoanOrigin construct callbackConstruct fallback selection borrowed.2) :
    Valid (image construct callbackConstruct fallback selection borrowed).2.2 := by
  change (identities (projectLedger borrowed.2.2.2.val.loan)).Nodup
  rw [project_identities]
  exact BodyCallWeighted.Compact.Attachment.origin_loan_valid construct callbackConstruct fallback selection borrowed.2 origin

def refuse (context : Context) (_ : Loan construct callbackConstruct fallback selection) : Bool × Context := (false, context)
def accept (context : Context) (_ : Loan construct callbackConstruct fallback selection) : Bool × Context := (true, context)

def inspect (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    Move construct callbackConstruct fallback selection (Context := Context) :=
  if BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selection call then .completed call
  else match call.2.1.terminal with
    | some returned => match returned.2.1 with
      | .decline _ => .interrupted call
      | .handoff _ => .handoff returned call
      | _ => .yielded call
    | none => match call.2.1.pending with
      | some returned => .returned (call.2.1.accepted, returned) call
      | none => .yielded call

def Coherent (call : Call construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  ∀ loan, call.2.1.pending = some loan → call.2.1.terminal = none ∧
    call.2.2.computation.2 = .done loan ∧ BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selection loan = true

theorem inspect_next (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    (inspect construct callbackConstruct fallback selection call).next = call := by
  unfold inspect
  split
  · rfl
  · cases call.2.1.terminal with
    | some returned => cases moved : returned.2.1 <;> simp [moved, Cursor.ProducerOccurrenceLog.ProducerOutcome.next]
    | none => cases call.2.1.pending <;> rfl

theorem inspect_returns (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    (inspect construct callbackConstruct fallback selection call).returns =
      call.2.1.pending.toList.map (fun loan => (call.2.1.accepted, loan)) := by
  cases pending : call.2.1.pending with
  | some loan =>
      have held := coherent loan pending
      simp [inspect, BodyCallWeighted.Compact.Attachment.complete, BodyCallAdmission.complete, BodyCallWeighted.Compact.Attachment.eraseCall, pending, held.1,
        Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
  | none =>
      unfold inspect
      split
      · rfl
      · cases terminal : call.2.1.terminal with
        | none => simp [pending, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
        | some returned => cases moved : returned.2.1 <;> simp [moved, Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]

theorem poll_shape (quantum : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context))
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none) :
    let later := BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection quantum 1
      (refuse construct callbackConstruct fallback selection) call
    later.2.2.context = call.2.2.context ∧ later.2.1.accepted = call.2.1.accepted ∧
      Coherent construct callbackConstruct fallback selection later := by
  cases outcome : (Cursor.resume (BodyCallWeighted.Compact.Attachment.SparseProvider construct callbackConstruct fallback selection)
      BodyCallProtocol.client (fun _ _ => 1) quantum call.2.2.computation).2 with
  | paused saved =>
      simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty, fromCallbacks,
        BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome, Coherent]
  | done returned =>
      cases produced : BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selection returned <;>
        simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty, fromCallbacks,
          BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome, produced, BodyCallWeighted.Compact.Attachment.consume, refuse, Coherent]

theorem acknowledge_shape (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call)
    (loan : Loan construct callbackConstruct fallback selection) (pending : call.2.1.pending = some loan) :
    let later := BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection 0 1
      (accept construct callbackConstruct fallback selection) call
    later.2.1.pending = none ∧ later.2.2.context.1 = call.2.2.context.1 ++ loan.2.1.rows ∧
      later.2.1.accepted = call.2.1.accepted + 1 ∧ Coherent construct callbackConstruct fallback selection later := by
  have held := coherent loan pending
  cases final : BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selection loan <;>
    simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, held.1, pending, fromCallbacks,
      BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, held.2.1, held.2.2, BodyCallWeighted.Compact.Attachment.consume, accept, final, Coherent]

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

def poll (quantum : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context)) :=
  if OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) then
    if FrameUpdate point.authority required then
      BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection quantum 1
        (refuse construct callbackConstruct fallback selection) call
    else call
  else call

def step (quantum : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context)) :
    Move construct callbackConstruct fallback selection (Context := Context) :=
  BodyCallShared.retainedStep (inspect construct callbackConstruct fallback selection)
    (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection 0 1
      (accept construct callbackConstruct fallback selection))
    (poll construct callbackConstruct fallback selection authority before current reader point required quantum) call

def Safe (items : List Input) (parameter : Nat) (call : Call construct callbackConstruct fallback selection (Context := Context)) : Prop :=
  BodyCallWeighted.Compact.Attachment.Captured construct callbackConstruct fallback selection (OrderedDependencyStore.query before reader) items parameter call ∧
    BodyCallWeighted.Compact.Attachment.Origin construct callbackConstruct fallback selection call.2.2.computation.2 ∧
    Coherent construct callbackConstruct fallback selection call

theorem open_safe (items : List Input) (parameter : Nat) (context : Context) :
    Safe construct callbackConstruct fallback selection before reader items parameter
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selection (OrderedDependencyStore.query before reader) items parameter context) := by
  refine ⟨BodyCallWeighted.Compact.Attachment.open_captured construct callbackConstruct fallback selection _ items parameter context,
    BodyCallWeighted.Compact.Attachment.open_origin construct callbackConstruct fallback selection _ items parameter context, ?_⟩
  intro loan pending
  cases pending

set_option backward.isDefEq.respectTransparency false in
theorem poll_safe (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter call)
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none) :
    Safe construct callbackConstruct fallback selection before reader items parameter
      (poll construct callbackConstruct fallback selection authority before current reader point required quantum call) := by
  by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
  · by_cases allowed : FrameUpdate point.authority required
    · simpa [poll, fresh, allowed] using
        (show Safe construct callbackConstruct fallback selection before reader items parameter
          (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selection quantum 1
            (refuse construct callbackConstruct fallback selection) call) from
          ⟨BodyCallWeighted.Compact.Attachment.resume_captured construct callbackConstruct fallback selection quantum 1
            (refuse construct callbackConstruct fallback selection) _ items parameter call safe.1,
            BodyCallWeighted.Compact.Attachment.resume_origin construct callbackConstruct fallback selection quantum 1
              (refuse construct callbackConstruct fallback selection) call safe.2.1,
            (poll_shape construct callbackConstruct fallback selection quantum call running empty).2.2⟩)
    · simpa [poll, fresh, allowed] using safe
  · simpa [poll, fresh] using safe

set_option backward.isDefEq.respectTransparency false in
theorem step_safe (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter call) :
    Safe construct callbackConstruct fallback selection before reader items parameter
      (step construct callbackConstruct fallback selection authority before current reader point required quantum call).next := by
  unfold step BodyCallShared.retainedStep
  split
  · simpa only [inspect_next] using safe
  · cases pending : call.2.1.pending with
    | some loan =>
        exact ⟨BodyCallWeighted.Compact.Attachment.resume_captured construct callbackConstruct fallback selection 0 1
          (accept construct callbackConstruct fallback selection) _ items parameter call safe.1,
          BodyCallWeighted.Compact.Attachment.resume_origin construct callbackConstruct fallback selection 0 1
            (accept construct callbackConstruct fallback selection) call safe.2.1,
          (acknowledge_shape construct callbackConstruct fallback selection call safe.2.2 loan pending).2.2.2⟩
    | none =>
        simpa only [inspect_next] using poll_safe construct callbackConstruct fallback selection authority before current reader point required
          quantum items parameter call safe (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending

theorem inspect_origin (call : Call construct callbackConstruct fallback selection (Context := Context))
    (origin : BodyCallWeighted.Compact.Attachment.Origin construct callbackConstruct fallback selection call.2.2.computation.2)
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    ∀ borrowed ∈ (inspect construct callbackConstruct fallback selection call).returns,
      Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed) := by
  rw [inspect_returns construct callbackConstruct fallback selection call coherent]
  intro borrowed present
  obtain ⟨loan, loanMember, equal⟩ := List.mem_map.mp present
  subst borrowed
  have pending : call.2.1.pending = some loan := Option.mem_toList.mp loanMember
  exact ⟨(call.2.1.accepted, loan), BodyCallWeighted.Compact.Attachment.held_loan_origin construct callbackConstruct fallback selection
    call.2.2 loan origin (coherent loan pending).2.1, rfl⟩

theorem step_origins (quantum : Nat) (items : List Input) (parameter : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter call) :
    ∀ borrowed ∈ (step construct callbackConstruct fallback selection authority before current reader point required quantum call).returns,
      Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed) := by
  unfold step BodyCallShared.retainedStep
  split
  · exact inspect_origin construct callbackConstruct fallback selection call safe.2.1 safe.2.2
  · cases pending : call.2.1.pending with
    | some loan => simp [Cursor.ProducerOccurrenceLog.ProducerOutcome.returns]
    | none =>
        have kept := poll_safe construct callbackConstruct fallback selection authority before current reader point required
          quantum items parameter call safe (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending
        exact inspect_origin construct callbackConstruct fallback selection _ kept.2.1 kept.2.2

#print axioms project_identities
#print axioms project_denote
#print axioms image_valid
#print axioms open_safe
#print axioms step_safe
#print axioms step_origins



def publishedRows (call : Call construct callbackConstruct fallback selection (Context := Context)) : List (List Output) :=
  call.2.2.context.1 ++ call.2.1.pending.toList.flatMap (fun loan => loan.2.1.rows)

def residualRows (call : Call construct callbackConstruct fallback selection (Context := Context)) : List (List Output) :=
  match call.2.1.pending with
  | some _ => BodyCall.workRows construct callbackConstruct (BodyCallProtocol.stateView construct callbackConstruct fallback
      (BodyCallWeighted.Compact.Attachment.forget construct callbackConstruct fallback selection call.2.2.computation.2)).work
  | none => BodyCallProtocol.unacceptedRows construct callbackConstruct fallback
      (BodyCallWeighted.Compact.Attachment.forget construct callbackConstruct fallback selection call.2.2.computation.2)

theorem published_residual_eq_view (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    publishedRows construct callbackConstruct fallback selection call ++ residualRows construct callbackConstruct fallback selection call =
      BodyCallWeighted.Compact.Attachment.view construct callbackConstruct fallback selection call.2.2 := by
  cases pending : call.2.1.pending with
  | none => simp [publishedRows, residualRows, pending, BodyCallWeighted.Compact.Attachment.view]
  | some loan =>
      have held := coherent loan pending
      simp [publishedRows, residualRows, pending, BodyCallWeighted.Compact.Attachment.view, held.2.1,
        BodyCallWeighted.Compact.Attachment.forget, Cursor.Outcome.mapState,
        BodyCallProtocol.unacceptedRows, BodyCallProtocol.moveView, List.append_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem step_rows (quantum : Nat)
    (call : Call construct callbackConstruct fallback selection (Context := Context))
    (coherent : Coherent construct callbackConstruct fallback selection call) :
    publishedRows construct callbackConstruct fallback selection
        (step construct callbackConstruct fallback selection authority before current reader point required quantum call).next =
      publishedRows construct callbackConstruct fallback selection call ++
        (step construct callbackConstruct fallback selection authority before current reader point required quantum call).returns.flatMap
          (fun borrowed => borrowed.2.2.1.rows) := by
  unfold step BodyCallShared.retainedStep
  split
  · rw [inspect_next, inspect_returns construct callbackConstruct fallback selection call coherent]
    have empty : call.2.1.pending = none := by
      cases pending : call.2.1.pending with
      | none => rfl
      | some loan =>
          have held := coherent loan pending
          simp [held.1] at ‹call.2.1.terminal.isSome = true›
    simp [empty]
  · cases pending : call.2.1.pending with
    | some loan =>
        have shape := acknowledge_shape construct callbackConstruct fallback selection call coherent loan pending
        simp [Cursor.ProducerOccurrenceLog.ProducerOutcome.next,
          Cursor.ProducerOccurrenceLog.ProducerOutcome.returns, publishedRows, shape.1, shape.2.1, pending]
    | none =>
        by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
        · by_cases permitted : FrameUpdate point.authority required
          · simp only [poll, fresh, permitted, ↓reduceIte]
            have shape := poll_shape construct callbackConstruct fallback selection quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) pending
            rw [inspect_next, inspect_returns construct callbackConstruct fallback selection _ shape.2.2]
            simp [publishedRows, shape.1, shape.2.1, pending, List.flatMap_map]
          · simp only [poll, fresh, permitted, ↓reduceIte]
            rw [inspect_next, inspect_returns construct callbackConstruct fallback selection call coherent]
            simp [pending]
        · simp only [poll, fresh, Bool.false_eq_true, ↓reduceIte]
          rw [inspect_next, inspect_returns construct callbackConstruct fallback selection call coherent]
          simp [pending]

theorem path_rows (quantum : Nat) (items : List Input) (parameter : Nat)
    {first last : Call construct callbackConstruct fallback selection (Context := Context)}
    {returns : List (Borrowed construct callbackConstruct fallback selection)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath
      (step construct callbackConstruct fallback selection authority before current reader point required quantum) first returns last)
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter first) :
    publishedRows construct callbackConstruct fallback selection last =
      publishedRows construct callbackConstruct fallback selection first ++ returns.flatMap (fun loan => loan.2.2.1.rows) := by
  induction path with
  | refl => simp
  | @next first move later returns transition tail ih =>
      have kept := step_safe construct callbackConstruct fallback selection authority before current reader
        point required quantum items parameter first safe
      have row := step_rows construct callbackConstruct fallback selection authority before current reader point required
        quantum first safe.2.2
      rw [transition] at kept row
      rw [ih kept, row, List.flatMap_append, List.append_assoc]

abbrev Configuration (Owner : Type) (clients : Nat) :=
  Cursor.ProducerOccurrenceLog.Configuration
    (Call construct callbackConstruct fallback selection (Context := Context))
    (Borrowed construct callbackConstruct fallback selection)
    (Stored (Output := Output) (Weight := Weight))
    (OrderedDependencyStore.Store (Equation Output) size) Owner Empty
    (Loan construct callbackConstruct fallback selection) clients

def initial (items : List Input) (parameter : Nat) (context : Context) (Owner : Type) (clients limit : Nat) :
    Configuration construct callbackConstruct fallback selection (Context := Context) (size := size) Owner clients :=
  Cursor.ProducerOccurrenceLog.initial
    (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selection
      (OrderedDependencyStore.query before reader) items parameter context) before limit

variable {Owner : Type} {clients : Nat} (quantum : Nat)
local notation "sourceStep" => step construct callbackConstruct fallback selection authority before current reader point required quantum
local notation "sourceCapture" => capture construct callbackConstruct fallback selection
local notation "Cfg" => Configuration construct callbackConstruct fallback selection (Context := Context) (size := size) Owner clients

/-- The whole saved source remains reachable. Authentication of immutable row
images is a proposition, never an extra field of a stored return. -/
def Accounted (items : List Input) (parameter : Nat) (state : Cfg) : Prop :=
  (∃ execution, state.execution = some execution ∧
    Safe construct callbackConstruct fallback selection before reader items parameter execution.producer) ∧
  (∀ stored ∈ state.delivery.log.rows, Authentic construct callbackConstruct fallback selection stored) ∧
  (∀ borrowed ∈ (Cursor.ProducerOccurrenceLog.pending state).toList,
    Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed))

theorem initial_accounted (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit) := by
  refine ⟨⟨_, rfl, open_safe construct callbackConstruct fallback selection before reader items parameter context⟩, ?_, ?_⟩
  · simp [initial, Cursor.ProducerOccurrenceLog.initial, Cursor.SharedOccurrenceLog.initial]
  · simp [initial, Cursor.ProducerOccurrenceLog.initial, Cursor.ProducerOccurrenceLog.pending]

theorem path_safe (items : List Input) (parameter : Nat)
    {first last : Call construct callbackConstruct fallback selection (Context := Context)}
    {returned : List (Borrowed construct callbackConstruct fallback selection)}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath sourceStep first returned last)
    (safe : Safe construct callbackConstruct fallback selection before reader items parameter first) :
    Safe construct callbackConstruct fallback selection before reader items parameter last ∧
      ∀ borrowed ∈ returned,
        Authentic construct callbackConstruct fallback selection (image construct callbackConstruct fallback selection borrowed) := by
  induction path with
  | refl => exact ⟨safe, by simp⟩
  | @next source outcome rest target transition tail ih =>
      have nextSafe := step_safe construct callbackConstruct fallback selection authority before current reader point required
        quantum items parameter source safe
      have nextOrigins := step_origins construct callbackConstruct fallback selection authority before current reader point required
        quantum items parameter source safe
      rw [transition] at nextSafe nextOrigins
      obtain ⟨finalSafe, origins⟩ := ih nextSafe
      refine ⟨finalSafe, ?_⟩
      intro borrowed member
      rcases List.mem_append.mp member with earlier | later
      · exact nextOrigins borrowed earlier
      · exact origins borrowed later

set_option backward.isDefEq.respectTransparency false in
theorem pump_accounted (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2 := by
  obtain ⟨⟨execution, attached, safe⟩, rows, pending⟩ := accounted
  obtain ⟨next, retained, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path
    sourceStep sourceCapture capacity (fun _ => true) state execution attached
  obtain ⟨nextSafe, returned⟩ := path_safe construct callbackConstruct fallback selection authority before current reader point required
    quantum items parameter path safe
  have conserved := Cursor.ProducerOccurrenceLog.pump_conservation
    (image construct callbackConstruct fallback selection) id sourceStep sourceCapture capacity (fun _ => true)
    (fun borrowed stored captured => by cases captured; rfl) state
  have authentic : ∀ stored ∈
      (Cursor.ProducerOccurrenceLog.admitted (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1) ++
        (Cursor.ProducerOccurrenceLog.pending (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2).toList.map
          (image construct callbackConstruct fallback selection),
      Authentic construct callbackConstruct fallback selection stored := by
    simpa only [List.map_id] using (show ∀ stored ∈
      (Cursor.ProducerOccurrenceLog.pending state).toList.map (image construct callbackConstruct fallback selection) ++
        (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).map
          (image construct callbackConstruct fallback selection),
      Authentic construct callbackConstruct fallback selection stored from by
        intro stored member
        rcases List.mem_append.mp member with old | new
        · obtain ⟨borrowed, present, same⟩ := List.mem_map.mp old
          subst stored
          exact pending borrowed present
        · obtain ⟨borrowed, present, same⟩ := List.mem_map.mp new
          subst stored
          exact returned borrowed present) |> fun proof => by
            rw [conserved] at proof
            simpa only [List.map_id] using proof
  refine ⟨⟨next, retained, nextSafe⟩, ?_, ?_⟩
  · rw [Cursor.ProducerOccurrenceLog.pump_rows]
    intro stored member
    rcases List.mem_append.mp member with old | new
    · exact rows stored old
    · exact authentic stored (List.mem_append_left _ new)
  · intro borrowed member
    exact authentic _ (List.mem_append_right _ (List.mem_map.mpr ⟨borrowed, member, rfl⟩))

variable [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]

set_option backward.isDefEq.respectTransparency false in
theorem delivery_accounted (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (client : Fin clients) (owner : Owner) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 := by
  obtain ⟨⟨execution, attached, safe⟩, rows, pending⟩ := accounted
  refine ⟨⟨execution, ?_, safe⟩, ?_, ?_⟩
  · simpa only [Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using attached
  · cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
      simpa [Cursor.ProducerOccurrenceLog.deliver, Cursor.SharedOccurrenceOwnership.advance, Cursor.SharedOccurrenceOwnership.acknowledge,
        Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceLog.pull, Cursor.SharedOccurrenceLog.setPosition, reply] using rows
  · simpa only [Cursor.ProducerOccurrenceLog.pending,
      Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using pending

theorem actions_accounted (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state) :
    Accounted construct callbackConstruct fallback selection before reader items parameter
      (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state) := by
  induction actions generalizing state with
  | nil => exact accounted
  | cons action rest ih =>
      cases action with
      | pump => exact ih _ (pump_accounted construct callbackConstruct fallback selection authority before current reader point required
          quantum capacity items parameter state accounted)
      | deliver client owner => exact ih _ (delivery_accounted construct callbackConstruct fallback selection before reader
          items parameter state accounted client owner)

#print axioms path_safe
#print axioms pump_accounted
#print axioms actions_accounted


/-- Publication alignment is proved from the actual log operations. It is
not an assumption that consumer acceptance equals an authored answer list. -/
def Aligned (state : Cfg) : Prop :=
  ∀ execution, state.execution = some execution →
    state.delivery.log.rows.flatMap (·.2.1) ++
      (Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (fun loan => loan.2.2.1.rows) =
      publishedRows construct callbackConstruct fallback selection execution.producer

omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
theorem initial_aligned (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    Aligned construct callbackConstruct fallback selection
      (initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit) := by
  intro execution attached
  cases attached
  rfl

omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
set_option backward.isDefEq.respectTransparency false in
theorem pump_aligned (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (aligned : Aligned construct callbackConstruct fallback selection state) :
    Aligned construct callbackConstruct fallback selection
      (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2 := by
  intro next attachedNext
  obtain ⟨⟨execution, attached, safe⟩, _, _⟩ := accounted
  obtain ⟨target, attachedTarget, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path
    sourceStep sourceCapture capacity (fun _ => true) state execution attached
  have same : target = next := Option.some.inj (attachedTarget.symm.trans attachedNext)
  subst next
  have row := path_rows construct callbackConstruct fallback selection authority before current reader point required
    quantum items parameter path safe
  have conserved := Cursor.ProducerOccurrenceLog.pump_conservation
    (fun (loan : Borrowed construct callbackConstruct fallback selection) => loan.2.2.1.rows)
    (fun (stored : Stored (Output := Output) (Weight := Weight)) => stored.2.1)
    sourceStep sourceCapture capacity (fun _ => true)
    (by intro loan stored captured; cases captured; rfl) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  calc
    _ = (state.delivery.log.rows.flatMap (·.2.1) ++
          (Cursor.ProducerOccurrenceLog.admitted (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap (·.2.1)) ++
          (Cursor.ProducerOccurrenceLog.pending (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2).toList.flatMap
            (fun loan => loan.2.2.1.rows) := by rw [Cursor.ProducerOccurrenceLog.pump_rows, List.flatMap_append]
    _ = state.delivery.log.rows.flatMap (·.2.1) ++
          ((Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (fun loan => loan.2.2.1.rows) ++
            (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap
              (fun loan => loan.2.2.1.rows)) := by rw [List.append_assoc, ← flat]
    _ = publishedRows construct callbackConstruct fallback selection execution.producer ++
          (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap
            (fun loan => loan.2.2.1.rows) := by rw [← List.append_assoc, aligned execution attached]
    _ = _ := row.symm

private theorem delivery_rows (state : Cfg) (client : Fin clients) (owner : Owner) :
    (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2.delivery.log.rows = state.delivery.log.rows := by
  cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
    simp [Cursor.ProducerOccurrenceLog.deliver, Cursor.SharedOccurrenceOwnership.advance,
      Cursor.SharedOccurrenceOwnership.acknowledge, Cursor.SharedOccurrenceOwnership.prepare,
      Cursor.SharedOccurrenceLog.pull, Cursor.SharedOccurrenceLog.setPosition, reply]

theorem delivery_aligned (state : Cfg) (aligned : Aligned construct callbackConstruct fallback selection state)
    (client : Fin clients) (owner : Owner) :
    Aligned construct callbackConstruct fallback selection
      (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 := by
  intro execution attached
  simpa only [delivery_rows, Cursor.ProducerOccurrenceLog.pending,
    Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using
    aligned execution (by simpa only [Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using attached)

theorem actions_aligned (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (aligned : Aligned construct callbackConstruct fallback selection state) :
    Aligned construct callbackConstruct fallback selection
      (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state) := by
  induction actions generalizing state with
  | nil => exact aligned
  | cons action rest ih =>
      cases action with
      | pump =>
          apply ih _
          · exact pump_accounted construct callbackConstruct fallback selection authority before current reader point required quantum capacity items parameter state accounted
          · exact pump_aligned construct callbackConstruct fallback selection authority before current reader point required quantum capacity items parameter state accounted aligned
      | deliver client owner =>
          apply ih _
          · exact delivery_accounted construct callbackConstruct fallback selection before reader items parameter state accounted client owner
          · exact delivery_aligned construct callbackConstruct fallback selection state aligned client owner

/-- Every arbitrary action word keeps the actual source Call and each
compact branch image, and partitions source answers into the admitted prefix,
the held return, and the full saved residual in occurrence order. -/
theorem actions_open_source (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit
    let final := Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions start
    Accounted construct callbackConstruct fallback selection before reader items parameter final ∧
      ∃ execution, final.execution = some execution ∧
        final.delivery.log.rows.flatMap (·.2.1) ++
          (Cursor.ProducerOccurrenceLog.pending final).toList.flatMap (fun loan => loan.2.2.1.rows) ++
          residualRows construct callbackConstruct fallback selection execution.producer =
          source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  have startAccounted := initial_accounted construct callbackConstruct fallback selection before reader items parameter context limit (Owner := Owner) (clients := clients)
  have startAligned := initial_aligned construct callbackConstruct fallback selection before reader items parameter context limit (Owner := Owner) (clients := clients)
  have finalAccounted := actions_accounted construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions
    items parameter _ startAccounted
  have finalAligned := actions_aligned construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions
    items parameter _ startAccounted startAligned
  obtain ⟨execution, attached, safe⟩ := finalAccounted.1
  refine ⟨finalAccounted, execution, attached, ?_⟩
  rw [finalAligned execution attached, published_residual_eq_view construct callbackConstruct fallback selection execution.producer safe.2.2]
  exact safe.1.2.2

#print axioms actions_open_source


omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
set_option backward.isDefEq.respectTransparency false in
/-- A stored row denotes the selected branch of its authentic source loan.
The failed physical ledger is not folded into this per-row interpretation. -/
theorem authentic_factors (stored : Stored (Output := Output) (Weight := Weight))
    (authentic : Authentic construct callbackConstruct fallback selection stored) :
    ∃ reference : BodyCallWeighted.Returned construct callbackConstruct fallback (BodyCall.Graded.Compact.Attachment.valuation selection),
      stored.2.1 = reference.2.1.rows ∧
      stored.2.2 = projectLedger (BodyCall.Graded.Compact.Attachment.selected selection reference.2.2.val.val.loan) ∧
      Mettapedia.Algebra.SharedCoefficientLedger.denote stored.2.2 = BodyCall.Graded.loanWeight reference.2.2.val.val ∧
      Valid stored.2.2 := by
  obtain ⟨borrowed, origin, same⟩ := authentic
  subst stored
  obtain ⟨reference, projected⟩ := origin
  refine ⟨reference, ?_, ?_, ?_, image_valid construct callbackConstruct fallback selection borrowed ⟨reference, projected⟩⟩
  · dsimp only [image]
    rw [← projected]
    rfl
  · dsimp only [image]
    rw [← projected]
    rfl
  · change Mettapedia.Algebra.SharedCoefficientLedger.denote (projectLedger borrowed.2.2.2.val.loan) = _
    rw [project_denote, ← projected]
    exact (BodyCallWeighted.Compact.Attachment.returned_source_weight construct callbackConstruct fallback selection reference).1

omit [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner] in
/-- Completion readout is earned in the captured source world. No current
permission check can turn this completed pure value into unfinished code. -/
theorem completed_log_source (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Accounted construct callbackConstruct fallback selection before reader items parameter state)
    (aligned : Aligned construct callbackConstruct fallback selection state)
    (execution : Cursor.ProducerOccurrenceLog.Execution
      (Call construct callbackConstruct fallback selection (Context := Context))
      (Borrowed construct callbackConstruct fallback selection) Empty (Loan construct callbackConstruct fallback selection))
    (attached : state.execution = some execution)
    (noLoan : Cursor.ProducerOccurrenceLog.pending state = none)
    (finished : BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selection execution.producer = true) :
    state.delivery.log.rows.flatMap (·.2.1) = source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨⟨actual, retained, safe⟩, _, _⟩ := accounted
  have same : actual = execution := Option.some.inj (retained.symm.trans attached)
  subst actual
  have noPending : execution.producer.2.1.pending = none := by
    cases pending : execution.producer.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallWeighted.Compact.Attachment.complete, BodyCallWeighted.Compact.Attachment.eraseCall,
        BodyCallAdmission.complete, pending] at finished
  have row := aligned execution attached
  simp only [noLoan, Option.toList_none, List.flatMap_nil, List.append_nil, publishedRows,
    noPending] at row
  exact row.trans (BodyCallWeighted.Compact.Attachment.completed_source construct callbackConstruct fallback selection
    _ items parameter execution.producer safe.1 finished)

section BranchScopes

omit [Semiring Weight] [DecidableEq Output] [DecidableEq Owner]
variable {Observer : Type} [DecidableEq Observer]
local notation "Account" => Scoped Nat Nat Weight Observer

/-- A scope checks the actual immutable branch image and its captured factors.
This claims contributions for readout; it neither issues execution authority
nor combines the ledgers of different alternatives. -/
def observeBranch (stored : Stored (Output := Output) (Weight := Weight))
    (entry current : Account) (observer : Observer) : Option (Account × Ledger Nat Nat Weight) :=
  if current.productions = stored.2.2 then Scoped.handleSince? entry current observer else none

theorem observeBranch_spec (stored : Stored (Output := Output) (Weight := Weight))
    (entry current result : Account) (observer : Observer) (observed : Ledger Nat Nat Weight)
    (accepted : observeBranch stored entry current observer = some (result, observed)) :
    current.productions = stored.2.2 ∧ entry.productions.Sublist stored.2.2 ∧
      result.productions = stored.2.2 ∧ observed = Scoped.selectedSince entry.productions current ∧
      Scoped.selectedSince entry.productions result = [] := by
  unfold observeBranch at accepted
  split at accepted
  · next same =>
      have spec := Scoped.handleSince_spec accepted
      have checked : Scoped.extendsOccurrenceCapture entry current = true := by
        unfold Scoped.handleSince? at accepted
        split at accepted
        · assumption
        · cases accepted
      exact ⟨same, same ▸ (Scoped.extendsOccurrenceCapture_valid checked).2, spec.1.trans same, spec.2⟩
  · cases accepted

theorem observeBranch_claims (stored : Stored (Output := Output) (Weight := Weight))
    (entry current result : Account) (observer : Observer) (observed : Ledger Nat Nat Weight)
    (supported : current.Supported)
    (accepted : observeBranch stored entry current observer = some (result, observed)) :
    result.Supported ∧ (∀ identity prior, current.claims identity = some prior → result.claims identity = some prior) ∧
      (∀ produced ∈ observed, result.claims produced.identity = some observer ∧
        produced ∈ stored.2.2 ∧ produced.identity ∉ identities entry.productions) := by
  unfold observeBranch at accepted
  split at accepted
  · next same =>
      unfold Scoped.handleSince? at accepted
      split at accepted
      · cases accepted
        refine ⟨Scoped.handleSince_supported _ _ _ supported, ?_, ?_⟩
        · intro identity prior claimed
          exact Scoped.handleSince_prior_claim_preserved _ _ _ claimed
        · intro produced member
          have present := (Scoped.mem_selectedSince entry.productions current produced).mp member
          exact ⟨Scoped.selectedSince_claimed _ _ _ member, same ▸ present.1, present.2.2⟩
      · cases accepted
  · cases accepted

end BranchScopes

#print axioms authentic_factors
#print axioms completed_log_source
#print axioms observeBranch_spec
#print axioms observeBranch_claims


/-- Retiring one independently held consumer preserves the whole actual
source, its captured context, protocol account, and the other's ordered view.
The schedule must not subsequently deliver to the retired consumer. -/
theorem independent_retirement (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (account : Cursor.ProducerOccurrenceLog.Accounting.ProtocolAccount) (state : Cfg)
    (retired other : Fin clients) (position : Nat) (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : Cursor.ProducerOccurrenceLog.Accounting.sparesRetired retired actions) :
    let original := Cursor.ProducerOccurrenceLog.Accounting.count sourceStep sourceCapture capacity (fun _ => true) actions account state
    let cancelled := Cursor.ProducerOccurrenceLog.Accounting.count sourceStep sourceCapture capacity (fun _ => true) actions account
      (Cursor.ProducerOccurrenceLog.retireConsumer state retired)
    cancelled.1.execution = original.1.execution ∧ cancelled.1.context = original.1.context ∧
      cancelled.2 = original.2 ∧
      Cursor.SharedOccurrenceLog.peek cancelled.1.delivery.log other = Cursor.SharedOccurrenceLog.peek original.1.delivery.log other ∧
      Cursor.SharedOccurrenceLog.unread cancelled.1.delivery.log other = Cursor.SharedOccurrenceLog.unread original.1.delivery.log other := by
  dsimp only
  rw [Cursor.ProducerOccurrenceLog.Accounting.count_after_retained_demand sourceStep sourceCapture capacity (fun _ => true)
    actions account state retired other position distinct live spares]
  exact ⟨rfl, rfl, rfl, (Cursor.ProducerOccurrenceLog.retireConsumer_releases_only_its_retention _ retired).2.2 other distinct⟩

namespace History

open Cursor.ProducerOccurrenceLog
open Cursor.ProducerOccurrenceLog.Accounting
open Mettapedia.GSLT.Core.InferenceControl.Recording

variable (capacity : Stored (Output := Output) (Weight := Weight) → Bool)
local notation "Action" => Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)

abbrev observe (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :=
  enterActionObservers sourceStep sourceCapture capacity (fun _ => true) history account actions state

/-- Optional history and protocol accounting erase to this same operational
source instance, including the complete Call and immutable branch images. -/
theorem source_erasure (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := initial construct callbackConstruct fallback selection before reader items parameter context Owner clients limit
    let observed := observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity history account actions start
    observed.2.2 = runActions sourceStep sourceCapture capacity (fun _ => true) actions start ∧
      Accounted construct callbackConstruct fallback selection before reader items parameter observed.2.2 ∧
      Aligned construct callbackConstruct fallback selection observed.2.2 := by
  dsimp only
  rw [enterActionObservers_erases]
  exact ⟨rfl,
    actions_accounted construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions items parameter _
      (initial_accounted construct callbackConstruct fallback selection before reader items parameter context limit),
    actions_aligned construct callbackConstruct fallback selection authority before current reader point required quantum capacity actions items parameter _
      (initial_accounted construct callbackConstruct fallback selection before reader items parameter context limit)
      (initial_aligned construct callbackConstruct fallback selection before reader items parameter context limit)⟩

theorem forget_keeps_source_and_account (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity none
      (observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity (some record) (some account) first state).2.1 second
      (observe construct callbackConstruct fallback selection authority before current reader point required quantum capacity (some record) (some account) first state).2.2 =
      (none, some (count sourceStep sourceCapture capacity (fun _ => true) (first ++ second) account state).2,
        runActions sourceStep sourceCapture capacity (fun _ => true) (first ++ second) state) := by
  unfold observe
  rw [forget_action_history_preserves_account, count_erases]

/-- Each observed admission/delivery occurrence belongs to an actual operation
at an actual prefix of this saved source. It grants no execution authority. -/
theorem occurrence_origin (actions : List Action) (state : Cfg) {event : Occurrence}
    (present : event ∈ pathOccurrences sourceStep sourceCapture capacity (fun _ => true)
      (actionPath sourceStep sourceCapture capacity (fun _ => true) actions state)) :
    ∃ done action later, actions = done ++ action :: later ∧
      (actionResult sourceStep sourceCapture capacity (fun _ => true) action
        (runActions sourceStep sourceCapture capacity (fun _ => true) done state)).occurrence = some event :=
  projected_occurrence_is_a_source_reply sourceStep sourceCapture capacity (fun _ => true) actions state present

#print axioms source_erasure
#print axioms forget_keeps_source_and_account
#print axioms occurrence_origin

end History

#print axioms independent_retirement


namespace Controls

open Cursor.ProducerOccurrenceLog
open Mettapedia.GSLT.Contracts
open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)
open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallShared.Controls (sourceAuthority held revoked)

abbrev Activation := BodyCall.Graded.Activation Nat Nat

def attachment (activation : Activation) : Option (WeighClause Nat Activation) :=
  some (.scalar (if activation.frontier.ordinal = 0 then 2
    else if activation.frontier.ordinal = 1 then 11 else if activation.frontier.ordinal = 2 then 3 else 5))

def authored : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .mapHead .callTail⟩,
   ⟨⟨.empty, .any⟩, false, .mapHead (.singleton 99)⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def world : OrderedDependencyStore.Store (Equation Nat) 1 := OrderedDependencyStore.initial 947 (fun _ => authored)

abbrev State := Configuration build callback noFallback attachment (Context := Unit) (size := 1) Nat 2

def start : State := initial build callback noFallback attachment world 0 [0] 0 () Nat 2 8

def actualStep (quantum : Nat) :=
  step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
    build callback noFallback attachment sourceAuthority world world 0 held .consume quantum (Context := Unit)

def captureRow := capture build callback noFallback attachment

def ordinary (ticks : Nat) (state : State) :=
  Cursor.ProducerOccurrenceLog.ordinary (actualStep 64) captureRow (fun _ => true) (fun _ => true) ticks state

def ready := ordinary 16 start
def pending := ordinary 1 start
def captured := ordinary 2 start
def acknowledged := ordinary 3 start

def ordinal (call : Call build callback noFallback attachment (Context := Unit)) : Nat :=
  match call.2.2.computation.2 with
  | .paused saved => saved.2.2.val.nextOrdinal
  | .done returned => returned.2.2.val.nextOrdinal

def sourceState (call : Call build callback noFallback attachment (Context := Unit)) : BodyCall.Graded.Compact.State Nat Nat Nat :=
  match call.2.2.computation.2 with
  | .paused saved => saved.2.2.val
  | .done returned => returned.2.2.val

def leftRow := ready.delivery.log.rows[0]!
def rightRow := ready.delivery.log.rows[1]!

/-- The failed coefficient belongs to physical work, not either branch.
Equal answers share the real outer factor and retain distinct alternatives. -/
theorem shared_outer_failed_and_equal_alternatives :
    ready.delivery.log.rows.map (fun row => (row.1, row.2.1, identities row.2.2,
      Mettapedia.Algebra.SharedCoefficientLedger.denote row.2.2)) =
        [(0, [[7]], [0, 2], 6), (1, [[7]], [0, 3], 10)] ∧
      ready.delivery.log.completed = true ∧ ready.execution.map (fun execution => ordinal execution.producer) = some 4 ∧
      leftRow.2.2.head? = rightRow.2.2.head? := by decide

def first := deliver (fun _ => true) captured 0 100
def cancelled := retireConsumer first.2 0
def otherFinished := ordinary 16 cancelled

theorem independent_delivery_and_cancel_keep_existing_branch_factors :
    first.1 = .observed (.answer 0 (0, [[7]], [⟨0, 0, 2⟩, ⟨2, 2, 3⟩])) ∧
      (deliver (fun _ => true) otherFinished 1 101).1 = first.1 ∧
      otherFinished.delivery.log.rows = ready.delivery.log.rows ∧
      Cursor.SharedOccurrenceLog.unread otherFinished.delivery.log 0 = [] ∧
      Cursor.SharedOccurrenceLog.unread otherFinished.delivery.log 1 = ready.delivery.log.rows ∧
      otherFinished.execution.map (fun execution => ordinal execution.producer) = some 4 := by
  exact ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩

/-- A refused capture keeps the actual paid loan and producer residual.
The later acknowledgment accepts that loan with no provider operation. -/
theorem refusal_zero_and_acknowledgment_keep_the_actual_loan :
    pump (actualStep 64) captureRow (fun _ => false) (fun _ => true) pending = (.admissionRefused, pending) ∧
      ordinary 0 pending = pending ∧
      captured.execution.map (fun execution => execution.producer.2.2.computation.1) =
        acknowledged.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      captured.execution.map (fun execution => sourceState execution.producer) =
        acknowledged.execution.map (fun execution => sourceState execution.producer) ∧
      captured.execution.map (fun execution => execution.producer.2.1.pending.isSome) = some true ∧
      acknowledged.execution.map (fun execution => execution.producer.2.1.pending.isSome) = some false := by
  exact ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

def outer : Scoped Nat Nat Nat Nat := ⟨[⟨0, 0, 2⟩], fun _ => none⟩
def leftWorld : Scoped Nat Nat Nat Nat := ⟨leftRow.2.2, fun _ => none⟩
def rightWorld : Scoped Nat Nat Nat Nat := ⟨rightRow.2.2, fun _ => none⟩
def handled := observeBranch leftRow outer leftWorld 17

theorem scoped_readout_excludes_shared_prefix_and_rejects_sibling_capture :
    handled.map (fun result => (result.2.map Factor.identity, Mettapedia.Algebra.SharedCoefficientLedger.denote result.2)) = some ([2], 3) ∧
      (observeBranch rightRow outer rightWorld 18).map (fun result => (identities result.2,
        Mettapedia.Algebra.SharedCoefficientLedger.denote result.2)) = some ([3], 5) ∧
      (handled.bind fun result => observeBranch leftRow outer result.1 19).map (fun result => identities result.2) = some [] ∧
      observeBranch rightRow leftWorld rightWorld 19 = none ∧
      observeBranch leftRow outer rightWorld 19 = none := by decide

namespace Stateful

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.AttachmentControls (unit scalarProgram warming)

def initialCall := BodyCallWeighted.Compact.Attachment.openCall build callback noFallback unit scalarProgram ([] : List Nat) 0 (false, ([] : List (Nat × List Nat)))
def paused := BodyCallWeighted.Compact.Attachment.resumeCallSource build callback noFallback unit 1 1 warming initialCall
def refused := BodyCallWeighted.Compact.Attachment.resumeCallSource build callback noFallback unit 64 1 warming paused
def retried := BodyCallWeighted.Compact.Attachment.resumeCallSource build callback noFallback unit 0 1 warming refused

theorem state_changing_refusal_resumes_same_paid_source :
    paused.2.1.pending.isNone = true ∧ (match paused.2.2.computation.2 with | .paused _ => true | .done _ => false) = true ∧
      refused.2.1.pending.isSome = true ∧ refused.2.2.context = ([], true, []) ∧
      retried.2.2.context = ([[7]], true, [(1, [0])]) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      retried.2.1.accepted = 1 := by decide

end Stateful


def programRun (program : List (Equation Nat)) : State :=
  let capturedWorld := OrderedDependencyStore.initial 948 (fun (_ : Fin 1) => program)
  Cursor.ProducerOccurrenceLog.ordinary
    (step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
      build callback noFallback attachment sourceAuthority capturedWorld capturedWorld 0 held .consume 64)
    captureRow (fun _ => true) (fun _ => true) 16
    (initial build callback noFallback attachment capturedWorld 0 [] 0 () Nat 2 8)

theorem yield_failure_empty_collection_and_handoff_remain_distinct :
    pending.delivery.log.completed = false ∧ pending.delivery.log.rows = [] ∧
      (programRun BodyCallRun.missed).delivery.log.completed = true ∧
      (programRun BodyCallRun.missed).delivery.log.rows = [] ∧
      (programRun BodyCallRun.blank).delivery.log.rows.map (fun row => (row.2.1, identities row.2.2)) = [([[]], [0])] ∧
      (programRun BodyCallRun.alienAppend).delivery.log.completed = false ∧
      (programRun BodyCallRun.alienAppend).execution.map (fun execution =>
        match execution.mode with | .handoff _ => true | _ => false) = some true := by decide

namespace Observation

open Mettapedia.GSLT.Core.InferenceControl.Recording

abbrev Word := List (Cursor.ProducerOccurrenceLog.Accounting.Action Nat 2)
def first : Word := [.pump, .pump, .deliver 0 100]
def rest : Word := List.replicate 16 .pump ++ [.deliver 1 101]

def recorded := History.observe
  (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
  build callback noFallback attachment sourceAuthority world world 0 held .consume 64 (fun _ => true)
  (some (Prefix.initial 1)) (some 1) first start

def forgotten := History.observe
  (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
  build callback noFallback attachment sourceAuthority world world 0 held .consume 64 (fun _ => true)
  none recorded.2.1 rest recorded.2.2

theorem forgetting_keeps_actual_source_factors_and_paid_account :
    forgotten = (none,
      some (Cursor.ProducerOccurrenceLog.Accounting.count (actualStep 64) captureRow (fun _ => true) (fun _ => true)
        (first ++ rest) 1 start).2,
      Cursor.ProducerOccurrenceLog.Accounting.runActions (actualStep 64) captureRow (fun _ => true) (fun _ => true) (first ++ rest) start) :=
  History.forget_keeps_source_and_account
    (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
    build callback noFallback attachment sourceAuthority world world 0 held .consume 64 (fun _ => true)
    (Prefix.initial 1) 1 first rest start

end Observation

#print axioms yield_failure_empty_collection_and_handoff_remain_distinct
#print axioms Observation.forgetting_keeps_actual_source_factors_and_paid_account

#print axioms shared_outer_failed_and_equal_alternatives
#print axioms independent_delivery_and_cancel_keep_existing_branch_factors
#print axioms refusal_zero_and_acknowledgment_keep_the_actual_loan
#print axioms scoped_readout_excludes_shared_prefix_and_rejects_sibling_capture
#print axioms Stateful.state_changing_refusal_resumes_same_paid_source

end Controls

end BodyCallShared.Weighted

/-! Authored weighted correspondence uses the maintained sparse provider and
client. The independent meaning is recursive on source Code/equations; these
views inspect only the actual current reply, branch factors and saved work. -/
namespace BodyCallWeighted.Authored

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

def selection (activation : BodyCall.Graded.Activation Input Output) :
    Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)) :=
  (BodyCall.WeightedSource.activationValue attachment activation).map WeighClause.scalar

@[simp] theorem selection_values :
    BodyCall.Graded.Compact.Attachment.values (selection attachment) =
      BodyCall.WeightedSource.activationValue attachment := by
  funext activation
  cases attached : BodyCall.WeightedSource.activationValue attachment activation <;>
    simp [BodyCall.Graded.Compact.Attachment.values, selection, attached, WeighClause.eval]

local notation "M" => Compact.Attachment.SparseProvider construct callbackConstruct fallback (selection attachment)
local notation "C" => (BodyCallProtocol.client (Item := Input) (Value := Output))
local notation "Packet" => Cursor.Packet M C (⟨()⟩ : ULift Unit)
local notation "Outcome" => Cursor.Outcome M C (⟨()⟩ : ULift Unit)
local notation "Returned" => Cursor.Finished M (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)

def stateView : Outcome → BodyCall.Graded.Compact.State Input Output Weight
  | .paused packet => packet.2.2.val
  | .done returned => returned.2.2.val

def moveView : Outcome → BodyCall.Move Input Output
  | .paused packet => packet.2.1.val
  | .done returned => returned.2.1

private theorem forget_state (outcome : Outcome) :
    BodyCallProtocol.stateView construct callbackConstruct fallback
        (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) outcome) =
      (stateView construct callbackConstruct fallback attachment outcome).core := by
  cases outcome <;> rfl

private theorem forget_move (outcome : Outcome) :
    BodyCallProtocol.moveView construct callbackConstruct fallback
        (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) outcome) =
      moveView construct callbackConstruct fallback attachment outcome := by
  cases outcome <;> rfl

def safe (outcome : Outcome) : Prop :=
  BodyCall.sourceReadings (stateView construct callbackConstruct fallback attachment outcome).core.work ∧
    (stateView construct callbackConstruct fallback attachment outcome).branches.length =
      (stateView construct callbackConstruct fallback attachment outcome).core.work.length

def residual (state : BodyCall.Graded.Compact.State Input Output Weight) :=
  BodyCall.WeightedSource.workRows construct callbackConstruct attachment state.core.work state.branches

def unaccepted (outcome : Outcome) :=
  BodyCall.WeightedSource.emitted (moveView construct callbackConstruct fallback attachment outcome)
      (stateView construct callbackConstruct fallback attachment outcome).loan ++
    residual construct callbackConstruct attachment (stateView construct callbackConstruct fallback attachment outcome)

private def replyPacket (actual : BodyCall.Move Input Output × BodyCall.Graded.Compact.State Input Output Weight)
    (linked : actual.2.core = actual.1.next) : Packet :=
  ⟨⟨actual.1.next.phase⟩, ⟨actual.1, rfl⟩, ⟨actual.2, congrArg BodyCall.State.phase linked⟩⟩

/-- One bounded client inspection sequence conserves the independent weighted
residual. A pending reply is counted once without another source operation. -/
theorem advance_view (fuel : Nat) (packet : Packet)
    (readings : BodyCall.sourceReadings packet.2.2.val.core.work)
    (aligned : packet.2.2.val.branches.length = packet.2.2.val.core.work.length) :
    let outcome := (Cursor.advance M C (fun _ _ => 1) fuel packet).2
    unaccepted construct callbackConstruct fallback attachment outcome =
        BodyCall.WeightedSource.emitted packet.2.1.val packet.2.2.val.loan ++
          residual construct callbackConstruct attachment packet.2.2.val ∧
      safe construct callbackConstruct fallback attachment outcome := by
  induction fuel generalizing packet with
  | zero => exact ⟨rfl, readings, aligned⟩
  | succ fuel ih =>
      rcases packet with ⟨phase, ⟨control, controlPhase⟩, ⟨state, statePhase⟩⟩
      cases control with
      | advance saved =>
          let actual := BodyCall.Graded.Compact.stepWith construct callbackConstruct fallback
            (BodyCall.Graded.Compact.Attachment.values (selection attachment)) state
          have one : BodyCall.WeightedSource.emitted actual.1 actual.2.loan ++
              residual construct callbackConstruct attachment actual.2 =
                residual construct callbackConstruct attachment state := by
            simpa only [actual, selection_values, residual] using
              BodyCall.WeightedSource.step_preserves_rows construct callbackConstruct fallback attachment state aligned readings
          have kept : BodyCall.sourceReadings actual.2.core.work := by
            simpa only [actual, BodyCall.Graded.Compact.stepWith_link, BodyCall.Graded.Compact.stepWith_move] using
              BodyCall.step_preserves_sourceReadings construct callbackConstruct fallback state.core readings
          have nextAligned : actual.2.branches.length = actual.2.core.work.length := by
            simpa only [actual, selection_values] using
              BodyCall.WeightedSource.step_aligned construct callbackConstruct fallback attachment state aligned
          have later := ih (replyPacket construct callbackConstruct fallback attachment actual
            (BodyCall.Graded.Compact.stepWith_link construct callbackConstruct fallback _ state)) kept nextAligned
          exact ⟨later.1.trans one, later.2⟩
      | yield row next => exact ⟨rfl, readings, aligned⟩
      | finish rows next => exact ⟨rfl, readings, aligned⟩
      | decline next => exact ⟨rfl, readings, aligned⟩
      | handoff next => exact ⟨rfl, readings, aligned⟩

/-- Arbitrary bounded resumption preserves the complete earned reply and
weighted future view. This uses scheduler inspections, not native work ticks. -/
theorem resume_view (fuel : Nat) (previous : Nat × Outcome)
    (valid : safe construct callbackConstruct fallback attachment previous.2) :
    unaccepted construct callbackConstruct fallback attachment
        (Cursor.resume M C (fun _ _ => 1) fuel previous).2 =
      unaccepted construct callbackConstruct fallback attachment previous.2 ∧
    safe construct callbackConstruct fallback attachment
      (Cursor.resume M C (fun _ _ => 1) fuel previous).2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done returned => exact ⟨rfl, valid⟩
  | paused packet => exact advance_view construct callbackConstruct fallback attachment fuel packet valid.1 valid.2

theorem run_open_source (fuel : Nat) (authored : List (Equation Output))
    (items : List Input) (parameter : Nat) :
    let actual := Compact.Attachment.run construct callbackConstruct fallback (selection attachment) fuel authored items parameter
    unaccepted construct callbackConstruct fallback attachment actual.2 =
        BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter ∧
      safe construct callbackConstruct fallback attachment actual.2 := by
  have viewed := advance_view construct callbackConstruct fallback attachment fuel
    (Compact.Attachment.openPacket construct callbackConstruct fallback (selection attachment) authored items parameter)
    (by
      change BodyCall.sourceReadings (BodyCall.openState authored items parameter (.observe .noAnswers)).work
      simp [BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]) (by rfl)
  exact ⟨viewed.1.trans (BodyCall.WeightedSource.open_rows construct callbackConstruct attachment authored items parameter), viewed.2⟩

/-- An ordinary result-collecting consumer folds actual weighted loans. The
user callback retains arbitrary context updates, including stateful refusal;
no factor is generated by this consumer and no future source answer is read. -/
def reader (accept : Context → Returned → Bool × Context)
    (context : List (BodyCall.WeightedSource.Row Output Weight) × Context) (returned : Returned) :=
  let decision := accept context.2 returned
  (decision.1,
    (if decision.1 then context.1 ++ BodyCall.WeightedSource.emitted returned.2.1 returned.2.2.val.loan else context.1,
      decision.2))

local notation "Owned" => Compact.Attachment.OwnedState construct callbackConstruct fallback (selection attachment)
  (Context := List (BodyCall.WeightedSource.Row Output Weight) × Context)
local notation "Call" => Compact.Attachment.Call construct callbackConstruct fallback (selection attachment)
  (Context := List (BodyCall.WeightedSource.Row Output Weight) × Context)

def view (state : Owned) :=
  state.context.2.1 ++ unaccepted construct callbackConstruct fallback attachment state.computation.2

/-- The existing retained callback engine preserves weighted output plus
residual under acceptance, refusal, source pause and terminal re-entry. -/
theorem owned_step_view (quantum : Nat) (accept : Context → Returned → Bool × Context)
    (state : Owned) (request : Request Returned)
    (valid : safe construct callbackConstruct fallback attachment state.computation.2) :
    let later := ((Compact.Attachment.ownedProvider construct callbackConstruct fallback (selection attachment)
      quantum (reader construct callbackConstruct fallback attachment accept)).step
        (base := ()) (index := ()) state request).2
    safe construct callbackConstruct fallback attachment later.computation.2 ∧
      view construct callbackConstruct fallback attachment later = view construct callbackConstruct fallback attachment state := by
  cases request with
  | next =>
      dsimp only [Compact.Attachment.ownedProvider]
      rw [Retained.next_retains_outcome]
      have kept := resume_view construct callbackConstruct fallback attachment quantum state.computation valid
      exact ⟨kept.2, congrArg (state.context.2.1 ++ ·) kept.1⟩
  | accept item =>
      cases ready : state.computation.2 with
      | paused packet =>
          simp only [Compact.Attachment.ownedProvider, Retained.provider, ready]
          exact ⟨by simpa only [ready] using valid, True.intro⟩
      | done returned =>
          cases produced : Compact.Attachment.isReturn construct callbackConstruct fallback (selection attachment) returned with
          | false =>
              simp only [Compact.Attachment.ownedProvider, Retained.provider, ready, produced, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by simpa only [ready] using valid, True.intro⟩
          | true =>
              cases decision : (accept state.context.2.2 returned).1 with
              | false =>
                  simp only [Compact.Attachment.ownedProvider, Retained.provider, ready, produced,
                    Compact.Attachment.consume, reader, decision, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨by simpa only [ready] using valid, rfl⟩
              | true =>
                  simp only [Compact.Attachment.ownedProvider, Retained.provider, ready, produced,
                    Compact.Attachment.consume, reader, decision, ↓reduceIte]
                  constructor
                  · simpa only [safe, stateView, ready, Compact.Attachment.rearm] using valid
                  · simp [view, unaccepted, ready, stateView, moveView, Compact.Attachment.rearm,
                      BodyCall.WeightedSource.emitted, BodyCall.Move.rows, List.append_assoc]

/-- Reachability retains both independent source views and the actual quiet
finished invariant. No equation equating accepted grades to source is assumed. -/
def Captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call) : Prop :=
  Compact.Attachment.Captured construct callbackConstruct fallback (selection attachment) authored items parameter call ∧
    safe construct callbackConstruct fallback attachment call.2.2.computation.2 ∧
    view construct callbackConstruct fallback attachment call.2.2 =
      BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter

theorem open_captured (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Captured construct callbackConstruct fallback attachment authored items parameter
      (Compact.Attachment.openCall construct callbackConstruct fallback (selection attachment) authored items parameter ([], context)) := by
  refine ⟨Compact.Attachment.open_captured construct callbackConstruct fallback (selection attachment) authored items parameter ([], context), ?_, ?_⟩
  · constructor
    · change BodyCall.sourceReadings (BodyCall.openState authored items parameter (.observe .noAnswers)).work
      simp [BodyCall.openState, BodyCall.sourceReadings_cons, BodyCall.Cursor.sourceReading, openFrontier]
    · rfl
  · exact BodyCall.WeightedSource.open_rows construct callbackConstruct attachment authored items parameter

theorem resume_captured (quantum allowance : Nat) (accept : Context → Returned → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (previous : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter previous) :
    Captured construct callbackConstruct fallback attachment authored items parameter
      (Compact.Attachment.resumeCallSource construct callbackConstruct fallback (selection attachment)
        quantum allowance (reader construct callbackConstruct fallback attachment accept) previous) := by
  refine ⟨Compact.Attachment.resume_captured construct callbackConstruct fallback (selection attachment)
    quantum allowance (reader construct callbackConstruct fallback attachment accept) authored items parameter previous valid.1, ?_⟩
  unfold Compact.Attachment.resumeCallSource resumeCall
  cases previous.2.1.terminal with
  | some reason => exact valid.2
  | none =>
      refine fromCallbacks_invariant (Compact.Attachment.ownedProvider construct callbackConstruct fallback (selection attachment)
        quantum (reader construct callbackConstruct fallback attachment accept)) (fun _ _ => 1)
        (fun (state : Owned) => safe construct callbackConstruct fallback attachment state.computation.2 ∧
          view construct callbackConstruct fallback attachment state =
            BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter)
        ?_ allowance previous.2.1.accepted previous.2.1.pending previous.2.2 valid.2 _
      intro state request invariant
      have kept := owned_step_view construct callbackConstruct fallback attachment quantum accept state request invariant.1
      exact ⟨kept.1, kept.2.trans invariant.2⟩

abbrev Grant := Nat × Nat × (Context → Returned → Bool × Context)

def readGrants (grants : List (Grant construct callbackConstruct fallback attachment (Context := Context))) :=
  grants.map (fun grant => (grant.1, grant.2.1, reader construct callbackConstruct fallback attachment grant.2.2))

theorem schedule_captured (grants : List (Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (previous : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter previous) :
    Captured construct callbackConstruct fallback attachment authored items parameter
      (Compact.Attachment.schedule construct callbackConstruct fallback (selection attachment)
        (readGrants construct callbackConstruct fallback attachment grants) previous) := by
  induction grants generalizing previous with
  | nil => exact valid
  | cons grant rest ih => exact ih _ (resume_captured construct callbackConstruct fallback attachment grant.1 grant.2.1
      grant.2.2 authored items parameter previous valid)

/-- Only an actual acknowledged finished cut exposes the completed weighted
answers. It preserves the whole retained call and its captured source world. -/
def readout (call : Call) : Option (List (BodyCall.WeightedSource.Row Output Weight)) × Call :=
  ((if Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call then
    some call.2.2.context.2.1 else none), call)

theorem completed_source (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call = true) :
    call.2.2.context.2.1 = BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter := by
  have cut := BodyCallAdmission.complete_cut construct callbackConstruct fallback
    (Compact.Attachment.eraseCall construct callbackConstruct fallback (selection attachment) call) finished
  simp only [Compact.Attachment.eraseCall, forget_state, forget_move] at cut
  have quiet := valid.1.2.1
  change BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) call.2.2.computation.2)) at quiet
  rw [forget_state] at quiet
  have erased := BodyCall.WeightedSource.workRows_erase construct callbackConstruct attachment
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).core.work
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).branches valid.2.1.2
  have empty : residual construct callbackConstruct attachment
      (stateView construct callbackConstruct fallback attachment call.2.2.computation.2) = [] :=
    List.map_eq_nil_iff.mp (erased.trans (quiet cut.1))
  simpa only [view, unaccepted, BodyCall.WeightedSource.emitted, cut.2, List.map_nil, List.nil_append,
    empty, List.append_nil] using valid.2.2

theorem schedule_open_completed (grants : List (Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment)
      (Compact.Attachment.schedule construct callbackConstruct fallback (selection attachment)
        (readGrants construct callbackConstruct fallback attachment grants)
        (Compact.Attachment.openCall construct callbackConstruct fallback (selection attachment) authored items parameter ([], context))) = true) :
    (Compact.Attachment.schedule construct callbackConstruct fallback (selection attachment)
      (readGrants construct callbackConstruct fallback attachment grants)
      (Compact.Attachment.openCall construct callbackConstruct fallback (selection attachment) authored items parameter ([], context))).2.2.context.2.1 =
        BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter :=
  completed_source construct callbackConstruct fallback attachment authored items parameter _
    (schedule_captured construct callbackConstruct fallback attachment grants authored items parameter _
      (open_captured construct callbackConstruct fallback attachment authored items parameter context)) finished

/-- Existing source-inferred conventions license weighted result readout.
The gate examines completion and the existing selected-worker convention. -/
def admit (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call) :
    Option (List (BodyCall.WeightedSource.Row Output Weight)) × Call :=
  ((if Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call &&
    BodyCallAdmission.modeEligible requested (BodyCallAdmission.workerMode (selectWorker authored items parameter interface)) interface then
      some call.2.2.context.2.1 else none), call)

theorem admit_license (requested : CallingConvention) (interface : ScalarResultInterface)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (answers : List (BodyCall.WeightedSource.Row Output Weight))
    (admitted : (admit construct callbackConstruct fallback attachment requested interface authored items parameter call).1 = some answers) :
    answers = BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter ∧
      ConventionAllows requested answers.length := by
  unfold admit at admitted
  split at admitted
  next allowed =>
    have gates := Bool.and_eq_true_iff.mp allowed
    have actual := completed_source construct callbackConstruct fallback attachment authored items parameter call valid gates.1
    have same := Option.some.inj admitted
    refine ⟨same.symm.trans actual, ?_⟩
    have mode := BodyCallAdmission.modeEligible_sound requested _ interface
      (source construct callbackConstruct authored items parameter).length gates.2
      (BodyCallAdmission.selected_mode_sound construct callbackConstruct authored items parameter interface)
    have counts := congrArg List.length (BodyCall.WeightedSource.source_erase construct callbackConstruct attachment authored items parameter)
    simp only [List.length_map] at counts
    rw [← actual, same] at counts
    simpa only [← counts] using mode
  next refused => cases admitted

/-- Ordered coefficient-word equality yields the semiring readout without
commutativity. Zero-valued rows remain in this list. -/
theorem completed_denote (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (valid : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call = true) :
    call.2.2.context.2.1.map (fun row => (row.1, row.2.prod)) =
      (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
        (fun row => (row.1, row.2.prod)) :=
  congrArg (List.map (fun row : BodyCall.WeightedSource.Row Output Weight => (row.1, row.2.prod)))
    (completed_source construct callbackConstruct fallback attachment authored items parameter call valid finished)

theorem origin_aligned (outcome : Outcome)
    (origin : Compact.Attachment.Origin construct callbackConstruct fallback (selection attachment) outcome) :
    (stateView construct callbackConstruct fallback attachment outcome).branches.length =
      (stateView construct callbackConstruct fallback attachment outcome).core.work.length := by
  obtain ⟨reference, same⟩ := origin
  rw [← same]
  cases reference with
  | paused packet =>
      change (packet.2.2.val.val.branches.map
        (BodyCall.Graded.Compact.Attachment.selected (selection attachment))).length = packet.2.2.val.val.core.work.length
      simpa only [List.length_map, BodyCall.Graded.Aligned] using packet.2.2.val.property.2.2
  | done returned =>
      change (returned.2.2.val.val.branches.map
        (BodyCall.Graded.Compact.Attachment.selected (selection attachment))).length = returned.2.2.val.val.core.work.length
      simpa only [List.length_map, BodyCall.Graded.Aligned] using returned.2.2.val.property.2.2

theorem completed_unaccepted
    (call : Compact.Attachment.Call construct callbackConstruct fallback (selection attachment) (Context := Context))
    (quiet : Compact.Attachment.quiet construct callbackConstruct fallback (selection attachment) call.2.2)
    (aligned : (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).branches.length =
      (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).core.work.length)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback (selection attachment) call = true) :
    unaccepted construct callbackConstruct fallback attachment call.2.2.computation.2 = [] := by
  have cut := BodyCallAdmission.complete_cut construct callbackConstruct fallback
    (Compact.Attachment.eraseCall construct callbackConstruct fallback (selection attachment) call) finished
  simp only [Compact.Attachment.eraseCall, forget_state, forget_move] at cut
  change BodyCallProtocol.finishedQuiet construct callbackConstruct
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (Compact.Attachment.forget construct callbackConstruct fallback (selection attachment) call.2.2.computation.2)) at quiet
  rw [forget_state] at quiet
  have erased := BodyCall.WeightedSource.workRows_erase construct callbackConstruct attachment
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).core.work
    (stateView construct callbackConstruct fallback attachment call.2.2.computation.2).branches aligned
  have empty : residual construct callbackConstruct attachment
      (stateView construct callbackConstruct fallback attachment call.2.2.computation.2) = [] :=
    List.map_eq_nil_iff.mp (erased.trans (quiet cut.1))
  simp only [unaccepted, BodyCall.WeightedSource.emitted, cut.2, List.map_nil, List.nil_append, empty]

#print axioms origin_aligned
#print axioms completed_unaccepted

#print axioms owned_step_view
#print axioms open_captured
#print axioms resume_captured
#print axioms schedule_captured
#print axioms completed_source
#print axioms schedule_open_completed
#print axioms admit_license
#print axioms completed_denote

#print axioms selection_values
#print axioms advance_view
#print axioms resume_view
#print axioms run_open_source

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)

abbrev SourceAttachment := BodyCall.WeightedSource.Attachment Nat Nat Nat

def branches : SourceAttachment := fun ordinal _ _ _ =>
  some (if ordinal = 0 then 2 else if ordinal = 1 then 11 else if ordinal = 2 then 3 else 5)

def cartesian : SourceAttachment := fun ordinal _ _ _ =>
  some (if ordinal = 0 then 2 else if ordinal = 1 then 3 else 5)

def accepted (attachment : SourceAttachment)
    (program : List (Equation Nat)) (items : List Nat) :=
  Compact.Attachment.resumeCallSource build callback noFallback (selection attachment) 64 32
    (reader build callback noFallback attachment (fun (_ : Unit) _ => (true, ())))
    (Compact.Attachment.openCall build callback noFallback (selection attachment) program items 0 ([], ()))

def equalBranches := accepted branches BodyCallShared.Weighted.Controls.authored [0]

/-- The independently authored meaning and actual completed callback agree;
failed and alternative firings cannot become a global branch multiplier. -/
theorem duplicate_answers_exclude_failed_and_sibling_factors :
    equalBranches.2.2.context.2.1 = [([7], [2, 3]), ([7], [2, 5])] ∧
      BodyCall.WeightedSource.source build callback branches BodyCallShared.Weighted.Controls.authored [0] 0 =
        [([7], [2, 3]), ([7], [2, 5])] ∧
      Compact.Attachment.complete build callback noFallback (selection branches) equalBranches = true ∧
      (stateView build callback noFallback branches equalBranches.2.2.computation.2).nextOrdinal = 4 ∧
      equalBranches.2.2.context.2.1 ≠ [([7], [2, 11, 3, 5]), ([7], [2, 11, 3, 5])] := by decide

def recursive := accepted cartesian BodyCallWeighted.Controls.cartesian [0]

/-- Left and right recursive calls contribute in authored Cartesian order.
The retained result rejects a permuted factor word even when scalar products coincide. -/
theorem recursive_cartesian_order_is_not_a_commutative_reordering :
    recursive.2.2.context.2.1 =
      [([18, 7], [2, 3, 3]), ([18, 7], [2, 3, 5]), ([18, 7], [2, 5, 3]), ([18, 7], [2, 5, 5])] ∧
      BodyCall.WeightedSource.source build callback cartesian BodyCallWeighted.Controls.cartesian [0] 0 =
        recursive.2.2.context.2.1 ∧
      recursive.2.2.context.2.1 ≠
        [([18, 7], [3, 2, 3]), ([18, 7], [3, 2, 5]), ([18, 7], [5, 2, 3]), ([18, 7], [5, 2, 5])] := by decide

def zero : SourceAttachment := fun _ _ _ _ => some 0
def sparse : SourceAttachment := fun ordinal _ _ _ => if ordinal = 0 then none else some 1

def equalProgram : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def zeroResult := accepted zero BodyCallRun.blank []
def sparseResult := accepted sparse equalProgram []

theorem zero_unit_and_absence_preserve_distinct_occurrences :
    zeroResult.2.2.context.2.1 = [([], [0])] ∧
      Compact.Attachment.complete build callback noFallback (selection zero) zeroResult = true ∧
      sparseResult.2.2.context.2.1 = [([7], []), ([7], [1])] ∧
      sparseResult.2.2.context.2.1.map (fun row => (row.1, row.2.prod)) = [([7], 1), ([7], 1)] ∧
      (admit build callback noFallback zero .direct .singleValue BodyCallRun.blank [] 0 zeroResult).1 = some [([], [0])] ∧
      (admit build callback noFallback sparse .direct .singleValue equalProgram [] 0 sparseResult).1 = none := by decide

def committedFailure : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .mapHead (.singleton 9)⟩, ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def committedResult := accepted branches committedFailure []

theorem committed_failure_is_completed_empty_not_zero_weight_success :
    committedResult.2.2.context.2.1 = [] ∧
      BodyCall.WeightedSource.source build callback branches committedFailure [] 0 = [] ∧
      Compact.Attachment.complete build callback noFallback (selection branches) committedResult = true ∧
      (stateView build callback noFallback branches committedResult.2.2.computation.2).nextOrdinal = 1 ∧
      zeroResult.2.2.context.2.1 ≠ committedResult.2.2.context.2.1 := by decide

def warming (ready : Bool) (_ : Compact.Attachment.SparseReturned build callback noFallback (selection branches)) :=
  (ready, true)

def refused := Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 64 1
  (reader build callback noFallback branches warming)
  (Compact.Attachment.openCall build callback noFallback (selection branches)
    BodyCallShared.Weighted.Controls.authored [0] 0 ([], false))

def retried := Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 0 1
  (reader build callback noFallback branches warming) refused

def completed := Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 64 8
  (reader build callback noFallback branches warming) retried

theorem stateful_refusal_and_zero_source_retry_preserve_the_weighted_loan :
    refused.2.1.pending.isSome = true ∧ refused.2.2.context.2 = ([], true) ∧
      (readout build callback noFallback branches refused).1 = none ∧
      retried.2.2.context.2 = ([([7], [2, 3])], true) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 0 0
        (reader build callback noFallback branches warming) refused = refused ∧
      completed.2.2.context.2.1 = [([7], [2, 3]), ([7], [2, 5])] ∧
      (readout build callback noFallback branches completed).1 = some [([7], [2, 3]), ([7], [2, 5])] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
  exact resumeCall_zero _ _ _ _

#print axioms duplicate_answers_exclude_failed_and_sibling_factors
#print axioms recursive_cartesian_order_is_not_a_commutative_reordering
#print axioms zero_unit_and_absence_preserve_distinct_occurrences
#print axioms committed_failure_is_completed_empty_not_zero_weight_success
#print axioms stateful_refusal_and_zero_source_retry_preserve_the_weighted_loan

end Controls

end BodyCallWeighted.Authored

/-! The shared weighted instance observes existing immutable branch images.
Its residual excludes a pending loan already exposed to the occurrence log;
acknowledgment therefore cannot mint another semantic occurrence. -/
namespace BodyCallShared.Weighted.Authored

open Mettapedia.Algebra.SharedCoefficientLedger
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

local notation "selected" => BodyCallWeighted.Authored.selection attachment
local notation "Call" => Weighted.Call construct callbackConstruct fallback selected (Context := Context)
local notation "Borrowed" => Weighted.Borrowed construct callbackConstruct fallback selected
local notation "Source" => BodyCallWeighted.Authored.stateView construct callbackConstruct fallback attachment
local notation "View" => BodyCallWeighted.Authored.unaccepted construct callbackConstruct fallback attachment

def loanRows (borrowed : Borrowed) :=
  BodyCall.WeightedSource.emitted borrowed.2.2.1 borrowed.2.2.2.val.loan

def storedRows (stored : Weighted.Stored (Output := Output) (Weight := Weight)) :=
  stored.2.1.map (fun row => (row, stored.2.2.map (·.coefficient)))

theorem capture_rows (borrowed : Borrowed) :
    storedRows (Weighted.image construct callbackConstruct fallback selected borrowed) =
      loanRows construct callbackConstruct fallback attachment borrowed := by
  simp [storedRows, Weighted.image, Weighted.projectLedger, BodyCall.WeightedSource.emitted,
    loanRows, List.map_map, Function.comp_def, Factor.rename]

def residual (call : Call) :=
  match call.2.1.pending with
  | some _ => BodyCallWeighted.Authored.residual construct callbackConstruct attachment (Source call.2.2.computation.2)
  | none => View call.2.2.computation.2

theorem inspect_rows (call : Call) (coherent : Weighted.Coherent construct callbackConstruct fallback selected call) :
    (Weighted.inspect construct callbackConstruct fallback selected call).returns.flatMap
        (loanRows construct callbackConstruct fallback attachment) ++ residual construct callbackConstruct fallback attachment call =
      View call.2.2.computation.2 := by
  rw [Weighted.inspect_returns construct callbackConstruct fallback selected call coherent]
  cases pending : call.2.1.pending with
  | none => simp [pending, residual]
  | some loan =>
      have held := coherent loan pending
      simp [pending, residual, loanRows, BodyCallWeighted.Authored.unaccepted,
        held.2.1, BodyCallWeighted.Authored.moveView, BodyCallWeighted.Authored.stateView]

theorem acknowledge_rows (call : Call) (coherent : Weighted.Coherent construct callbackConstruct fallback selected call)
    (loan : Weighted.Loan construct callbackConstruct fallback selected) (pending : call.2.1.pending = some loan) :
    residual construct callbackConstruct fallback attachment
        (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selected 0 1
          (Weighted.accept construct callbackConstruct fallback selected) call) =
      residual construct callbackConstruct fallback attachment call := by
  have held := coherent loan pending
  cases final : BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selected loan <;>
    simp [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, held.1, pending, fromCallbacks,
      BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, held.2.1, held.2.2,
      BodyCallWeighted.Compact.Attachment.consume, Weighted.accept, final, residual,
      BodyCallWeighted.Authored.unaccepted, BodyCallWeighted.Authored.stateView,
      BodyCallWeighted.Authored.moveView, BodyCallWeighted.Compact.Attachment.rearm,
      BodyCall.WeightedSource.emitted, BodyCall.Move.rows]

private theorem poll_view (quantum : Nat) (call : Call)
    (running : call.2.1.terminal = none) (empty : call.2.1.pending = none)
    (safe : BodyCallWeighted.Authored.safe construct callbackConstruct fallback attachment call.2.2.computation.2) :
    View (BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selected quantum 1
      (Weighted.refuse construct callbackConstruct fallback selected) call).2.2.computation.2 =
        View call.2.2.computation.2 := by
  have preserved := (BodyCallWeighted.Authored.resume_view construct callbackConstruct fallback attachment quantum call.2.2.computation safe).1
  cases outcome : (Cursor.resume (BodyCallWeighted.Compact.Attachment.SparseProvider construct callbackConstruct fallback selected)
    BodyCallProtocol.client (fun _ _ => 1) quantum call.2.2.computation).2 with
  | paused saved =>
      simpa [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty,
        fromCallbacks, BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome] using preserved
  | done returned =>
      cases produced : BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selected returned <;>
        simpa [BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall, running, empty,
          fromCallbacks, BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider, outcome,
          produced, BodyCallWeighted.Compact.Attachment.consume, Weighted.refuse] using preserved

variable {size : Nat} (before : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)

theorem safe_view (items : List Input) (parameter : Nat) (call : Call)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter call) :
    BodyCallWeighted.Authored.safe construct callbackConstruct fallback attachment call.2.2.computation.2 := by
  refine ⟨?_, BodyCallWeighted.Authored.origin_aligned construct callbackConstruct fallback attachment _ safe.2.1⟩
  have readings := safe.1.1.2
  change BodyCall.sourceReadings
    (BodyCallProtocol.stateView construct callbackConstruct fallback
      (BodyCallWeighted.Compact.Attachment.forget construct callbackConstruct fallback selected call.2.2.computation.2)).work at readings
  rw [BodyCallWeighted.Authored.forget_state] at readings
  exact readings

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (current : OrderedDependencyStore.Store (Equation Output) size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)] (quantum : Nat)
local notation "sourceStep" => Weighted.step construct callbackConstruct fallback selected authority before current reader point required quantum

set_option backward.isDefEq.respectTransparency false in
theorem step_rows (items : List Input) (parameter : Nat) (call : Call)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter call) :
    (sourceStep call).returns.flatMap (loanRows construct callbackConstruct fallback attachment) ++
        residual construct callbackConstruct fallback attachment (sourceStep call).next =
      residual construct callbackConstruct fallback attachment call := by
  unfold Weighted.step BodyCallShared.retainedStep
  split
  · have noLoan : call.2.1.pending = none := by
      cases pending : call.2.1.pending with
      | none => rfl
      | some loan => simp [(safe.2.2 loan pending).1] at ‹call.2.1.terminal.isSome = true›
    rw [Weighted.inspect_next, Weighted.inspect_returns construct callbackConstruct fallback selected call safe.2.2]
    simp [noLoan]
  · cases pending : call.2.1.pending with
    | some loan =>
        exact acknowledge_rows construct callbackConstruct fallback attachment call safe.2.2 loan pending
    | none =>
        dsimp only
        have running : call.2.1.terminal = none := by simpa using ‹¬call.2.1.terminal.isSome = true›
        have kept := Weighted.poll_safe construct callbackConstruct fallback selected authority before current reader point required quantum
          items parameter call safe running pending
        rw [Weighted.inspect_next]
        have observed := inspect_rows construct callbackConstruct fallback attachment
          (Weighted.poll construct callbackConstruct fallback selected authority before current reader point required quantum call) kept.2.2
        rw [observed]
        by_cases fresh : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp before reader) = true
        · by_cases permitted : FrameUpdate point.authority required
          · simpa only [Weighted.poll, fresh, permitted, ↓reduceIte, residual, pending] using
              poll_view construct callbackConstruct fallback attachment quantum call running pending
                (safe_view construct callbackConstruct fallback attachment before reader items parameter call safe)
          · simp [Weighted.poll, fresh, permitted, residual, pending]
        · simp [Weighted.poll, fresh, residual, pending]

/-- Existing actual producer paths telescope the ordered loan/residual law;
no schedule-independent trace or factor identity is invented. -/
theorem path_rows (items : List Input) (parameter : Nat)
    {first last : Call} {returns : List Borrowed}
    (path : Cursor.ProducerOccurrenceLog.ProducerPath sourceStep first returns last)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter first) :
    returns.flatMap (loanRows construct callbackConstruct fallback attachment) ++
        residual construct callbackConstruct fallback attachment last =
      residual construct callbackConstruct fallback attachment first := by
  induction path with
  | refl => rfl
  | @next first move later returns transition tail ih =>
      have kept := Weighted.step_safe construct callbackConstruct fallback selected authority before current reader point required quantum
        items parameter first safe
      have one := step_rows construct callbackConstruct fallback attachment before reader authority current point required quantum items parameter first safe
      rw [transition] at kept one
      rw [List.flatMap_append, List.append_assoc, ih kept, one]

variable {Owner : Type} {clients : Nat}
local notation "Cfg" => Weighted.Configuration construct callbackConstruct fallback selected
  (Context := Context) (size := size) Owner clients
local notation "sourceCapture" => Weighted.capture construct callbackConstruct fallback selected
local notation "Execution" => Cursor.ProducerOccurrenceLog.Execution Call Borrowed Empty
  (Weighted.Loan construct callbackConstruct fallback selected)

def view (state : Cfg) (call : Call) :=
  state.delivery.log.rows.flatMap (storedRows (Output := Output) (Weight := Weight)) ++
    (Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (loanRows construct callbackConstruct fallback attachment) ++
      residual construct callbackConstruct fallback attachment call

set_option backward.isDefEq.respectTransparency false in
theorem pump_view (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg) (execution target : Execution)
    (attached : state.execution = some execution)
    (nextAttached : (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2.execution = some target)
    (safe : Weighted.Safe construct callbackConstruct fallback selected before reader items parameter execution.producer) :
    view construct callbackConstruct fallback attachment
        (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2 target.producer =
      view construct callbackConstruct fallback attachment state execution.producer := by
  obtain ⟨actual, retained, path⟩ := Cursor.ProducerOccurrenceLog.pump_producer_path sourceStep sourceCapture capacity (fun _ => true) state execution attached
  have same : actual = target := Option.some.inj (retained.symm.trans nextAttached)
  subst actual
  have row := path_rows construct callbackConstruct fallback attachment before reader authority current point required quantum
    items parameter path safe
  have conserved := Cursor.ProducerOccurrenceLog.pump_conservation
    (loanRows construct callbackConstruct fallback attachment) (storedRows (Output := Output) (Weight := Weight))
    sourceStep sourceCapture capacity (fun _ => true)
    (by intro loan stored captured; cases captured; exact capture_rows construct callbackConstruct fallback attachment loan) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  unfold view
  rw [Cursor.ProducerOccurrenceLog.pump_rows, List.flatMap_append]
  calc
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((Cursor.ProducerOccurrenceLog.admitted (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap storedRows ++
          (Cursor.ProducerOccurrenceLog.pending (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).2).toList.flatMap
            (loanRows construct callbackConstruct fallback attachment)) ++
          residual construct callbackConstruct fallback attachment target.producer := by simp only [List.append_assoc]
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((Cursor.ProducerOccurrenceLog.pending state).toList.flatMap (loanRows construct callbackConstruct fallback attachment) ++
          (Cursor.ProducerOccurrenceLog.returned (Cursor.ProducerOccurrenceLog.pump sourceStep sourceCapture capacity (fun _ => true) state).1).flatMap
            (loanRows construct callbackConstruct fallback attachment)) ++
          residual construct callbackConstruct fallback attachment target.producer := by rw [← flat]
    _ = _ := by simp only [List.append_assoc]; rw [row]

private theorem delivery_view [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (state : Cfg) (execution : Execution) (client : Fin clients) (owner : Owner) :
    view construct callbackConstruct fallback attachment (Cursor.ProducerOccurrenceLog.deliver (fun _ => true) state client owner).2 execution.producer =
      view construct callbackConstruct fallback attachment state execution.producer := by
  simp only [view, Weighted.delivery_rows, Cursor.ProducerOccurrenceLog.pending,
    Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution]

private theorem actions_view [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (state : Cfg)
    (accounted : Weighted.Accounted construct callbackConstruct fallback selected before reader items parameter state)
    (conserved : ∀ execution, state.execution = some execution →
      view construct callbackConstruct fallback attachment state execution.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter) :
    ∀ execution, (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state).execution = some execution →
      view construct callbackConstruct fallback attachment
        (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions state) execution.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  induction actions generalizing state with
  | nil => exact conserved
  | cons action rest ih =>
      cases action with
      | pump =>
          apply ih _ (Weighted.pump_accounted construct callbackConstruct fallback selected authority before current reader point required quantum capacity
            items parameter state accounted)
          intro target attachedTarget
          obtain ⟨⟨execution, attached, safe⟩, _, _⟩ := accounted
          exact (pump_view construct callbackConstruct fallback attachment before reader authority current point required quantum capacity
            items parameter state execution target attached attachedTarget safe).trans (conserved execution attached)
      | deliver client owner =>
          apply ih _ (Weighted.delivery_accounted construct callbackConstruct fallback selected before reader items parameter state accounted client owner)
          intro execution attached
          exact (delivery_view construct callbackConstruct fallback attachment state execution client owner).trans
            (conserved execution (by simpa only [Cursor.ProducerOccurrenceLog.delivery_preserves_complete_execution] using attached))

/-- Arbitrary actual shared pump/delivery actions preserve the independent
weighted source partition in existing stored rows, pending loan and residual. -/
theorem actions_open_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (context : Context) (limit : Nat) :
    let start := Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit
    let final := Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions start
    Weighted.Accounted construct callbackConstruct fallback selected before reader items parameter final ∧
      ∃ execution, final.execution = some execution ∧
        view construct callbackConstruct fallback attachment final execution.producer =
          BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  have startAccounted := Weighted.initial_accounted construct callbackConstruct fallback selected before reader items parameter context limit (Owner := Owner) (clients := clients)
  have finalAccounted := Weighted.actions_accounted construct callbackConstruct fallback selected authority before current reader point required quantum capacity actions
    items parameter _ startAccounted
  have initialView : ∀ execution, (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit).execution = some execution →
      view construct callbackConstruct fallback attachment
        (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit) execution.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
    intro execution attached
    cases attached
    exact BodyCall.WeightedSource.open_rows construct callbackConstruct attachment _ items parameter
  have finalView := actions_view construct callbackConstruct fallback attachment before reader authority current point required quantum capacity actions
    items parameter _ startAccounted initialView
  obtain ⟨execution, attached, _⟩ := finalAccounted.1
  exact ⟨finalAccounted, execution, attached, finalView execution attached⟩

/-- On an actually finished, acknowledged shared cut, stored branch images
alone equal the recursively weighted authored source. Delivery adds no factor. -/
theorem completed_log_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients))
    (items : List Input) (parameter : Nat) (context : Context) (limit : Nat)
    (execution : Execution)
    (attached : (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions
      (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit)).execution = some execution)
    (noLoan : Cursor.ProducerOccurrenceLog.pending
      (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions
        (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit)) = none)
    (finished : BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selected execution.producer = true) :
    (Cursor.ProducerOccurrenceLog.Accounting.runActions sourceStep sourceCapture capacity (fun _ => true) actions
      (Weighted.initial construct callbackConstruct fallback selected before reader items parameter context Owner clients limit)).delivery.log.rows.flatMap storedRows =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨accounted, actual, retained, conserved⟩ := actions_open_source construct callbackConstruct fallback attachment before reader authority current point required quantum
    capacity actions items parameter context limit (Owner := Owner) (clients := clients)
  have same : actual = execution := Option.some.inj (retained.symm.trans attached)
  subst actual
  obtain ⟨⟨actual, retained, safe⟩, _, _⟩ := accounted
  have same : actual = execution := Option.some.inj (retained.symm.trans attached)
  subst actual
  have noPending : execution.producer.2.1.pending = none := by
    cases pending : execution.producer.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallWeighted.Compact.Attachment.complete, BodyCallWeighted.Compact.Attachment.eraseCall,
        BodyCallAdmission.complete, pending] at finished
  have empty := BodyCallWeighted.Authored.completed_unaccepted construct callbackConstruct fallback attachment
    execution.producer safe.1.2.1 (safe_view construct callbackConstruct fallback attachment before reader items parameter execution.producer safe).2 finished
  simpa only [view, noLoan, Option.toList_none, List.flatMap_nil, List.append_nil, residual, noPending, empty] using conserved

#print axioms pump_view
#print axioms actions_open_source
#print axioms completed_log_source

#print axioms capture_rows
#print axioms inspect_rows
#print axioms acknowledge_rows
#print axioms safe_view
#print axioms step_rows
#print axioms path_rows

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)
open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallShared.Weighted.Controls
  (authored actualStep captureRow start pending captured acknowledged otherFinished)

abbrev sourceAttachment := BodyCallWeighted.Authored.Controls.branches

def expected := BodyCall.WeightedSource.source build callback sourceAttachment authored [0] 0

def actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Nat 2) := List.replicate 16 .pump

def produced := Cursor.ProducerOccurrenceLog.Accounting.runActions (actualStep 64) captureRow
  (fun _ => true) (fun _ => true) actions start

/-- Existing action execution, independent delivery and cancellation all retain
one captured semantic branch word, including the common outer occurrence. -/
theorem actual_shared_storage_and_cancellation_match_weighted_source :
    produced.delivery.log.rows.flatMap storedRows = expected ∧
      produced.delivery.log.completed = true ∧
      otherFinished.delivery.log.rows.flatMap storedRows = expected ∧
      expected = [([7], [2, 3]), ([7], [2, 5])] ∧
      produced.delivery.log.rows.map (fun row => identities row.2.2) = [[0, 2], [0, 3]] ∧
      expected ≠ [([7], [2, 2, 3]), ([7], [2, 2, 5])] := by decide

/-- Outer pending capture and the retained source loan describe the same row.
Capture, refusal and acknowledgment do not duplicate its weighted occurrence. -/
theorem pending_capture_and_acknowledgment_count_the_same_loan_once :
    pending.delivery.log.rows = [] ∧
      pending.execution.map (fun execution => view build callback noFallback sourceAttachment pending execution.producer) = some expected ∧
      captured.execution.map (fun execution => view build callback noFallback sourceAttachment captured execution.producer) = some expected ∧
      acknowledged.execution.map (fun execution => view build callback noFallback sourceAttachment acknowledged execution.producer) = some expected ∧
      captured.delivery.log.rows.flatMap storedRows = [([7], [2, 3])] ∧
      (Cursor.ProducerOccurrenceLog.pump (actualStep 64) captureRow (fun _ => false) (fun _ => true) pending).1 = .admissionRefused ∧
      pending.execution.map (fun execution => view build callback noFallback sourceAttachment pending execution.producer) ≠
        some [([7], [2, 3]), ([7], [2, 3]), ([7], [2, 5])] := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, by decide⟩

#print axioms actual_shared_storage_and_cancellation_match_weighted_source
#print axioms pending_capture_and_acknowledgment_count_the_same_loan_once

end Controls

end BodyCallShared.Weighted.Authored

namespace BodyCallShared.Handoff

open Cursor.ProducerOccurrenceLog
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Context Owner : Type} {clients size : Nat}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

local notation "Call" => BodyCallShared.Call construct callbackConstruct fallback (Context := Context)
local notation "Loan" => BodyCallShared.Loan construct callbackConstruct fallback
local notation "Borrowed" => BodyCallShared.Borrowed construct callbackConstruct fallback
local notation "Cfg" => BodyCallShared.Configuration construct callbackConstruct fallback
  (Context := Context) (size := size) Owner clients

private theorem callbacks_coherent (quantum : Nat)
    (consumer : Context → Loan → Bool × Context)
    (charges : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (allowance accepted : Nat) (held : Option Loan)
    (state : BodyCallOwned.State construct callbackConstruct fallback (Context := Context))
    (aligned : ∀ loan, held = some loan → state.computation.2 = .done loan ∧
      BodyCallOwned.isReturn construct callbackConstruct fallback loan = true) :
    BodyCallShared.Coherent construct callbackConstruct fallback
      (fromCallbacks (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer)
        charges allowance held accepted state (BodyCallOwned.terminalAfter construct callbackConstruct fallback)) := by
  simpa only [BodyCallShared.Coherent, BodyCallOwned.provider] using
    BodyCallShared.retainedCallbacks_coherent
      (BodyCallProtocol.provider construct callbackConstruct fallback)
      (BodyCallProtocol.requestCharge construct callbackConstruct fallback) quantum
      (BodyCallOwned.isReturn construct callbackConstruct fallback)
      (BodyCallOwned.rearm construct callbackConstruct fallback)
      (BodyCallOwned.consume construct callbackConstruct fallback consumer)
      (BodyCallOwned.terminalAfter construct callbackConstruct fallback)
      charges allowance accepted held state aligned

/-- Actual ordinary callback resumption constructs the loan-shape invariant;
it is not supplied as an equality with an expected answer stream. -/
theorem resume_coherent (quantum allowance : Nat)
    (consumer : Context → Loan → Bool × Context)
    (charges : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (call : Call) (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call) :
    BodyCallShared.Coherent construct callbackConstruct fallback
      (BodyCallAdmission.resume construct callbackConstruct fallback quantum allowance consumer charges call) := by
  unfold BodyCallAdmission.resume resumeCall
  cases stopped : call.2.1.terminal with
  | some reason => exact coherent
  | none =>
      simpa [BodyCallShared.Coherent] using
        callbacks_coherent construct callbackConstruct fallback quantum consumer charges allowance
          call.2.1.accepted call.2.1.pending call.2.2 (fun loan pending => (coherent loan pending).2)

theorem schedule_coherent
    (charges : ∀ quantum (consumer : Context → Loan → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    BodyCallShared.Coherent construct callbackConstruct fallback
      (BodyCallAdmission.schedule construct callbackConstruct fallback charges grants
        (BodyCallAdmission.openCall construct callbackConstruct fallback authored items parameter context)) := by
  have preserved : ∀ call : Call, BodyCallShared.Coherent construct callbackConstruct fallback call →
      BodyCallShared.Coherent construct callbackConstruct fallback
        (BodyCallAdmission.schedule construct callbackConstruct fallback charges grants call) := by
    induction grants with
    | nil => exact fun _ safe => safe
    | cons grant rest ih =>
        exact fun call safe => ih _ (resume_coherent construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
          (charges grant.1 grant.2.2) call safe)
  exact preserved _ (BodyCallShared.open_coherent construct callbackConstruct fallback authored items parameter context)

/-- Transfer the actual owned cut. Its held return is already issued, so it
enters the log's pending slot without invoking the source or its consumer.
Prior ordinary acknowledgments stay in the Call, outside the new reader log. -/
def adopt (world : OrderedDependencyStore.Store (Equation Output) size)
    (limit : Nat) (call : Call) : Cfg :=
  BodyCallShared.retainedAdopt world limit call

/-- Handback distinguishes a loan still awaiting capture from one already
captured by the shared log. The latter needs only its existing acknowledgment;
no source request is made. Buffered images retain their independent owners. -/
def release (state : Cfg) : Option Call × Cfg :=
  BodyCallShared.retainedRelease
    (BodyCallAdmission.resume construct callbackConstruct fallback 0 1
      (BodyCallShared.accept construct callbackConstruct fallback)
      (BodyCallShared.charge construct callbackConstruct fallback _ _)) state

theorem adopt_keeps_cut (world : OrderedDependencyStore.Store (Equation Output) size)
    (limit : Nat) (call : Call) :
    (adopt construct callbackConstruct fallback world limit call (Owner := Owner) (clients := clients)).execution =
      some ⟨call, call.2.1.pending.map (fun loan => (call.2.1.accepted, loan)), 0, .active⟩ ∧
      pending (adopt construct callbackConstruct fallback world limit call (Owner := Owner) (clients := clients)) =
        call.2.1.pending.map (fun loan => (call.2.1.accepted, loan)) := ⟨rfl, rfl⟩

theorem release_adopt (world : OrderedDependencyStore.Store (Equation Output) size)
    (limit : Nat) (call : Call) :
    (release construct callbackConstruct fallback
      (adopt construct callbackConstruct fallback world limit call (Owner := Owner) (clients := clients))).1 =
      some call := by
  cases held : call.2.1.pending <;> simp [release, adopt, BodyCallShared.retainedRelease, BodyCallShared.retainedAdopt, held]

theorem release_keeps_delivery (state : Cfg) :
    (release construct callbackConstruct fallback state).2.execution = none ∧
      (release construct callbackConstruct fallback state).2.context = state.context ∧
      (release construct callbackConstruct fallback state).2.delivery = state.delivery := ⟨rfl, rfl, rfl⟩

/-- Even after capture, handback keeps the exact source frontier and source
operation account. Only acknowledgment/context accounting may advance. -/
theorem release_keeps_source (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    ∃ call, (release construct callbackConstruct fallback state).1 = some call ∧
      call.2.2.computation.1 = execution.producer.2.2.computation.1 ∧
      BodyCallProtocol.stateView construct callbackConstruct fallback call.2.2.computation.2 =
        BodyCallProtocol.stateView construct callbackConstruct fallback execution.producer.2.2.computation.2 := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  next ready =>
    obtain ⟨loan, held⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp ready).2
    have shape := coherent loan held
    exact ⟨_, rfl, BodyCallAdmission.pending_resume_keeps_source construct callbackConstruct fallback 0
      (BodyCallShared.accept construct callbackConstruct fallback)
      (BodyCallShared.charge construct callbackConstruct fallback _ _) execution.producer loan shape.1 held⟩
  next waiting => exact ⟨_, rfl, rfl, rfl⟩

theorem release_captured (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback authored items parameter execution.producer) :
    ∃ call, (release construct callbackConstruct fallback state).1 = some call ∧
      BodyCallAdmission.captured construct callbackConstruct fallback authored items parameter call := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  · exact ⟨_, rfl, BodyCallAdmission.resume_captured construct callbackConstruct fallback 0 1
      (BodyCallShared.accept construct callbackConstruct fallback)
      (BodyCallShared.charge construct callbackConstruct fallback _ _) authored items parameter execution.producer safe⟩
  · exact ⟨_, rfl, safe⟩

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

/-- Current permission and the captured dependency stamp gate both new source
progress and publication from a buffer. This does not discharge authority. -/
def compatible (captured : OrderedDependencyStore.Store (Equation Output) size) : Bool :=
  OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp captured reader) &&
    decide (FrameUpdate point.authority required)

local notation "sourceStep" => BodyCallShared.step construct callbackConstruct fallback authority before current reader point required
local notation "sourceCapture" => BodyCallShared.capture construct callbackConstruct fallback
local notation "gate" => compatible authority current reader point required

/-- The same existing log engine performs all shared requests. Source quantum
and admission/delivery operations remain separate units. -/
def advance [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg) : Cfg :=
  Accounting.runActions (sourceStep quantum) sourceCapture capacity gate actions state

def view (state : Cfg) (call : Call) : List (List Output) :=
  state.delivery.log.rows.flatMap (·.2) ++
    (pending state).toList.flatMap (fun loan => loan.2.2.1.rows) ++
      BodyCallShared.residualRows construct callbackConstruct fallback call

theorem adopt_view (limit : Nat) (call : Call)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call) :
    call.2.2.context.1 ++ view construct callbackConstruct fallback
        (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients)) call =
      BodyCallOwned.view construct callbackConstruct fallback call.2.2 := by
  have partition := BodyCallShared.published_residual_eq_view construct callbackConstruct fallback call coherent
  cases held : call.2.1.pending <;>
    simpa [view, adopt, BodyCallShared.retainedAdopt, pending, Cursor.SharedOccurrenceLog.initial, BodyCallShared.publishedRows,
      held, List.append_assoc] using partition

private theorem path_residual (quantum : Nat) (items : List Input) (parameter : Nat)
    {first last : Call} {returns : List Borrowed}
    (path : ProducerPath (sourceStep quantum) first returns last)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter first)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback first) :
    returns.flatMap (fun loan => loan.2.2.1.rows) ++
        BodyCallShared.residualRows construct callbackConstruct fallback last =
      BodyCallShared.residualRows construct callbackConstruct fallback first := by
  obtain ⟨nextCoherent, rows⟩ := BodyCallShared.path_rows construct callbackConstruct fallback
    authority before current reader point required quantum path coherent
  have nextSafe := BodyCallShared.path_preserves_captured construct callbackConstruct fallback
    authority before current reader point required quantum items parameter path safe
  have initialView := BodyCallShared.published_residual_eq_view construct callbackConstruct fallback first coherent
  have finalView := BodyCallShared.published_residual_eq_view construct callbackConstruct fallback last nextCoherent
  rw [rows, List.append_assoc] at finalView
  apply List.append_cancel_left (as := BodyCallShared.publishedRows construct callbackConstruct fallback first)
  exact (finalView.trans nextSafe.2.2).trans (initialView.trans safe.2.2).symm

set_option backward.isDefEq.respectTransparency false in
theorem pump_view (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg)
    (execution target : Execution Call Borrowed Empty Loan)
    (attached : state.execution = some execution)
    (nextAttached : (pump (sourceStep quantum) sourceCapture capacity gate state).2.execution = some target)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    view construct callbackConstruct fallback
        (pump (sourceStep quantum) sourceCapture capacity gate state).2 target.producer =
      view construct callbackConstruct fallback state execution.producer := by
  obtain ⟨actual, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
  have same : actual = target := Option.some.inj (retained.symm.trans nextAttached)
  subst actual
  have row := path_residual construct callbackConstruct fallback authority before current reader point required quantum
    items parameter path safe coherent
  have conserved := pump_conservation (fun (loan : Borrowed) => loan.2.2.1.rows)
    (fun (stored : BodyCallShared.Stored (Output := Output)) => stored.2)
    (sourceStep quantum) sourceCapture capacity gate
    (by intro loan stored captured; cases captured; rfl) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  unfold view
  rw [pump_rows, List.flatMap_append]
  calc
    _ = state.delivery.log.rows.flatMap (·.2) ++
        ((admitted (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap (·.2) ++
          (pending (pump (sourceStep quantum) sourceCapture capacity gate state).2).toList.flatMap
            (fun loan => loan.2.2.1.rows)) ++ BodyCallShared.residualRows construct callbackConstruct fallback target.producer := by
          simp only [List.append_assoc]
    _ = state.delivery.log.rows.flatMap (·.2) ++
        ((pending state).toList.flatMap (fun loan => loan.2.2.1.rows) ++
          (returned (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap
            (fun loan => loan.2.2.1.rows)) ++ BodyCallShared.residualRows construct callbackConstruct fallback target.producer := by rw [← flat]
    _ = _ := by simp only [List.append_assoc]; rw [row]

private theorem delivery_view [DecidableEq Output] [DecidableEq Owner]
    (state : Cfg) (call : Call) (client : Fin clients) (owner : Owner) :
    view construct callbackConstruct fallback (deliver gate state client owner).2 call =
      view construct callbackConstruct fallback state call := by
  have rows : (deliver gate state client owner).2.delivery.log.rows = state.delivery.log.rows := by
    unfold deliver
    split
    · cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
        simp [Cursor.SharedOccurrenceOwnership.advance, Cursor.SharedOccurrenceOwnership.acknowledge,
          Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceLog.pull,
          Cursor.SharedOccurrenceLog.setPosition, reply]
    · rfl
  simp only [view, rows, pending, delivery_preserves_complete_execution]

/-- Arbitrary finite shared requests preserve the actual source, loan shape
and exact ordered suffix partition, including refusals and delivery retries. -/
theorem advance_source [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    ∃ target, (advance construct callbackConstruct fallback authority before current reader point required
        quantum capacity actions state).execution = some target ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      BodyCallShared.Coherent construct callbackConstruct fallback target.producer ∧
      view construct callbackConstruct fallback
          (advance construct callbackConstruct fallback authority before current reader point required
            quantum capacity actions state) target.producer =
        view construct callbackConstruct fallback state execution.producer := by
  induction actions generalizing state execution with
  | nil => exact ⟨execution, attached, safe, coherent, rfl⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨next, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
          have safeNext := BodyCallShared.path_preserves_captured construct callbackConstruct fallback authority
            before current reader point required quantum items parameter path safe
          have coherentNext := (BodyCallShared.path_rows construct callbackConstruct fallback authority
            before current reader point required quantum path coherent).1
          obtain ⟨target, final, safeFinal, coherentFinal, same⟩ := ih _ next retained safeNext coherentNext
          exact ⟨target, final, safeFinal, coherentFinal, same.trans
            (pump_view construct callbackConstruct fallback authority before current reader point required quantum capacity
              items parameter state execution next attached retained safe coherent)⟩
      | deliver client owner =>
          have retained := (delivery_preserves_complete_execution gate state client owner).trans attached
          obtain ⟨target, final, safeFinal, coherentFinal, same⟩ := ih _ execution retained safe coherent
          exact ⟨target, final, safeFinal, coherentFinal, same.trans
            (delivery_view construct callbackConstruct fallback authority current reader point required state execution.producer client owner)⟩

/-- An ordinary owned prefix is kept outside the new multicast log. The actual
pending loan and future residual enter exactly once at this nonfresh cut. -/
theorem adopt_advance_source [DecidableEq Output] [DecidableEq Owner]
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (call : Call)
    (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter call)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call) :
    let final := advance construct callbackConstruct fallback authority before current reader point required
      quantum capacity actions (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))
    ∃ target, final.execution = some target ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      BodyCallShared.Coherent construct callbackConstruct fallback target.producer ∧
      call.2.2.context.1 ++ view construct callbackConstruct fallback final target.producer =
        source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨target, attached, safeFinal, coherentFinal, same⟩ := advance_source construct callbackConstruct fallback
    authority before current reader point required quantum capacity actions
    (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients)) _ rfl
    items parameter safe coherent
  refine ⟨target, attached, safeFinal, coherentFinal, ?_⟩
  rw [same, adopt_view construct callbackConstruct fallback before limit call coherent]
  exact safe.2.2

/-- The handback readout uses the independently proved source invariant. It
retains the full Call, and all four modes use their existing grade licenses. -/
theorem advance_release_license [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter execution.producer)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback execution.producer) :
    ∃ call, (release construct callbackConstruct fallback
        (advance construct callbackConstruct fallback authority before current reader point required
          quantum capacity actions state)).1 = some call ∧
      ∃ earned : BodyCallAdmission.quiet construct callbackConstruct fallback call.2.2,
        ∀ requested interface answers,
          (BodyCallAdmission.admit construct callbackConstruct fallback requested interface
            (OrderedDependencyStore.query before reader) items parameter call earned).1 = some answers →
          answers = source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter ∧
            ConventionAllows requested answers.length := by
  obtain ⟨target, final, safeFinal, _, _⟩ := advance_source construct callbackConstruct fallback
    authority before current reader point required quantum capacity actions state execution attached items parameter safe coherent
  obtain ⟨call, handedBack, safeBack⟩ := release_captured construct callbackConstruct fallback _ target final
    (OrderedDependencyStore.query before reader) items parameter safeFinal
  exact ⟨call, handedBack, safeBack.2.1, fun requested interface answers admitted =>
    BodyCallAdmission.admit_license construct callbackConstruct fallback requested interface _ items parameter call
      safeBack.2.1 safeBack.2.2 answers admitted⟩

/-- Splitting keeps the same source quantum, captured/current context and
permission. It does not combine grants across external context changes. -/
theorem advance_split [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (first second : List (Accounting.Action Owner clients)) (state : Cfg) :
    advance construct callbackConstruct fallback authority before current reader point required quantum capacity (first ++ second) state =
      advance construct callbackConstruct fallback authority before current reader point required quantum capacity second
        (advance construct callbackConstruct fallback authority before current reader point required quantum capacity first state) :=
  Accounting.runActions_append _ _ _ _ _ _ _

theorem denied_keeps_cut [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (state : Cfg) (client : Fin clients) (owner : Owner)
    (denied : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp state.context reader) = false ∨
      ¬ FrameUpdate point.authority required) :
    pump (sourceStep quantum) sourceCapture capacity gate state =
        (if state.execution.isNone then .detached else .contextRefused, state) ∧
      deliver gate state client owner = (.contextRefused, state) := by
  have no : gate state.context = false := by
    rcases denied with stale | revoked <;> simp [compatible, *]
  constructor
  · cases attached : state.execution <;> simp [pump, attached, no]
  · simp [deliver, no]

/-- The entry invariant is constructed from actual ordinary resumptions,
then transported through the shared engine from their exact retained cut. -/
theorem scheduled_handoff_source [DecidableEq Output] [DecidableEq Owner]
    (charges : ∀ quantum (consumer : Context → Loan → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallAdmission.schedule construct callbackConstruct fallback charges grants
      (BodyCallAdmission.openCall construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter context)
    let final := advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit owned (Owner := Owner) (clients := clients))
    ∃ target, final.execution = some target ∧
      BodyCallAdmission.captured construct callbackConstruct fallback
        (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      BodyCallShared.Coherent construct callbackConstruct fallback target.producer ∧
      owned.2.2.context.1 ++ view construct callbackConstruct fallback final target.producer =
        source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  exact adopt_advance_source construct callbackConstruct fallback authority before current reader point required quantum limit capacity
    actions _ items parameter
    (BodyCallAdmission.schedule_open_captured construct callbackConstruct fallback charges grants _ items parameter context)
    (schedule_coherent construct callbackConstruct fallback charges grants _ items parameter context)

theorem completed_residual (call : Call)
    (earned : BodyCallAdmission.quiet construct callbackConstruct fallback call.2.2)
    (completed : BodyCallAdmission.complete construct callbackConstruct fallback call = true) :
    BodyCallShared.residualRows construct callbackConstruct fallback call = [] := by
  obtain ⟨finished, empty⟩ := BodyCallAdmission.complete_cut construct callbackConstruct fallback call completed
  have noLoan : call.2.1.pending = none := by
    cases held : call.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallAdmission.complete, held] at completed
  simp [BodyCallShared.residualRows, noLoan, BodyCallProtocol.unacceptedRows, empty, earned finished]

/-- A completed acknowledged shared suffix combines with the earlier ordinary
prefix, preserving multiplicity. The multicast log alone need not be the whole
source when adoption happened after earlier ordinary acknowledgments. -/
theorem completed_handoff_source [DecidableEq Output] [DecidableEq Owner]
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (call : Call) (items : List Input) (parameter : Nat)
    (safe : BodyCallAdmission.captured construct callbackConstruct fallback
      (OrderedDependencyStore.query before reader) items parameter call)
    (coherent : BodyCallShared.Coherent construct callbackConstruct fallback call)
    (target : Execution Call Borrowed Empty Loan)
    (attached : (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))).execution = some target)
    (noLoan : pending (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))) = none)
    (completed : BodyCallAdmission.complete construct callbackConstruct fallback target.producer = true) :
    call.2.2.context.1 ++ (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit call (Owner := Owner) (clients := clients))).delivery.log.rows.flatMap (·.2) =
      source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter := by
  obtain ⟨actual, retained, safeFinal, _, partition⟩ := adopt_advance_source construct callbackConstruct fallback
    authority before current reader point required quantum limit capacity actions call items parameter safe coherent
  have same : actual = target := Option.some.inj (retained.symm.trans attached)
  subst actual
  simpa [view, noLoan, completed_residual construct callbackConstruct fallback target.producer safeFinal.2.1 completed] using partition

theorem retirement_commutes [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (retired other : Fin clients) (position : Nat) (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : Accounting.sparesRetired retired actions) :
    advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions (retireConsumer state retired) =
      retireConsumer (advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions state) retired :=
  Accounting.runActions_after_retained_demand (sourceStep quantum) sourceCapture capacity gate actions state
    retired other position distinct live spares

/-- This license starts from authored entry, includes arbitrary ordinary
callback grants, shared requests, and the actual acknowledgment-only handback. -/
theorem scheduled_release_license [DecidableEq Output] [DecidableEq Owner]
    (charges : ∀ quantum (consumer : Context → Loan → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum consumer))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (quantum limit : Nat) (capacity : BodyCallShared.Stored (Output := Output) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallAdmission.schedule construct callbackConstruct fallback charges grants
      (BodyCallAdmission.openCall construct callbackConstruct fallback (OrderedDependencyStore.query before reader) items parameter context)
    let final := advance construct callbackConstruct fallback authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback before limit owned (Owner := Owner) (clients := clients))
    ∃ call, (release construct callbackConstruct fallback final).1 = some call ∧
      ∃ earned : BodyCallAdmission.quiet construct callbackConstruct fallback call.2.2,
        ∀ requested interface answers,
          (BodyCallAdmission.admit construct callbackConstruct fallback requested interface
            (OrderedDependencyStore.query before reader) items parameter call earned).1 = some answers →
          answers = source construct callbackConstruct (OrderedDependencyStore.query before reader) items parameter ∧
            ConventionAllows requested answers.length := by
  exact advance_release_license construct callbackConstruct fallback authority before current reader point required quantum capacity actions
    _ _ rfl items parameter
    (BodyCallAdmission.schedule_open_captured construct callbackConstruct fallback charges grants _ items parameter context)
    (schedule_coherent construct callbackConstruct fallback charges grants _ items parameter context)

#print axioms scheduled_release_license
#print axioms resume_coherent
#print axioms schedule_coherent
#print axioms scheduled_handoff_source
#print axioms completed_residual
#print axioms completed_handoff_source
#print axioms retirement_commutes
#print axioms adopt_keeps_cut
#print axioms release_adopt
#print axioms release_keeps_delivery
#print axioms release_keeps_source
#print axioms release_captured
#print axioms adopt_view
#print axioms pump_view
#print axioms advance_source
#print axioms adopt_advance_source
#print axioms advance_release_license
#print axioms advance_split
#print axioms denied_keeps_cut

namespace Controls

open BodyCallShared.Controls (world changed unrelated held revoked sourceAuthority)

abbrev State := BodyCallShared.Controls.State
abbrev OwnedCall := BodyCallShared.Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit)
def accept := BodyCallShared.accept Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit)
def refuse := BodyCallShared.refuse Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit)

def ordinary (consumer : Unit → BodyCallShared.Loan Nat.add (fun _ left _ => left) (fun _ _ => []) → Bool × Unit)
    (call : OwnedCall) :=
  BodyCallAdmission.resume Nat.add (fun _ left _ => left) (fun _ _ => []) 64 1 consumer
    (BodyCallShared.charge Nat.add (fun _ left _ => left) (fun _ _ => []) _ _) call

def firstAccepted := ordinary accept BodyCallShared.Controls.initialCall
def secondHeld := ordinary refuse firstAccepted
def heldFirst := ordinary refuse BodyCallShared.Controls.initialCall

def transfer (call : OwnedCall) : State :=
  adopt Nat.add (fun _ left _ => left) (fun _ _ => []) world 8 call

def progress (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point sourceAuthority) (quantum : Nat)
    (actions : List (Accounting.Action Nat 2)) (state : State) :=
  advance (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) sourceAuthority world current 0 point .consume
    quantum (fun _ => true) actions state

def currentGate (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point sourceAuthority) :=
  compatible (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume) sourceAuthority current 0 point .consume

def secondAdopted := transfer secondHeld
def secondCaptured := progress world held 0 [.pump] secondAdopted
def suffixDone := progress world held 64 (List.replicate 16 .pump) secondCaptured

theorem ordinary_pending_handoff_keeps_origin_prefix_and_paid_cut :
    firstAccepted.2.2.context.1 = [[7]] ∧ secondHeld.2.1.pending.isSome = true ∧
      (pending secondAdopted).map (·.1) = some 1 ∧
      secondAdopted.execution.map (·.producer) = some secondHeld ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) secondAdopted).1 = some secondHeld ∧
      progress world held 0 [] secondAdopted = secondAdopted :=
  ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩

theorem capture_and_handback_do_not_reissue_or_repoll :
    secondCaptured.delivery.log.rows = [(1, [[7]])] ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) secondCaptured).1.map
        (fun call => (call.2.1.pending.isNone, call.2.1.accepted, call.2.2.context.1, call.2.2.computation.1)) =
        some (true, 2, [[7], [7]], secondHeld.2.2.computation.1) ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) secondCaptured).2.delivery = secondCaptured.delivery ∧
      suffixDone.delivery.log.rows = [(1, [[7]])] ∧ suffixDone.delivery.log.completed = true :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

theorem refusal_and_zero_source_retry_keep_the_same_loan :
    pump (BodyCallShared.Controls.actualStep world held 0)
      (BodyCallShared.capture Nat.add (fun _ left _ => left) (fun _ _ => []))
      (fun _ => false) (currentGate world held) secondAdopted = (.admissionRefused, secondAdopted) ∧
      secondCaptured.execution.map (fun execution => execution.producer.2.2.computation) =
        secondAdopted.execution.map (fun execution => execution.producer.2.2.computation) ∧
      secondCaptured.execution.map (fun execution => execution.producer.1) =
        secondAdopted.execution.map (fun execution => execution.producer.1) :=
  ⟨rfl, rfl, by decide⟩

def both := progress world held 64 (List.replicate 16 .pump) (transfer heldFirst)
def firstReader := deliver (currentGate world held) both 0 100
def oneCancelled := retireConsumer firstReader.2 0
def otherReader := deliver (currentGate world held) oneCancelled 1 101

theorem independent_readers_keep_equal_occurrences_after_cancellation :
    both.delivery.log.rows = [(0, [[7]]), (1, [[7]])] ∧
      firstReader.1 = .observed (.answer 0 (0, [[7]])) ∧
      otherReader.1 = .observed (.answer 0 (0, [[7]])) ∧
      (deliver (currentGate world held) otherReader.2 1 101).1 = .observed (.answer 1 (1, [[7]])) ∧
      otherReader.2.execution = both.execution ∧
      (deliver (currentGate world held) oneCancelled 0 100).1 = .observed .cancelled :=
  ⟨by decide, by decide, by decide, by decide, rfl, by decide⟩

theorem current_source_and_permission_gate_progress_and_buffered_delivery :
    progress changed held 64 [.pump] secondAdopted = secondAdopted ∧
      progress world revoked 64 [.pump] secondAdopted = secondAdopted ∧
      progress unrelated held 0 [.pump] secondAdopted = secondCaptured ∧
      deliver (currentGate changed held) both 1 101 = (.contextRefused, both) ∧
      deliver (currentGate world revoked) both 1 101 = (.contextRefused, both) ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) both).1.map (fun call =>
        (BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) call, call.2.2.context.1)) =
        some (true, [[7], [7]]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩

def closedCall (authored : List (Equation Nat)) : OwnedCall :=
  BodyCallAdmission.resume Nat.add (fun _ left _ => left) (fun _ _ => []) 64 8 accept
    (BodyCallShared.charge Nat.add (fun _ left _ => left) (fun _ _ => []) _ _)
    (BodyCallAdmission.openCall Nat.add (fun _ left _ => left) (fun _ _ => []) authored ([] : List Nat) 0 ())

theorem terminal_empty_value_failure_and_yield_are_separate :
    (closedCall BodyCallRun.blank).2.2.context.1 = [[]] ∧
      (closedCall BodyCallRun.missed).2.2.context.1 = [] ∧
      BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) (closedCall BodyCallRun.blank) = true ∧
      BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) (closedCall BodyCallRun.missed) = true ∧
      BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) secondHeld = false ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) (transfer (closedCall BodyCallRun.blank))).1 =
        some (closedCall BodyCallRun.blank) :=
  ⟨by decide, by decide, by decide, by decide, by decide, rfl⟩

#print axioms ordinary_pending_handoff_keeps_origin_prefix_and_paid_cut
#print axioms capture_and_handback_do_not_reissue_or_repoll
#print axioms refusal_and_zero_source_retry_keep_the_same_loan
#print axioms independent_readers_keep_equal_occurrences_after_cancellation
#print axioms current_source_and_permission_gate_progress_and_buffered_delivery
#print axioms terminal_empty_value_failure_and_yield_are_separate

end Controls

end BodyCallShared.Handoff

namespace BodyCallShared.Weighted.Authored.Handoff

open Mettapedia.Algebra.SharedCoefficientLedger
open Cursor.ProducerOccurrenceLog
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory

variable {Input Output Weight Context Owner : Type} [Semiring Weight] {clients size : Nat}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

local notation "selected" => BodyCallWeighted.Authored.selection attachment
local notation "Row" => BodyCall.WeightedSource.Row Output Weight
local notation "Call" => Weighted.Call construct callbackConstruct fallback selected (Context := List Row × Context)
local notation "Loan" => Weighted.Loan construct callbackConstruct fallback selected
local notation "Borrowed" => Weighted.Borrowed construct callbackConstruct fallback selected
local notation "Cfg" => Weighted.Configuration construct callbackConstruct fallback selected
  (Context := List Row × Context) (size := size) Owner clients
local notation "Source" => BodyCallWeighted.Authored.stateView construct callbackConstruct fallback attachment
local notation "Residual" => Authored.residual construct callbackConstruct fallback attachment
local notation "loanRows" => Authored.loanRows construct callbackConstruct fallback attachment
local notation "storedRows" => Authored.storedRows (Output := Output) (Weight := Weight)

def resume (quantum allowance : Nat) (consumer : Context → Loan → Bool × Context) (call : Call) : Call :=
  BodyCallWeighted.Compact.Attachment.resumeCallSource construct callbackConstruct fallback selected quantum allowance
    (BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment consumer) call

def accept (context : Context) (_ : Loan) := (true, context)

def refuse (context : Context) (_ : Loan) := (false, context)


/-- The same cold handoff used by plain source calls, now retaining the full
sparse loan and its prior authored weighted prefix. -/
def adopt (world : OrderedDependencyStore.Store (Equation Output) size) (limit : Nat) (call : Call) : Cfg :=
  BodyCallShared.retainedAdopt world limit call

def acknowledge := resume construct callbackConstruct fallback attachment 0 1
  (accept construct callbackConstruct fallback attachment (Context := Context))

def release (state : Cfg) : Option Call × Cfg :=
  BodyCallShared.retainedRelease (acknowledge construct callbackConstruct fallback attachment) state

def Safe (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call) : Prop :=
  BodyCallWeighted.Authored.Captured construct callbackConstruct fallback attachment authored items parameter call ∧
    BodyCallWeighted.Compact.Attachment.Origin construct callbackConstruct fallback selected call.2.2.computation.2 ∧
    Weighted.Coherent construct callbackConstruct fallback selected call

theorem resume_safe (quantum allowance : Nat) (consumer : Context → Loan → Bool × Context)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (resume construct callbackConstruct fallback attachment quantum allowance consumer call) := by
  refine ⟨BodyCallWeighted.Authored.resume_captured construct callbackConstruct fallback attachment quantum allowance consumer
      authored items parameter call safe.1,
    BodyCallWeighted.Compact.Attachment.resume_origin construct callbackConstruct fallback selected quantum allowance
      (BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment consumer) call safe.2.1, ?_⟩
  unfold resume BodyCallWeighted.Compact.Attachment.resumeCallSource resumeCall
  cases stopped : call.2.1.terminal with
  | some reason => exact safe.2.2
  | none =>
      simpa [Weighted.Coherent, BodyCallWeighted.Compact.Attachment.ownedProvider] using
        BodyCallShared.retainedCallbacks_coherent
          (BodyCallWeighted.Compact.Attachment.SparseProvider construct callbackConstruct fallback selected)
          (fun _ _ => 1) quantum
          (BodyCallWeighted.Compact.Attachment.isReturn construct callbackConstruct fallback selected)
          (BodyCallWeighted.Compact.Attachment.rearm construct callbackConstruct fallback selected)
          (BodyCallWeighted.Compact.Attachment.consume construct callbackConstruct fallback selected
            (BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment consumer))
          (BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selected)
          (fun _ _ => 1) allowance call.2.1.accepted call.2.1.pending call.2.2
          (fun loan held => (safe.2.2 loan held).2)

/-- Construct the source/loan invariant from entry and arbitrary actual
callback grants; no weighted-answer equality is an input. -/
theorem schedule_safe
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
        (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
        (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected authored items parameter ([], context))) := by
  have keeps : ∀ call, Safe construct callbackConstruct fallback attachment authored items parameter call →
      Safe construct callbackConstruct fallback attachment authored items parameter
        (BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
          (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants) call) := by
    induction grants with
    | nil => exact fun _ safe => safe
    | cons grant rest ih =>
        exact fun call safe => ih _ (resume_safe construct callbackConstruct fallback attachment grant.1 grant.2.1 grant.2.2 authored items parameter call safe)
  exact keeps _ ⟨BodyCallWeighted.Authored.open_captured construct callbackConstruct fallback attachment authored items parameter context,
    BodyCallWeighted.Compact.Attachment.open_origin construct callbackConstruct fallback selected authored items parameter ([], context),
    by intro loan held; cases held⟩

theorem release_adopt (world : OrderedDependencyStore.Store (Equation Output) size) (limit : Nat) (call : Call) :
    (release construct callbackConstruct fallback attachment
      (adopt construct callbackConstruct fallback attachment world limit call (Owner := Owner) (clients := clients))).1 = some call := by
  cases held : call.2.1.pending <;>
    simp [release, adopt, BodyCallShared.retainedRelease, BodyCallShared.retainedAdopt, held]

/-- Acknowledgment uses the existing authored collector. It adds exactly this
loan's coefficient word and keeps every source frame, factor and firing ordinal. -/
theorem acknowledge_cut (call : Call) (coherent : Weighted.Coherent construct callbackConstruct fallback selected call)
    (loan : Loan) (held : call.2.1.pending = some loan) :
    let next := acknowledge construct callbackConstruct fallback attachment call
    next.2.1.pending = none ∧ next.2.1.accepted = call.2.1.accepted + 1 ∧
      next.2.2.context.2.1 = call.2.2.context.2.1 ++ loanRows (call.2.1.accepted, loan) ∧
      next.2.2.computation.1 = call.2.2.computation.1 ∧
      Source next.2.2.computation.2 = Source call.2.2.computation.2 ∧ Residual next = Residual call := by
  have shape := coherent loan held
  cases final : BodyCallWeighted.Compact.Attachment.terminalAfter construct callbackConstruct fallback selected loan <;>
    simp [acknowledge, resume, BodyCallWeighted.Compact.Attachment.resumeCallSource, resumeCall,
      shape.1, held, fromCallbacks, BodyCallWeighted.Compact.Attachment.ownedProvider, Retained.provider,
      shape.2.1, shape.2.2, BodyCallWeighted.Compact.Attachment.consume, BodyCallWeighted.Authored.reader,
      accept, final, Authored.residual, BodyCallWeighted.Authored.unaccepted, BodyCallWeighted.Authored.stateView,
      BodyCallWeighted.Authored.moveView, BodyCallWeighted.Compact.Attachment.rearm, Authored.loanRows,
      BodyCall.WeightedSource.emitted, BodyCall.Move.rows]

theorem release_safe (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter execution.producer) :
    ∃ call, (release construct callbackConstruct fallback attachment state).1 = some call ∧
      Safe construct callbackConstruct fallback attachment authored items parameter call := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  · exact ⟨_, rfl, resume_safe construct callbackConstruct fallback attachment 0 1
      (accept construct callbackConstruct fallback attachment) authored items parameter execution.producer safe⟩
  · exact ⟨_, rfl, safe⟩

theorem release_keeps_source (state : Cfg) (execution : Execution Call Borrowed Empty Loan)
    (attached : state.execution = some execution)
    (coherent : Weighted.Coherent construct callbackConstruct fallback selected execution.producer) :
    ∃ call, (release construct callbackConstruct fallback attachment state).1 = some call ∧
      call.2.2.computation.1 = execution.producer.2.2.computation.1 ∧
      Source call.2.2.computation.2 = Source execution.producer.2.2.computation.2 ∧
      (release construct callbackConstruct fallback attachment state).2.delivery = state.delivery := by
  unfold release BodyCallShared.retainedRelease
  rw [attached]
  simp only [Option.map_some]
  split
  next ready =>
    obtain ⟨loan, held⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp ready).2
    have kept := acknowledge_cut construct callbackConstruct fallback attachment execution.producer coherent loan held
    exact ⟨_, rfl, kept.2.2.2.1, kept.2.2.2.2.1, rfl⟩
  next waiting => exact ⟨_, rfl, rfl, rfl, rfl⟩

variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

local notation "gate" => BodyCallShared.Handoff.compatible authority current reader point required

/-- New source progress and buffered publication use the same current gate.
The actual weighted reader is retained across acknowledgments and handback. -/
def poll (quantum : Nat) (call : Call) : Call :=
  if gate before then resume construct callbackConstruct fallback attachment quantum 1
    (refuse construct callbackConstruct fallback attachment) call else call

def step (quantum : Nat) : Call → Weighted.Move construct callbackConstruct fallback selected (Context := List Row × Context) :=
  BodyCallShared.retainedStep (Weighted.inspect construct callbackConstruct fallback selected)
    (acknowledge construct callbackConstruct fallback attachment)
    (poll construct callbackConstruct fallback attachment authority before current reader point required quantum)

private theorem poll_safe (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (poll construct callbackConstruct fallback attachment authority before current reader point required quantum call) := by
  unfold poll
  split
  · exact resume_safe construct callbackConstruct fallback attachment quantum 1
      (refuse construct callbackConstruct fallback attachment) authored items parameter call safe
  · exact safe

theorem step_safe (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    Safe construct callbackConstruct fallback attachment authored items parameter
      (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).next := by
  unfold step BodyCallShared.retainedStep
  split
  · simpa only [Weighted.inspect_next] using safe
  · cases held : call.2.1.pending with
    | some loan =>
        exact resume_safe construct callbackConstruct fallback attachment 0 1
          (accept construct callbackConstruct fallback attachment) authored items parameter call safe
    | none =>
        rw [Weighted.inspect_next]
        unfold poll
        split
        · exact resume_safe construct callbackConstruct fallback attachment quantum 1
            (refuse construct callbackConstruct fallback attachment) authored items parameter call safe
        · exact safe

theorem step_rows (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).returns.flatMap loanRows ++
        Residual (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).next = Residual call := by
  unfold step BodyCallShared.retainedStep
  split
  · rw [Weighted.inspect_next]
    have empty : call.2.1.pending = none := by
      cases held : call.2.1.pending with
      | none => rfl
      | some loan => simp [(safe.2.2 loan held).1] at ‹call.2.1.terminal.isSome = true›
    simpa [Authored.residual, empty] using
      Authored.inspect_rows construct callbackConstruct fallback attachment call safe.2.2
  · cases held : call.2.1.pending with
    | some loan =>
        simpa only [ProducerOutcome.returns, ProducerOutcome.next, List.flatMap_nil, List.nil_append] using
          (acknowledge_cut construct callbackConstruct fallback attachment call safe.2.2 loan held).2.2.2.2.2
    | none =>
        rw [Weighted.inspect_next]
        have coherent := (poll_safe construct callbackConstruct fallback attachment authority before current reader point required
          quantum authored items parameter call safe).2.2
        rw [Authored.inspect_rows construct callbackConstruct fallback attachment _ coherent]
        unfold poll
        split
        · have identical : BodyCallWeighted.Authored.reader construct callbackConstruct fallback attachment
              (refuse construct callbackConstruct fallback attachment (Context := Context)) =
              Weighted.refuse construct callbackConstruct fallback selected := by
            funext context loan
            cases context
            rfl
          unfold resume
          rw [identical]
          simpa only [Authored.residual, held] using
            Authored.poll_view construct callbackConstruct fallback attachment quantum call
              (by simpa using ‹¬call.2.1.terminal.isSome = true›) held safe.1.2.1
        · simp [Authored.residual, held]

/-- Every newly exposed factor image is licensed by the actual source loan;
failed and sibling activations cannot be relabelled as return contributions. -/
theorem step_factor_origin (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (call : Call) (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    ∀ borrowed ∈ (step construct callbackConstruct fallback attachment authority before current reader point required quantum call).returns,
      Weighted.Authentic construct callbackConstruct fallback selected (Weighted.image construct callbackConstruct fallback selected borrowed) := by
  unfold step BodyCallShared.retainedStep
  split
  · exact Weighted.inspect_origin construct callbackConstruct fallback selected call safe.2.1 safe.2.2
  · cases held : call.2.1.pending with
    | some loan => simp [ProducerOutcome.returns]
    | none =>
        have nextSafe := poll_safe construct callbackConstruct fallback attachment authority before current reader point required quantum
          authored items parameter call safe
        exact Weighted.inspect_origin construct callbackConstruct fallback selected _ nextSafe.2.1 nextSafe.2.2

theorem adopt_pending_origin (world : OrderedDependencyStore.Store (Equation Output) size) (limit : Nat)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (call : Call)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter call) :
    ∀ borrowed ∈ (pending (adopt construct callbackConstruct fallback attachment world limit call (Owner := Owner) (clients := clients))).toList,
      Weighted.Authentic construct callbackConstruct fallback selected (Weighted.image construct callbackConstruct fallback selected borrowed) := by
  intro borrowed present
  have origin := Weighted.inspect_origin construct callbackConstruct fallback selected call safe.2.1 safe.2.2
  rw [Weighted.inspect_returns construct callbackConstruct fallback selected call safe.2.2] at origin
  exact origin borrowed (by simpa [pending, adopt, BodyCallShared.retainedAdopt] using present)

local notation "sourceStep" => step construct callbackConstruct fallback attachment authority before current reader point required
local notation "sourceCapture" => Weighted.capture construct callbackConstruct fallback selected

private theorem path_rows (quantum : Nat) (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    {first last : Call} {returns : List Borrowed} (path : ProducerPath (sourceStep quantum) first returns last)
    (safe : Safe construct callbackConstruct fallback attachment authored items parameter first) :
    Safe construct callbackConstruct fallback attachment authored items parameter last ∧
      returns.flatMap loanRows ++ Residual last = Residual first := by
  induction path with
  | refl => exact ⟨safe, by simp⟩
  | @next first moved later returns transition tail ih =>
      have nextSafe := step_safe construct callbackConstruct fallback attachment authority before current reader point required quantum
        authored items parameter first safe
      have rows := step_rows construct callbackConstruct fallback attachment authority before current reader point required quantum
        authored items parameter first safe
      rw [transition] at nextSafe rows
      obtain ⟨finalSafe, remaining⟩ := ih nextSafe
      exact ⟨finalSafe, by simp only [List.flatMap_append, List.append_assoc]; rw [remaining, rows]⟩

def advance [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg) :=
  Accounting.runActions (sourceStep quantum) sourceCapture capacity gate actions state

local notation "View" => Authored.view construct callbackConstruct fallback attachment

private theorem pump_view (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (items : List Input) (parameter : Nat) (state : Cfg) (execution target : Execution Call Borrowed Empty Loan)
    (attached : state.execution = some execution)
    (nextAttached : (pump (sourceStep quantum) sourceCapture capacity gate state).2.execution = some target)
    (safe : Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter execution.producer) :
    View (pump (sourceStep quantum) sourceCapture capacity gate state).2 target.producer = View state execution.producer := by
  obtain ⟨actual, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
  have same : actual = target := Option.some.inj (retained.symm.trans nextAttached)
  subst actual
  have rows := (path_rows construct callbackConstruct fallback attachment authority before current reader point required quantum
    (OrderedDependencyStore.query before reader) items parameter path safe).2
  have conserved := pump_conservation loanRows storedRows (sourceStep quantum) sourceCapture capacity gate
    (by intro loan stored captured; cases captured; exact Authored.capture_rows construct callbackConstruct fallback attachment loan) state
  have flat := congrArg (List.flatMap id) conserved
  simp only [List.flatMap_append, List.flatMap_map, id_eq] at flat
  unfold Authored.view
  rw [pump_rows, List.flatMap_append]
  calc
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((admitted (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap storedRows ++
          (pending (pump (sourceStep quantum) sourceCapture capacity gate state).2).toList.flatMap loanRows) ++ Residual target.producer := by
          simp only [List.append_assoc]
    _ = state.delivery.log.rows.flatMap storedRows ++
        ((pending state).toList.flatMap loanRows ++
          (returned (pump (sourceStep quantum) sourceCapture capacity gate state).1).flatMap loanRows) ++ Residual target.producer := by rw [← flat]
    _ = _ := by simp only [List.append_assoc]; rw [rows]

private theorem delivery_view [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (state : Cfg) (call : Call) (client : Fin clients) (owner : Owner) :
    View (deliver gate state client owner).2 call = View state call := by
  have rows : (deliver gate state client owner).2.delivery.log.rows = state.delivery.log.rows := by
    unfold deliver
    split
    · cases reply : Cursor.SharedOccurrenceLog.peek state.delivery.log client <;>
        simp [Cursor.SharedOccurrenceOwnership.advance, Cursor.SharedOccurrenceOwnership.acknowledge,
          Cursor.SharedOccurrenceOwnership.prepare, Cursor.SharedOccurrenceLog.pull, Cursor.SharedOccurrenceLog.setPosition, reply]
    · rfl
  simp only [Authored.view, rows, pending, delivery_preserves_complete_execution]

theorem advance_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (state : Cfg)
    (execution : Execution Call Borrowed Empty Loan) (attached : state.execution = some execution)
    (items : List Input) (parameter : Nat)
    (safe : Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter execution.producer) :
    ∃ target, (advance construct callbackConstruct fallback attachment authority before current reader point required
        quantum capacity actions state).execution = some target ∧
      Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      View (advance construct callbackConstruct fallback attachment authority before current reader point required
        quantum capacity actions state) target.producer = View state execution.producer := by
  induction actions generalizing state execution with
  | nil => exact ⟨execution, attached, safe, rfl⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨next, retained, path⟩ := pump_producer_path (sourceStep quantum) sourceCapture capacity gate state execution attached
          obtain ⟨nextSafe, _⟩ := path_rows construct callbackConstruct fallback attachment authority before current reader point required quantum
            (OrderedDependencyStore.query before reader) items parameter path safe
          obtain ⟨target, final, safeFinal, same⟩ := ih _ next retained nextSafe
          exact ⟨target, final, safeFinal, same.trans
            (pump_view construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
              items parameter state execution next attached retained safe)⟩
      | deliver client owner =>
          obtain ⟨target, final, safeFinal, same⟩ := ih _ execution
            ((delivery_preserves_complete_execution gate state client owner).trans attached) safe
          exact ⟨target, final, safeFinal, same.trans
            (delivery_view construct callbackConstruct fallback attachment authority current reader point required state execution.producer client owner)⟩

/-- The actual nonfresh authored collector supplies the weighted prefix. The
shared log captures its same sparse factors once; delivery creates none. -/
theorem scheduled_handoff_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (quantum limit : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let final := advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ target, final.execution = some target ∧
      Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      owned.2.2.context.2.1 ++ View final target.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
    (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
    (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
      (OrderedDependencyStore.query before reader) items parameter ([], context))
  have safe := schedule_safe construct callbackConstruct fallback attachment grants (OrderedDependencyStore.query before reader) items parameter context
  obtain ⟨target, final, nextSafe, same⟩ := advance_source construct callbackConstruct fallback attachment authority before current reader point required
    quantum capacity actions (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients)) _ rfl items parameter safe
  refine ⟨target, final, nextSafe, ?_⟩
  rw [same]
  have inspected := Authored.inspect_rows construct callbackConstruct fallback attachment owned safe.2.2
  rw [Weighted.inspect_returns construct callbackConstruct fallback selected owned safe.2.2] at inspected
  have balance : View (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients)) owned =
      BodyCallWeighted.Authored.unaccepted construct callbackConstruct fallback attachment owned.2.2.computation.2 := by
    simpa [Authored.view, adopt, BodyCallShared.retainedAdopt, pending, Cursor.SharedOccurrenceLog.initial,
      Option.toList_map, List.flatMap_map] using inspected
  rw [balance]
  exact safe.1.2.2

/-- All four completed calling modes are earned after this actual weighted
handoff and handback; a pending final loan is not treated as completion. -/
theorem scheduled_release_license [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (quantum limit : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let final := advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ call, (release construct callbackConstruct fallback attachment final).1 = some call ∧
      ∀ requested interface answers,
        (BodyCallWeighted.Authored.admit construct callbackConstruct fallback attachment requested interface
          (OrderedDependencyStore.query before reader) items parameter call).1 = some answers →
        answers = BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter ∧
          ConventionAllows requested answers.length := by
  dsimp only
  obtain ⟨target, attached, safe, _⟩ := scheduled_handoff_source construct callbackConstruct fallback attachment authority before current reader point required
    grants quantum limit capacity actions items parameter context (Owner := Owner) (clients := clients)
  obtain ⟨call, handback, safeBack⟩ := release_safe construct callbackConstruct fallback attachment
    (OrderedDependencyStore.query before reader) items parameter _ target attached safe
  exact ⟨call, handback, fun requested interface answers admitted =>
    BodyCallWeighted.Authored.admit_license construct callbackConstruct fallback attachment requested interface
      (OrderedDependencyStore.query before reader) items parameter call safeBack.1 answers admitted⟩

theorem denied_keeps_cut [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (state : Cfg) (client : Fin clients) (owner : Owner)
    (denied : OrderedDependencyStore.checkRead current (OrderedDependencyStore.readStamp state.context reader) = false ∨
      ¬ FrameUpdate point.authority required) :
    pump (sourceStep quantum) sourceCapture capacity gate state =
        (if state.execution.isNone then .detached else .contextRefused, state) ∧
      deliver gate state client owner = (.contextRefused, state) := by
  have no : gate state.context = false := by
    rcases denied with stale | revoked <;> simp [BodyCallShared.Handoff.compatible, *]
  constructor
  · cases attached : state.execution <;> simp [pump, attached, no]
  · simp [deliver, no]

/-- At an acknowledged finished cut, the stored suffix and the prior ordinary
weighted prefix are exactly the authored weighted meaning. -/
theorem completed_suffix_source [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (quantum limit : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
    (actions : List (Accounting.Action Owner clients)) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let final := advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions
      (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∀ target : Execution Call Borrowed Empty Loan, final.execution = some target → pending final = none →
      BodyCallWeighted.Compact.Attachment.complete construct callbackConstruct fallback selected target.producer = true →
      owned.2.2.context.2.1 ++ final.delivery.log.rows.flatMap storedRows =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  intro owned final target attached noLoan finished
  obtain ⟨actual, retained, safe, partition⟩ := scheduled_handoff_source construct callbackConstruct fallback attachment authority
    before current reader point required grants quantum limit capacity actions items parameter context (Owner := Owner) (clients := clients)
  have same : actual = target := Option.some.inj (retained.symm.trans attached)
  subst actual
  have noPending : target.producer.2.1.pending = none := by
    cases held : target.producer.2.1.pending with
    | none => rfl
    | some loan => simp [BodyCallWeighted.Compact.Attachment.complete,
        BodyCallWeighted.Compact.Attachment.eraseCall, BodyCallAdmission.complete, held] at finished
  have empty := BodyCallWeighted.Authored.completed_unaccepted construct callbackConstruct fallback attachment target.producer
    safe.1.1.2.1 safe.1.2.1.2 finished
  dsimp only [owned, final] at noLoan ⊢
  simpa [Authored.view, noLoan, Authored.residual, noPending, empty] using partition

namespace History

open Mettapedia.GSLT.Core.InferenceControl.Recording
open Cursor.ProducerOccurrenceLog.Accounting

variable [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]
    (quantum : Nat) (capacity : Weighted.Stored (Output := Output) (Weight := Weight) → Bool)
local notation "Action" => Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)
local notation "actualStep" => sourceStep quantum

/-- Entry selection uses the existing streaming observers. The disabled
branch is the original uncounted action runner on this same retained Call. -/
def observe (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :=
  enterActionObservers actualStep sourceCapture capacity gate history account actions state

theorem erasure (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (actions : List Action) (state : Cfg) :
    (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account actions state).2.2 =
      advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions state :=
  enterActionObservers_erases _ _ _ _ _ _ _ _

/-- The recorded endpoint retains the independently weighted source partition,
actual source loan, frames and work. Nothing is reconstructed from the diary. -/
theorem scheduled_source (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (limit : Nat) (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let observed := observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account actions (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ target, observed.2.2.execution = some target ∧
      Safe construct callbackConstruct fallback attachment (OrderedDependencyStore.query before reader) items parameter target.producer ∧
      owned.2.2.context.2.1 ++ View observed.2.2 target.producer =
        BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter := by
  dsimp only
  rw [erasure]
  exact scheduled_handoff_source construct callbackConstruct fallback attachment authority before current reader point required
    grants quantum limit capacity actions items parameter context

theorem scheduled_license (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (grants : List (BodyCallWeighted.Authored.Grant construct callbackConstruct fallback attachment (Context := Context)))
    (limit : Nat) (actions : List Action) (items : List Input) (parameter : Nat) (context : Context) :
    let owned := BodyCallWeighted.Compact.Attachment.schedule construct callbackConstruct fallback selected
      (BodyCallWeighted.Authored.readGrants construct callbackConstruct fallback attachment grants)
      (BodyCallWeighted.Compact.Attachment.openCall construct callbackConstruct fallback selected
        (OrderedDependencyStore.query before reader) items parameter ([], context))
    let observed := observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account actions (adopt construct callbackConstruct fallback attachment before limit owned (Owner := Owner) (clients := clients))
    ∃ call, (release construct callbackConstruct fallback attachment observed.2.2).1 = some call ∧
      ∀ requested interface answers,
        (BodyCallWeighted.Authored.admit construct callbackConstruct fallback attachment requested interface
          (OrderedDependencyStore.query before reader) items parameter call).1 = some answers →
        answers = BodyCall.WeightedSource.source construct callbackConstruct attachment (OrderedDependencyStore.query before reader) items parameter ∧
          ConventionAllows requested answers.length := by
  dsimp only
  rw [erasure]
  exact scheduled_release_license construct callbackConstruct fallback attachment authority before current reader point required
    grants quantum limit capacity actions items parameter context

set_option backward.isDefEq.respectTransparency false in
/-- History and numeric accounts are the existing RunAccount projections of
actual operations. These are admission/delivery events and protocol units;
acknowledgment may count a driver operation without a new source request. -/
theorem source_path (record : Prefix Occurrence) (account : ProtocolAccount) (actions : List Action) (state : Cfg) :
    letI : Quiver.{0} Cfg := actionQuiver (Output := Owner) (clients := clients) actualStep sourceCapture capacity gate
    observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
        (some record) (some account) actions state =
      (some (Prefix.append record (pathOccurrences actualStep sourceCapture capacity gate
        (actionPath actualStep sourceCapture capacity gate actions state))),
        some (account * (splitAccount (Output := Owner) (clients := clients) actualStep sourceCapture capacity gate).of
          (actionPath actualStep sourceCapture capacity gate actions state)),
        advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity actions state) := by
  simpa only [observe, enterActionObservers, advance] using
    congrArg (fun result => (some result.1, some result.2.2, result.2.1))
      (observeActions_eq_source_accounts actualStep sourceCapture capacity gate actions record account state)

theorem split (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
      history account (first ++ second) state =
      observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
        (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity history account first state).1
        (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity history account first state).2.1 second
        (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity history account first state).2.2 :=
  enterActionObservers_append _ _ _ _ _ _ _ _ _

theorem forget (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List Action) (state : Cfg) :
    observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity none
      (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity (some record) (some account) first state).2.1
      second (observe construct callbackConstruct fallback attachment authority before current reader point required quantum capacity
        (some record) (some account) first state).2.2 =
      (none, some (count actualStep sourceCapture capacity gate (first ++ second) account state).2,
        advance construct callbackConstruct fallback attachment authority before current reader point required quantum capacity (first ++ second) state) := by
  unfold observe
  rw [forget_action_history_preserves_account, count_erases]
  rfl

theorem late_bounded (first gap last : List Action) (earlier : Prefix Occurrence) (bound : Nat) (state : Cfg) :
    let resumed := runActions actualStep sourceCapture capacity gate gap
      (recordActions actualStep sourceCapture capacity gate first earlier state).2
    let events := pathOccurrences actualStep sourceCapture capacity gate (actionPath actualStep sourceCapture capacity gate last resumed)
    let result := recordActions actualStep sourceCapture capacity gate last (Prefix.initial bound) resumed
    result.1.items = events.take bound ∧ result.1.remaining = bound - events.length ∧ result.1.omitted = events.length - bound :=
  fresh_record_after_unrecorded_gap_bounds _ _ _ _ _ _ _ _ _ _

#print axioms erasure
#print axioms scheduled_source
#print axioms scheduled_license
#print axioms source_path
#print axioms split
#print axioms forget
#print axioms late_bounded

end History

#print axioms completed_suffix_source
#print axioms release_keeps_source
#print axioms denied_keeps_cut
#print axioms step_factor_origin
#print axioms adopt_pending_origin
#print axioms resume_safe
#print axioms schedule_safe
#print axioms release_adopt
#print axioms acknowledge_cut
#print axioms release_safe
#print axioms step_safe
#print axioms step_rows
#print axioms advance_source
#print axioms scheduled_handoff_source
#print axioms scheduled_release_license

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)
open BodyCallAdmission.CurrentAuthority.Controls (held revoked)
abbrev sourceAuthority := BodyCallShared.Controls.sourceAuthority
abbrev authored := BodyCallShared.Weighted.Controls.authored
abbrev world := BodyCallShared.Weighted.Controls.world
open Mettapedia.GSLT.Core.InferenceControl.Recording

abbrev profile := BodyCallWeighted.Authored.Controls.branches
abbrev chosen := BodyCallWeighted.Authored.selection profile
abbrev ControlCall := Weighted.Call build callback noFallback chosen
  (Context := List (BodyCall.WeightedSource.Row Nat Nat) × Unit)
abbrev State := Weighted.Configuration build callback noFallback chosen
  (Context := List (BodyCall.WeightedSource.Row Nat Nat) × Unit) (size := 1) Nat 2

def initialCall : ControlCall := BodyCallWeighted.Compact.Attachment.openCall build callback noFallback chosen authored [0] 0 ([], ())
def firstAccepted := resume build callback noFallback profile 64 1 (accept build callback noFallback profile) initialCall
def secondHeld := resume build callback noFallback profile 64 1 (refuse build callback noFallback profile) firstAccepted
def heldFirst := resume build callback noFallback profile 64 1 (refuse build callback noFallback profile) initialCall

def transfer (call : ControlCall) : State := adopt build callback noFallback profile world 8 call

def progress (current : OrderedDependencyStore.Store (Equation Nat) 1)
    (point : IndexedAuthority.Point sourceAuthority) (quantum : Nat)
    (actions : List (Accounting.Action Nat 2)) (state : State) :=
  advance (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume)
    build callback noFallback profile sourceAuthority world current 0 point .consume quantum (fun _ => true) actions state

def currentGate (current : OrderedDependencyStore.Store (Equation Nat) 1)
    (point : IndexedAuthority.Point sourceAuthority) :=
  BodyCallShared.Handoff.compatible (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume) sourceAuthority current 0 point .consume

def observe (bound : Nat) (actions : List (Accounting.Action Nat 2)) (state : State) :=
  History.observe (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
    build callback noFallback profile sourceAuthority world world 0 held .consume 64 (fun _ => true)
    (some (Prefix.initial bound)) (some 1) actions state

def seed := transfer secondHeld
def captured := progress world held 0 [.pump] seed
def acknowledged := progress world held 0 [.pump] captured
def finished := progress world held 64 (List.replicate 16 .pump) acknowledged

def factorView (state : State) := state.delivery.log.rows.map (fun row =>
  (row.1, row.2.1, identities row.2.2, Mettapedia.Algebra.SharedCoefficientLedger.denote row.2.2))

theorem nonfresh_handoff_keeps_original_weighted_prefix_and_loan :
    firstAccepted.2.2.context.2.1 = [([7], [2, 3])] ∧
      (pending seed).map (fun loan => (loan.1, identities loan.2.2.2.val.loan)) = some (1, [0, 3]) ∧
      factorView captured = [(1, [[7]], [0, 3], 10)] ∧
      (release build callback noFallback profile seed).1 = some secondHeld :=
  ⟨by decide, by decide, by decide, rfl⟩

theorem acknowledgment_and_handback_keep_source_factors_without_global_fold :
    acknowledged.execution.map (fun execution => execution.producer.2.2.context.2.1) =
        some [([7], [2, 3]), ([7], [2, 5])] ∧
      captured.execution.map (fun execution => execution.producer.2.2.computation.1) =
        acknowledged.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      captured.execution.map (fun execution => BodyCallWeighted.Authored.stateView build callback noFallback profile execution.producer.2.2.computation.2) =
        acknowledged.execution.map (fun execution => BodyCallWeighted.Authored.stateView build callback noFallback profile execution.producer.2.2.computation.2) ∧
      (release build callback noFallback profile captured).1 = acknowledged.execution.map (·.producer) ∧
      factorView finished = [(1, [[7]], [0, 3], 10)] ∧
      (release build callback noFallback profile finished).1.map
        (fun call => (BodyCallWeighted.Compact.Attachment.complete build callback noFallback chosen call, call.2.2.context.2.1)) =
        some (true, [([7], [2, 3]), ([7], [2, 5])]) :=
  ⟨by decide, rfl, rfl, rfl, by decide, by decide⟩

def both := progress world held 64 (List.replicate 16 .pump) (transfer heldFirst)
def left := deliver (currentGate world held) both 0 100
def cancelled := retireConsumer left.2 0
def right := deliver (currentGate world held) cancelled 1 101

theorem equal_payloads_share_outer_identity_but_keep_distinct_branch_factors :
    factorView both = [(0, [[7]], [0, 2], 6), (1, [[7]], [0, 3], 10)] ∧
      both.delivery.log.rows[0]!.2.2.head? = both.delivery.log.rows[1]!.2.2.head? ∧
      right.1 = left.1 ∧ right.2.execution = both.execution ∧
      (deliver (currentGate world held) right.2 1 101).1 =
        .observed (.answer 1 (1, [[7]], [⟨0, 0, 2⟩, ⟨3, 3, 5⟩])) ∧
      Cursor.SharedOccurrenceLog.unread cancelled.delivery.log 0 = [] :=
  ⟨by decide, by decide, rfl, rfl, by decide, by decide⟩

def word : List (Accounting.Action Nat 2) := [.pump, .pump, .deliver 0 100, .deliver 1 101]
def recorded := observe 1 word seed

def forgotten := History.observe
  (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
  build callback noFallback profile sourceAuthority world world 0 held .consume 64 (fun _ => true)
  none recorded.2.1 (List.replicate 16 .pump) recorded.2.2

theorem bounded_history_distinguishes_admission_delivery_and_source_work :
    recorded.1.map (fun diary => (diary.items.length, diary.omitted)) = some (1, 2) ∧
      recorded.2.1.map (fun account => (Multiplicative.toAdd account.1, Multiplicative.toAdd account.2)) = some (1, 2) ∧
      recorded.2.2.execution.map (fun execution => execution.producer.2.2.computation.1) =
        seed.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      forgotten.1 = none ∧ factorView forgotten.2.2 = factorView finished ∧
      forgotten.2.2.execution = finished.execution :=
  ⟨by decide, by decide, rfl, rfl, by decide, rfl⟩

def late := observe 0 [.pump, .deliver 1 101] captured

theorem late_recording_omits_prior_admission_and_retains_the_weighted_residual :
    late.1.map (fun diary => (diary.items.length, diary.omitted)) = some (0, 1) ∧
      late.2.2.execution = recorded.2.2.execution ∧
      factorView late.2.2 = factorView captured ∧
      (release build callback noFallback profile late.2.2).1.map (fun call => call.2.2.context.2.1) =
        some [([7], [2, 3]), ([7], [2, 5])] :=
  ⟨by decide, rfl, by decide, by decide⟩

def changed := OrderedDependencyStore.appendOwn world 0 [⟨⟨.any, .any⟩, false, .singleton 8⟩]

theorem refusal_currentness_and_mode_checks_keep_the_same_earned_weighted_cut :
    pump (step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
      build callback noFallback profile sourceAuthority world world 0 held .consume 0)
      (Weighted.capture build callback noFallback chosen) (fun _ => false) (currentGate world held) seed = (.admissionRefused, seed) ∧
      progress changed held 64 [.pump] seed = seed ∧
      progress world revoked 64 [.pump] seed = seed ∧
      deliver (currentGate changed held) both 1 101 = (.contextRefused, both) ∧
      (release build callback noFallback profile finished).1.map
        (fun call => (BodyCallWeighted.Authored.admit build callback noFallback profile .direct .singleValue authored [0] 0 call).1) = some none ∧
      (release build callback noFallback profile seed).1.map
        (fun call => BodyCallWeighted.Compact.Attachment.complete build callback noFallback chosen call) = some false :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

#print axioms nonfresh_handoff_keeps_original_weighted_prefix_and_loan
#print axioms acknowledgment_and_handback_keep_source_factors_without_global_fold
#print axioms equal_payloads_share_outer_identity_but_keep_distinct_branch_factors
#print axioms bounded_history_distinguishes_admission_delivery_and_source_work
#print axioms late_recording_omits_prior_admission_and_retains_the_weighted_residual
#print axioms refusal_currentness_and_mode_checks_keep_the_same_earned_weighted_cut

end Controls

end BodyCallShared.Weighted.Authored.Handoff


namespace PreparationControls

private def constant (body : Code Nat) : Code Nat :=
  DecisionTree.code ⟨body, body, body, body⟩

def committedPrefix : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .singleton 7⟩,
   ⟨⟨.any, .any⟩, false, .unsupported⟩]

/-- Selected bodies and whole-source cursor support have different scopes. -/
theorem committed_body_compiles_while_discarded_source_is_unsupported :
    (Preparation.prepare committedPrefix).supported = false ∧
    Preparation.strictCode (Preparation.prepare committedPrefix) = some (constant (.singleton 7)) ∧
    Preparation.optionalTree (Preparation.prepare committedPrefix) =
      some ⟨some (.singleton 7), some (.singleton 7), some (.singleton 7), some (.singleton 7)⟩ ∧
    ∀ (items : List Nat) parameter interface,
      selectWorker committedPrefix items parameter interface = .directCode (constant (.singleton 7)) :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem duplicate_equations_keep_ambiguity_and_both_equal_occurrences :
    (Preparation.prepare Controls.duplicates).choices.branch ⟨false, false⟩ = none ∧
    Preparation.strictCode (Preparation.prepare Controls.duplicates) = none ∧
    Preparation.optionalTree (Preparation.prepare Controls.duplicates) = none ∧
    (match selectWorker Controls.duplicates ([] : List Nat) 0 with
      | .bodyCall .nonemptyProducer => true | _ => false) = true ∧
    executeWorker Nat.add (fun _ left _ => left) Controls.duplicates [] 0
      (selectWorker Controls.duplicates ([] : List Nat) 0) = some [[7], [7]] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [selected_worker_refines_source]
  rfl

theorem matched_failure_absence_and_returned_empty_remain_distinct :
    noMatch ⟨false, false⟩ Controls.failingMatch = false ∧
    Preparation.optionalBranch (Preparation.prepare Controls.failingMatch) ⟨false, false⟩ =
      some (some .callTail) ∧
    Preparation.optionalBranch (Preparation.prepare Controls.failingMatch) ⟨true, false⟩ =
      some none ∧
    source Nat.add (fun _ left _ => left) Controls.failingMatch ([] : List Nat) 0 = [] ∧
    source Nat.add (fun _ left _ => left)
      [⟨⟨.any, .any⟩, false, .empty⟩] ([] : List Nat) 0 = [[]] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def committedFailure : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .callTail⟩, ⟨⟨.any, .any⟩, false, .singleton 9⟩]

theorem committed_failure_never_retargets_to_a_later_success :
    Preparation.strictCode (Preparation.prepare committedFailure) = none ∧
    Preparation.optionalBranch (Preparation.prepare committedFailure) ⟨false, false⟩ =
      some (some .callTail) ∧
    executeWorker Nat.add (fun _ left _ => left) committedFailure [] 0
      (selectWorker committedFailure ([] : List Nat) 0) = some [] :=
  ⟨rfl, rfl, rfl⟩

/-- Preparation inspects code, independently of the invocation's item values.
A value-only receiver still refuses the optional representation. -/
theorem optional_preparation_preserves_deferred_inputs_and_receiver :
    ∀ (items : List Nat) parameter,
      selectWorker OptionalControls.headProgram items parameter =
        .optionalCode ⟨none, some (.mapHead (.singleton 7)),
          none, some (.mapHead (.singleton 7))⟩ ∧
      ∀ tree, selectWorker OptionalControls.headProgram items parameter .singleValue ≠
        .optionalCode tree := by
  intro items parameter
  exact ⟨rfl, value_only_selector_refuses_optional _ _ _⟩

theorem recursive_preparation_and_current_source_validation :
    (∃ compiled, Preparation.strictCode (Preparation.prepare Controls.recursive) = some compiled ∧
      ∀ (items : List Nat) parameter,
        selectWorker Controls.recursive items parameter = .directCode compiled) ∧
    OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn Controls.recursiveWorld 0
        [⟨⟨.any, .any⟩, false, .singleton 7⟩])
      (OrderedDependencyStore.readStamp Controls.recursiveWorld 0) = false ∧
    (match checkedWorker Controls.recursiveWorld
        (OrderedDependencyStore.appendOwn Controls.recursiveWorld 0
          [⟨⟨.any, .any⟩, false, .singleton 7⟩]) 0 ([] : List Nat) 0 with
      | .bodyCall .producer => true | _ => false) = true := by
  obtain ⟨compiled, built, selected⟩ := Controls.recursive_worker_is_constructed
  exact ⟨⟨compiled, by simpa only [Preparation.strictCode_eq] using built, selected⟩,
    Controls.added_equation_refuses_old_direct_code⟩

#print axioms committed_body_compiles_while_discarded_source_is_unsupported
#print axioms duplicate_equations_keep_ambiguity_and_both_equal_occurrences
#print axioms matched_failure_absence_and_returned_empty_remain_distinct
#print axioms committed_failure_never_retargets_to_a_later_success
#print axioms optional_preparation_preserves_deferred_inputs_and_receiver
#print axioms recursive_preparation_and_current_source_validation

end PreparationControls

namespace AdmissionControls

/-- The same current class can have different future answer multiplicities. -/
def recursiveChoice : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.cons, .any⟩, false, .ifZero .callTail .callPredecessor⟩,
   ⟨⟨.cons, .zero⟩, false, .singleton 9⟩]

theorem equal_current_shapes_do_not_probe_distinct_recursive_futures :
    shape ([0] : List Nat) 1 = shape ([0, 1] : List Nat) 1 ∧
    sourceGrade recursiveChoice ([0] : List Nat) 1 = .one ∧
    sourceGrade recursiveChoice ([0, 1] : List Nat) 1 = .nonempty ∧
    source Nat.add (fun _ left _ => left) recursiveChoice [0] 1 = [[7]] ∧
    source Nat.add (fun _ left _ => left) recursiveChoice [0, 1] 1 = [[7], [9]] ∧
    (Preparation.prepare recursiveChoice).bounds.branch (shape ([0] : List Nat) 1) = .any ∧
    selectWorker recursiveChoice ([0] : List Nat) 1 = .bodyCall .producer ∧
    selectWorker recursiveChoice ([0, 1] : List Nat) 1 = .bodyCall .producer :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def knownAfterCall : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .callTail⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩]

/-- A known answer establishes nonemptiness even beside an unknown call.
Equal payloads remain separate source occurrences. -/
theorem known_alternative_gives_a_useful_nonempty_producer :
    (Preparation.prepare knownAfterCall).bounds.branch ⟨true, false⟩ = .nonempty ∧
    selectWorker knownAfterCall ([0] : List Nat) 0 = .bodyCall .nonemptyProducer ∧
    executeWorker Nat.add (fun _ left _ => left) knownAfterCall [0] 0
      (selectWorker knownAfterCall ([0] : List Nat) 0) = some [[7], [7]] := by
  refine ⟨rfl, rfl, ?_⟩
  rw [selected_worker_refines_source]
  rfl

/-- Unknown recursion supplies no nonfailure guarantee; commit cannot borrow
a later known answer. Current guards can still establish immediate failure. -/
theorem recursive_unknown_does_not_license_success_or_ignore_commit :
    (Preparation.analyze (Code.callPredecessor : Code Nat)).bounds.branch ⟨true, false⟩ = .zero ∧
    (Preparation.analyze (Code.callPredecessor : Code Nat)).bounds.branch ⟨true, true⟩ = .any ∧
    (Preparation.prepare PreparationControls.committedFailure).bounds.branch ⟨true, false⟩ = .any ∧
    selectWorker PreparationControls.committedFailure ([0] : List Nat) 0 .singleValue =
      .bodyCall .producer ∧
    sourceGrade PreparationControls.committedFailure ([0] : List Nat) 0 = .zero ∧
    source Nat.add (fun _ left _ => left) PreparationControls.committedFailure [0] 0 = [] ∧
    ¬ ConventionAllows .nonemptyProducer
      (source Nat.add (fun _ left _ => left) PreparationControls.committedFailure [0] 0).length :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by change ¬ 1 ≤ 0; decide⟩

#print axioms equal_current_shapes_do_not_probe_distinct_recursive_futures
#print axioms known_alternative_gives_a_useful_nonempty_producer
#print axioms recursive_unknown_does_not_license_success_or_ignore_commit

end AdmissionControls


/-! ## Immutable native-space snapshot to retained authored worker

This source instance uses an ordered one-result-per-occurrence projection.
Pages carry the actual captured source revision, not the revision of a handle
used to request a query. They provide projected values, never physical input
IDs. The worker is the existing BodyCall owned computation. Only its earned,
acknowledged completion can supply an append-only batch. Storage currency
neither supplies invocation permission nor proves a native implementation.
-/
namespace SpaceSnapshotWorker

open RevisionedStoreView

variable {StoreId Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

abbrev Call := BodyCallAdmission.Call construct callbackConstruct fallback (Context := Context)

structure State where
  pages : Snapshot.Prefix StoreId Input
  worker : Option (Call construct callbackConstruct fallback (Context := Context))
  cancelled : Bool := false

def begin {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context) :=
  ⟨Snapshot.start (Snapshot.capture source project), none, false⟩

/-- Once a worker starts, page requests cannot replace its captured input. -/
def fetch (count : Nat) (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) :=
  if state.cancelled || state.worker.isSome then state
  else { state with pages := Snapshot.fetch count state.pages }

def start (authored : List (Equation Output)) (parameter : Nat) (context : Context)
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :=
  if state.cancelled || state.worker.isSome then state
  else if Snapshot.ready state.pages then
    { state with worker := some (BodyCallAdmission.openCall construct callbackConstruct fallback
        authored state.pages.1 parameter context) }
  else state

def resume (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :=
  if state.cancelled then state else
    { state with worker := state.worker.map (BodyCallAdmission.resume
        construct callbackConstruct fallback quantum allowance accept charge) }

/-- Cancellation retains the saved packet for inspection, but closes its
publication and progress entrances. It is distinct from completed emptiness. -/
def cancel (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) :=
  { state with cancelled := true }

def schedule
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :=
  grants.foldl (fun saved grant => resume construct callbackConstruct fallback
    grant.1 grant.2.1 grant.2.2 (charge grant.1 grant.2.2) saved) state

/-- Reachability invariant obtained from paging and actual callback execution. -/
def Lawful (snapshot : RevisionedStoreView StoreId Nat Input)
    (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) : Prop :=
  Snapshot.Lawful snapshot state.pages ∧
    ∀ call, state.worker = some call → Snapshot.ready state.pages = true ∧
      BodyCallAdmission.captured construct callbackConstruct fallback authored snapshot.entries parameter call

def outputs {Entry : Type} (encode : List Output → Entry)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) : Option (List Entry) :=
  if state.cancelled then none else state.worker.bind fun call =>
    if BodyCallAdmission.complete construct callbackConstruct fallback call then
      some (call.2.2.context.1.map encode) else none

/-- Publication never polls or acknowledges a worker. Refusal retains its
whole actual packet, paid accounts, pending loan and completed prefix. -/
def append [DecidableEq StoreId] {Entry : Type} (current : RevisionedStoreView StoreId Nat Entry)
    (nextRevision : Nat) (encode : List Output → Entry)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context)) :=
  ((outputs construct callbackConstruct fallback encode state).bind fun rows =>
    Publication.publish current state.pages.2.captured.readToken [] rows nextRevision, state)

theorem begin_lawful {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) (authored : List (Equation Output)) (parameter : Nat) :
    Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter
      (begin construct callbackConstruct fallback source project (Context := Context)) := by
  exact ⟨Snapshot.start_lawful _, by simp [begin]⟩

theorem fetch_lawful (count : Nat) (snapshot : RevisionedStoreView StoreId Nat Input)
    (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (fetch construct callbackConstruct fallback count state) := by
  unfold fetch
  split
  · exact safe
  · rename_i unused
    have absent : state.worker = none := by
      cases present : state.worker <;> simp_all
    exact ⟨Snapshot.fetch_lawful count snapshot state.pages safe.1, by simp [absent]⟩

theorem start_lawful (snapshot : RevisionedStoreView StoreId Nat Input)
    (authored : List (Equation Output)) (parameter : Nat) (context : Context)
    (state : State construct callbackConstruct fallback (StoreId := StoreId))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (start construct callbackConstruct fallback authored parameter context state) := by
  unfold start
  split
  · exact safe
  · split
    · rename_i completed
      refine ⟨safe.1, ?_⟩
      intro call held
      have equal : call = BodyCallAdmission.openCall construct callbackConstruct fallback authored
          state.pages.1 parameter context := (Option.some.inj held).symm
      subst call
      refine ⟨completed, ?_⟩
      rw [Snapshot.completed_rows snapshot state.pages safe.1 completed]
      exact BodyCallAdmission.open_captured construct callbackConstruct fallback authored snapshot.entries parameter context
    · exact safe

theorem resume_lawful (quantum allowance : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (resume construct callbackConstruct fallback quantum allowance accept charge state) := by
  unfold resume
  split
  · exact safe
  · refine ⟨safe.1, ?_⟩
    intro call held
    obtain ⟨previous, present, equal⟩ := Option.map_eq_some_iff.mp held
    subst call
    obtain ⟨ready, captured⟩ := safe.2 previous present
    exact ⟨ready, BodyCallAdmission.resume_captured construct callbackConstruct fallback quantum allowance
      accept charge authored snapshot.entries parameter previous captured⟩

theorem schedule_lawful
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state) :
    Lawful construct callbackConstruct fallback snapshot authored parameter
      (schedule construct callbackConstruct fallback charge grants state) := by
  induction grants generalizing state with
  | nil => exact safe
  | cons grant rest ih =>
      exact ih _ (resume_lawful construct callbackConstruct fallback grant.1 grant.2.1 grant.2.2
        (charge grant.1 grant.2.2) snapshot authored parameter state safe)

theorem schedule_split
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (first second : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) :
    schedule construct callbackConstruct fallback charge second
      (schedule construct callbackConstruct fallback charge first state) =
    schedule construct callbackConstruct fallback charge (first ++ second) state := by
  simp [schedule, List.foldl_append]

/-- This equality is discharged from the actual source invariant, not supplied
as a coefficient, output-list or accepted-source assumption. -/
theorem outputs_source {Entry : Type} (encode : List Output → Entry)
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state)
    (rows : List Entry) (completed : outputs construct callbackConstruct fallback encode state = some rows) :
    rows = (source construct callbackConstruct authored snapshot.entries parameter).map encode := by
  unfold outputs at completed
  split at completed
  · contradiction
  · obtain ⟨call, held, result⟩ := Option.bind_eq_some_iff.mp completed
    split at result
    · rename_i finished
      obtain ⟨_, captured⟩ := safe.2 call held
      have independent := captured.2.2
      rw [BodyCallAdmission.completed_view construct callbackConstruct fallback call captured.2.1 finished] at independent
      exact (Option.some.inj result).symm.trans (congrArg (List.map encode) independent)
    · contradiction

theorem append_source [DecidableEq StoreId] {Entry : Type} (encode : List Output → Entry)
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state)
    (current result : RevisionedStoreView StoreId Nat Entry) (nextRevision : Nat)
    (accepted : (append construct callbackConstruct fallback current nextRevision encode state).1 = some result) :
    snapshot.readToken = current.readToken ∧ nextRevision ≠ current.revision ∧
      result = current.replaceRevision nextRevision
        (current.entries ++ (source construct callbackConstruct authored snapshot.entries parameter).map encode) := by
  obtain ⟨rows, completed, published⟩ := Option.bind_eq_some_iff.mp accepted
  rw [Snapshot.append_only] at published
  split at published
  · rename_i admitted
    have same := outputs_source construct callbackConstruct fallback encode snapshot authored parameter state safe rows completed
    exact ⟨safe.1.1 ▸ admitted.1, admitted.2, by simpa [same] using (Option.some.inj published).symm⟩
  · contradiction

theorem stale_append_refused [DecidableEq StoreId] {Entry : Type} (encode : List Output → Entry)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (current : RevisionedStoreView StoreId Nat Entry) (nextRevision : Nat)
    (stale : state.pages.2.captured.readToken ≠ current.readToken) :
    append construct callbackConstruct fallback current nextRevision encode state = (none, state) := by
  apply Prod.ext
  · simp only [append]
    cases produced : outputs construct callbackConstruct fallback encode state <;>
      simp [Snapshot.append_only, stale]
  · rfl


/-- All page grants are consumed by the existing cursor before worker entry.
Insufficient pages leave the worker absent; no truncated input is executed. -/
def prepare {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) (pageGrants : List Nat)
    (authored : List (Equation Output)) (parameter : Nat) (context : Context) :=
  start construct callbackConstruct fallback authored parameter context
    (pageGrants.foldl (fun state count => fetch construct callbackConstruct fallback count state)
      (begin construct callbackConstruct fallback source project))

theorem prepare_lawful {Entry : Type} (source : RevisionedStoreView StoreId Nat Entry)
    (project : Entry → Option Input) (pageGrants : List Nat)
    (authored : List (Equation Output)) (parameter : Nat) (context : Context) :
    Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter
      (prepare construct callbackConstruct fallback source project pageGrants authored parameter context) := by
  apply start_lawful
  have preserved : ∀ state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context),
      Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter state →
      Lawful construct callbackConstruct fallback (Snapshot.capture source project) authored parameter
        (pageGrants.foldl (fun saved count => fetch construct callbackConstruct fallback count saved) state) := by
    induction pageGrants with
    | nil => exact fun _ safe => safe
    | cons count rest ih =>
        exact fun state safe => ih _
          (fetch_lawful construct callbackConstruct fallback count _ authored parameter state safe)
  exact preserved _ (begin_lawful construct callbackConstruct fallback source project authored parameter)

/-- An arbitrary actual callback/refusal schedule after actual finite paging
has the independently authored source as its completed output meaning. -/
theorem prepared_completed_source {Entry Result : Type}
    (sourceView : RevisionedStoreView StoreId Nat Entry) (project : Entry → Option Input)
    (pageGrants : List Nat) (authored : List (Equation Output)) (parameter : Nat) (context : Context)
    (charge : ∀ quantum (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context),
      Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (grants : List (BodyCallAdmission.Grant construct callbackConstruct fallback (Context := Context)))
    (encode : List Output → Result) (rows : List Result)
    (completed : outputs construct callbackConstruct fallback encode
      (schedule construct callbackConstruct fallback charge grants
        (prepare construct callbackConstruct fallback sourceView project pageGrants authored parameter context)) = some rows) :
    rows = (source construct callbackConstruct authored (sourceView.entries.filterMap project) parameter).map encode :=
  outputs_source construct callbackConstruct fallback encode _ authored parameter _
    (schedule_lawful construct callbackConstruct fallback charge grants _ authored parameter _
      (prepare_lawful construct callbackConstruct fallback sourceView project pageGrants authored parameter context)) rows completed

/-- The four existing result conventions constrain outer occurrences; the
encoding cannot erase equal answers or a returned empty collection. -/
theorem completed_mode_license {Entry : Type} (encode : List Output → Entry)
    (snapshot : RevisionedStoreView StoreId Nat Input) (authored : List (Equation Output)) (parameter : Nat)
    (state : State construct callbackConstruct fallback (StoreId := StoreId) (Context := Context))
    (safe : Lawful construct callbackConstruct fallback snapshot authored parameter state)
    (rows : List Entry) (completed : outputs construct callbackConstruct fallback encode state = some rows)
    (requested : CallingConvention) (interface : ScalarResultInterface)
    (eligible : BodyCallAdmission.modeEligible requested
      (BodyCallAdmission.workerMode (selectWorker authored snapshot.entries parameter interface)) interface = true) :
    ConventionAllows requested rows.length := by
  rw [outputs_source construct callbackConstruct fallback encode snapshot authored parameter state safe rows completed,
    List.length_map]
  exact BodyCallAdmission.modeEligible_sound _ _ _ _ eligible
    (BodyCallAdmission.selected_mode_sound construct callbackConstruct authored snapshot.entries parameter interface)

theorem zero_and_cancelled_entrances (quantum : Nat)
    (accept : Context → BodyCallOwned.Returned construct callbackConstruct fallback → Bool × Context)
    (charge : Cursor.Charge (BodyCallOwned.provider construct callbackConstruct fallback quantum accept))
    (state : State construct callbackConstruct fallback (StoreId := StoreId)) (count allowance : Nat)
    {Entry : Type} (encode : List Output → Entry) :
    fetch construct callbackConstruct fallback 0 state = state ∧
    resume construct callbackConstruct fallback quantum 0 accept charge state = state ∧
    fetch construct callbackConstruct fallback count (cancel construct callbackConstruct fallback state) =
      cancel construct callbackConstruct fallback state ∧
    resume construct callbackConstruct fallback quantum allowance accept charge
      (cancel construct callbackConstruct fallback state) = cancel construct callbackConstruct fallback state ∧
    outputs construct callbackConstruct fallback encode (cancel construct callbackConstruct fallback state) = none := by
  constructor
  · unfold fetch
    split <;> rfl
  constructor
  · unfold resume
    split
    · rfl
    · cases state with
      | mk pages worker cancelled =>
          cases worker <;> simp [BodyCallAdmission.resume_zero]
  · simp [fetch, resume, cancel, outputs]

#print axioms prepare_lawful
#print axioms prepared_completed_source
#print axioms completed_mode_license
#print axioms zero_and_cancelled_entrances

#print axioms begin_lawful
#print axioms fetch_lawful
#print axioms start_lawful
#print axioms resume_lawful
#print axioms schedule_lawful
#print axioms schedule_split
#print axioms outputs_source
#print axioms append_source
#print axioms stale_append_refused

end SpaceSnapshotWorker

/-! ## Checked publication of closed and open weighted returns

The source is the existing authored weighted Call. Ordinary completion
publishes its complete records separately; a genuine handoff publishes one
observation with the captured prefix and the same retained Call. A source
pause supplies no publication packet. The finite publication provider neither
re-enters source syntax nor interprets the returned records' conditions.
-/
namespace BodyCallWeighted.Authored.Publication

open Cursor.Fold.OwnedSequence.CallbackBoundary

variable {Input Output Weight Context Term Environment Consumer : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)

local notation "selected" => selection attachment
local notation "Row" => BodyCall.WeightedSource.Row Output Weight
local notation "Record" => Cursor.Fold.OwnedSequence.Returned Term Environment
local notation "SourceCall" => Compact.Attachment.Call construct callbackConstruct fallback selected
  (Context := List Row × Context)
local notation "Loan" => Compact.Attachment.SparseReturned construct callbackConstruct fallback selected
local notation "OpenReturn" => Record × (List Record × SourceCall)
local notation "Item" => Record ⊕ OpenReturn


/-- Only an acknowledged producer-finished cut supplies a closed batch.
A genuine handoff retains both the observed prefix and the original Call.
Pending loans, intermediate yields and source pauses remain unpublished here. -/
def reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall) : NextReply (List Record) OpenReturn :=
  if Compact.Attachment.complete construct callbackConstruct fallback selected call then
    .returned (call.2.2.context.2.1.map record)
  else match BodyCallShared.Weighted.inspect construct callbackConstruct fallback selected call with
    | .handoff _ _ => .terminal (observe call, call.2.2.context.2.1.map record, call)
    | _ => .paused

theorem closed_reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true) :
    reply construct callbackConstruct fallback attachment record observe call =
      .returned (call.2.2.context.2.1.map record) := by
  simp [reply, finished]

theorem handoff_reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall) (loan : Loan)
    (handed : BodyCallShared.Weighted.inspect construct callbackConstruct fallback selected call =
      .handoff loan call) :
    reply construct callbackConstruct fallback attachment record observe call =
      .terminal (observe call, call.2.2.context.2.1.map record, call) := by
  by_cases finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true
  · simp [BodyCallShared.Weighted.inspect, finished] at handed
  · simp [reply, finished, handed]

/-- A grant can finish without supplying either a closed bag or an open stop.
The paused source remains with its caller, rather than becoming an Observation. -/
theorem running_reply (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall)
    (running : call.2.1.terminal = none) (noLoan : call.2.1.pending = none) :
    reply construct callbackConstruct fallback attachment record observe call = .paused := by
  simp [reply, Compact.Attachment.complete, Compact.Attachment.eraseCall,
    BodyCallAdmission.complete, BodyCallShared.Weighted.inspect, running, noLoan]

/-- The concrete publisher preserves the exact source and the independent
weighted meaning while partitioning complete return records. No answer
equality is supplied by the publication checker. -/
theorem closed_partition (record : Row → Record) (call : SourceCall)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (captured : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call
        (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer)
    later.2.2.1 = call ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
          (fun row => Sum.inl (record row)) := by
  have actual := completed_source construct callbackConstruct fallback attachment
    authored items parameter call captured finished
  simpa [FrozenPublication.records, actual, List.map_map, Function.comp_def] using
    FrozenPublication.schedule_partition check grants call
      (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer

/-- Entry and actual source grants construct the source invariant. The only
completion premise is the real finished cut, not the number of granted steps. -/
theorem actual_closed_partition (record : Row → Record)
    (sourceGrants : List (Grant construct callbackConstruct fallback attachment (Context := Context)))
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat) (context : Context)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let call := Compact.Attachment.schedule construct callbackConstruct fallback selected
      (readGrants construct callbackConstruct fallback attachment sourceGrants)
      (Compact.Attachment.openCall construct callbackConstruct fallback selected authored items parameter ([], context))
    Compact.Attachment.complete construct callbackConstruct fallback selected call = true →
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call
        (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer)
    later.2.2.1 = call ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
          (fun row => Sum.inl (record row)) := by
  intro call finished
  exact closed_partition construct callbackConstruct fallback attachment record call authored items parameter
    (schedule_captured construct callbackConstruct fallback attachment sourceGrants authored items parameter _
      (open_captured construct callbackConstruct fallback attachment authored items parameter context))
    finished check grants consumer

/-- Finishing the checked suffix, including the zero-row case, exposes exactly
the independent source records. Source closure alone does not discharge these
two consumer-side obligations. -/
theorem closed_drained (record : Row → Record) (call : SourceCall)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (captured : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (finished : Compact.Attachment.complete construct callbackConstruct fallback selected call = true)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call
        (FrozenPublication.records (Observation := OpenReturn) (.inl (call.2.2.context.2.1.map record))) consumer)
    later.2.2.2.pending = none → later.2.2.2.remaining = [] →
      later.2.2.2.accumulator.1 =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
          (fun row => Sum.inl (record row)) := by
  intro later noLoan noRows
  have conserved := (closed_partition construct callbackConstruct fallback attachment record call
    authored items parameter captured finished check grants consumer).2
  change later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining =
    (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map
      (fun row => Sum.inl (record row)) at conserved
  simpa only [noLoan, noRows, Option.toList_none, List.append_nil] using conserved

/-- The singleton open reply retains the full actual residual. Its observed
prefix plus that residual equals the independent weighted source; publication
refusals preserve both parts without an additional source step. -/
theorem open_partition (record : Row → Record) (observe : SourceCall → Record)
    (call : SourceCall)
    (authored : List (Equation Output)) (items : List Input) (parameter : Nat)
    (captured : Captured construct callbackConstruct fallback attachment authored items parameter call)
    (loan : Loan)
    (handed : BodyCallShared.Weighted.inspect construct callbackConstruct fallback selected call =
      .handoff loan call)
    (check : Consumer → Item → Bool × Consumer) (grants : List Nat) (consumer : Consumer) :
    let packet : OpenReturn := (observe call, call.2.2.context.2.1.map record, call)
    FrozenPublication.prepare call consumer
        (reply construct callbackConstruct fallback attachment record observe call) =
      some (FrozenPublication.start call [Sum.inr packet] consumer) ∧
    let later := FrozenPublication.schedule check grants
      (FrozenPublication.start call [Sum.inr packet] consumer)
    later.2.2.1 = call ∧
      later.2.2.2.accumulator.1 ++ later.2.2.2.pending.toList ++ later.2.2.2.remaining = [Sum.inr packet] ∧
      packet.2.1 ++ (unaccepted construct callbackConstruct fallback attachment call.2.2.computation.2).map record =
        (BodyCall.WeightedSource.source construct callbackConstruct attachment authored items parameter).map record := by
  intro packet
  constructor
  · rw [handoff_reply construct callbackConstruct fallback attachment record observe call loan handed]
    rfl
  · have kept := FrozenPublication.schedule_partition check grants call [Sum.inr packet] consumer
    refine ⟨kept.1, kept.2, ?_⟩
    simpa [packet, view, List.map_append] using congrArg (List.map record) captured.2.2

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls
  (build callback noFallback)

private def encode (row : BodyCall.WeightedSource.Row Nat Nat) :
    Cursor.Fold.OwnedSequence.Returned (BodyCall.WeightedSource.Row Nat Nat) Nat :=
  ⟨row, if row.2 = [2, 3] then 11 else 22, .completed, [row]⟩

private def observation (_ : Compact.Attachment.Call build callback noFallback
    (selection Authored.Controls.branches)
    (Context := List (BodyCall.WeightedSource.Row Nat Nat) × Unit)) :
    Cursor.Fold.OwnedSequence.Returned (BodyCall.WeightedSource.Row Nat Nat) Nat :=
  ⟨([99], []), 71, .completed, []⟩

/-- Equal answer values keep distinct coefficient words and complete records.
The finished-failure control is a zero-row bag, not one empty collection. -/
theorem actual_closed_records_and_zero_bag :
    (match reply build callback noFallback Authored.Controls.branches encode observation
        Authored.Controls.equalBranches with
      | .returned rows => some rows
      | _ => none) = some [encode ([7], [2, 3]), encode ([7], [2, 5])] ∧
    (match reply build callback noFallback Authored.Controls.branches encode observation
        Authored.Controls.committedResult with
      | .returned rows => some rows
      | _ => none) = some [] := by decide

private def unfinished := Compact.Attachment.resumeCallSource build callback noFallback
  (selection Authored.Controls.branches) 0 1
  (reader build callback noFallback Authored.Controls.branches (fun (_ : Unit) _ => (true, ())))
  (Compact.Attachment.openCall build callback noFallback (selection Authored.Controls.branches)
    BodyCallShared.Weighted.Controls.authored [0] 0 ([], ()))

theorem zero_source_grant_is_neither_closed_nor_an_observation :
    (match reply build callback noFallback Authored.Controls.branches encode observation unfinished with
      | .paused => false
      | _ => true) = false ∧
    Compact.Attachment.complete build callback noFallback (selection Authored.Controls.branches) unfinished = false := by
  decide

private def handoffProgram : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .unsupported⟩]

private def handedOff := Authored.Controls.accepted Authored.Controls.branches handoffProgram []

theorem actual_handoff_is_one_observation_with_earned_prefix :
    (match reply build callback noFallback Authored.Controls.branches encode observation handedOff with
      | .terminal (observed, rows, retained) =>
          some (observed.environment, rows, retained.2.2.context.2.1)
      | _ => none) = some (71, [encode ([7], [2])], [([7], [2])]) ∧
    Compact.Attachment.complete build callback noFallback (selection Authored.Controls.branches) handedOff = false := by
  constructor <;> rfl

end Controls

#print axioms closed_reply
#print axioms handoff_reply
#print axioms running_reply
#print axioms closed_partition
#print axioms actual_closed_partition
#print axioms closed_drained
#print axioms open_partition
#print axioms Controls.actual_closed_records_and_zero_bag
#print axioms Controls.zero_source_grant_is_neither_closed_nor_an_observation
#print axioms Controls.actual_handoff_is_one_observation_with_earned_prefix

end BodyCallWeighted.Authored.Publication

end Mettapedia.Machines.SourceProducerCardinality
