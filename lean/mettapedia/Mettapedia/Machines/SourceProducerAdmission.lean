import Mettapedia.Machines.RecursiveFiniteProducer
import Mettapedia.Machines.EquationCut
import Mettapedia.Machines.AnswerCardinality
import Mathlib.Tactic.Linarith
import Mettapedia.Algebra.SharedCoefficientLedger
import Mettapedia.GSLT.Core.WeightedMuScheduler

/-!
# Ordered equation admission for recursive collection producers

The source is an explicitly scope-resolved equation IR. Its list patterns are
wildcard, empty and head/tail; its numeric patterns are wildcard and zero.
Self, the current list, its head/tail, and the numeric parameter are lexical
roles, not recognized function or variable spellings. Mapping named MeTTa
syntax, authored plans and unification into this IR is a separate obligation.

Source evaluation keeps every matching uncommitted equation and the Cartesian
product of collection-valued recursive answers. An entry cut commits only its
current invocation. The compiler checks every input-shape class, refusing
overlapping uncommitted alternatives and unguarded recursive operations. Its
result is one shared `RecursiveFiniteProducer.Code`, not an expanded tree.

The source body uses the existing local instruction grammar, interpreted
independently: its recursive calls re-enter the ordered source equations,
whereas compiled recursive calls re-enter the compiled decision tree.

`RetainedFrontier` is the coarse equation observer. It keeps every authored
equation and that invocation's captured items and parameter, then publishes
one matched equation through `bodyResults`. `tailResults` is supplied already
computed. That observer is not the execution cursor.

`BodyCall` is the execution cursor. One step runs one existing `Frame`
instruction, parks the right code of an append, and pushes a fresh authored
invocation on a call. It does not call `bodyResults`, `source`, or `sourceTail`.
`.decline` keeps the whole stack. `.unsupported` hands its frame off.
Under `.observe .noAnswers`, the cursor preserves ordered emitted occurrences
and the source meaning of every retained continuation. A finished bounded run
equals the complete source result. `optionalSupported` excludes handoff code
for completion arguments; the batch clause for `.unsupported` remains `[]`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceProducerAdmission

open RecursiveFiniteProducer

universe u v
variable {Item : Type u} {Value : Type v}

inductive ListHead where
  | any | empty | cons
deriving DecidableEq, Repr

inductive NumberHead where
  | any | zero
deriving DecidableEq, Repr

structure Head where
  list : ListHead
  number : NumberHead
deriving DecidableEq, Repr

structure Shape where
  nonempty : Bool
  positive : Bool
deriving DecidableEq, Repr

def shape (items : List Item) (parameter : Nat) : Shape :=
  ⟨!items.isEmpty, parameter != 0⟩

/-- Matching the actual source arguments, independently of the compiler's
four abstract input classes. All variables in this IR are distinct binders. -/
def Head.matches (head : Head) (items : List Item) (parameter : Nat) : Bool :=
  (match head.list, items with
    | .any, _ | .empty, [] | .cons, _ :: _ => true
    | _, _ => false) &&
  (match head.number with
    | .any => true
    | .zero => parameter == 0)

def Head.accepts (head : Head) (input : Shape) : Bool :=
  (match head.list with
    | .any => true
    | .empty => !input.nonempty
    | .cons => input.nonempty) &&
  (match head.number with
    | .any => true
    | .zero => !input.positive)

theorem Head.matches_eq_accepts (head : Head) (items : List Item) (parameter : Nat) :
    head.matches items parameter = head.accepts (shape items parameter) := by
  rcases head with ⟨list, number⟩
  cases list <;> cases number <;> cases items <;> cases parameter <;> rfl

structure Equation (Value : Type v) where
  head : Head
  commit : Bool
  body : Code Value
deriving Repr

/-- Complete eager body results. The outer list records derivation
occurrences; each inner list is one returned collection. -/
def bodyResults (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (items : List Item) (parameter : Nat) :
    Code Value → List (List Value)
  | .empty => [[]]
  | .singleton value => [[value]]
  | .append left right =>
      (bodyResults construct callbackConstruct tailResults items parameter left).flatMap
        (fun first =>
          (bodyResults construct callbackConstruct tailResults items parameter right).map
            (fun second => first ++ second))
  | .mapHead body =>
      match items with
      | [] => []
      | head :: tail =>
          (bodyResults construct callbackConstruct tailResults (head :: tail) parameter body).map
            (List.map (construct head))
  | .map callback body =>
      (bodyResults construct callbackConstruct tailResults items parameter body).map
        (List.map (callback.run callbackConstruct))
  | .ifZero yes no =>
      if parameter = 0 then bodyResults construct callbackConstruct tailResults items parameter yes
      else bodyResults construct callbackConstruct tailResults items parameter no
  | .ifEmpty yes no =>
      if items = [] then bodyResults construct callbackConstruct tailResults items parameter yes
      else bodyResults construct callbackConstruct tailResults items parameter no
  | .callTail =>
      match items with
      | [] => []
      | _ :: _ => tailResults parameter
  | .callPredecessor =>
      match items, parameter with
      | _ :: _, count + 1 => tailResults count
      | _, _ => []
  | .unsupported => []

/-- Ordered, invocation-local commitment. Even a failing committed body
discards later equations. An uncommitted empty collection is one answer,
not failure; it must not erase its later alternatives. -/
def equationsResults (matchesHead : Head → Bool) (runBody : Code Value → List (List Value)) :
    List (Equation Value) → List (List Value)
  | [] => []
  | equation :: rest =>
      if matchesHead equation.head then
        if equation.commit then runBody equation.body
        else runBody equation.body ++ equationsResults matchesHead runBody rest
      else equationsResults matchesHead runBody rest

/-- Recursive source execution eagerly obtains all answers from each tail
call before constructing the enclosing collection. -/
def source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value)) :
    List Item → Nat → List (List Value)
  | [], parameter =>
      equationsResults (fun head => head.matches ([] : List Item) parameter)
        (bodyResults construct callbackConstruct (fun _ => []) [] parameter) program
  | head :: tail, parameter =>
      equationsResults (fun pattern => pattern.matches (head :: tail) parameter)
        (bodyResults construct callbackConstruct
          (source construct callbackConstruct program tail) (head :: tail) parameter) program

def noMatch (input : Shape) (program : List (Equation Value)) : Bool :=
  program.all (fun equation => !equation.head.accepts input)

/-- Select the only observable equation, allowing an earlier entry cut to
discard later overlapping heads. No semantic singleton/purity claim is an
input to this check. -/
def select (input : Shape) : List (Equation Value) → Option (Code Value)
  | [] => none
  | equation :: rest =>
      if equation.head.accepts input then
        if equation.commit || noMatch input rest then some equation.body else none
      else select input rest

theorem equationsResults_noMatch (input : Shape) (program : List (Equation Value))
    (runBody : Code Value → List (List Value)) (absent : noMatch input program = true) :
    equationsResults (fun head => head.accepts input) runBody program = [] := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      simp only [noMatch, List.all_cons, Bool.and_eq_true] at absent
      have unmatched : equation.head.accepts input = false := by
        cases h : equation.head.accepts input <;> simp_all
      simp [equationsResults, unmatched, ih absent.2]

theorem select_sound (input : Shape) (program : List (Equation Value))
    (body : Code Value) (selected : select input program = some body)
    (runBody : Code Value → List (List Value)) :
    equationsResults (fun head => head.accepts input) runBody program = runBody body := by
  induction program with
  | nil => simp [select] at selected
  | cons equation rest ih =>
      by_cases matched : equation.head.accepts input = true
      · simp only [select, matched, ↓reduceIte] at selected
        split at selected
        next accepted =>
          cases selected
          cases committed : equation.commit with
          | true => simp [equationsResults, matched, committed]
          | false =>
              have absent : noMatch input rest = true := by simpa [committed] using accepted
              simp [equationsResults, matched, committed,
                equationsResults_noMatch input rest runBody absent]
        next rejected => simp at selected
      · have unmatched : equation.head.accepts input = false := by simpa using matched
        simp only [select, unmatched, Bool.false_eq_true, ↓reduceIte] at selected
        simpa [equationsResults, unmatched] using ih selected

structure ShapeTree (Branch : Type v) where
  zeroEmpty : Branch
  zeroCons : Branch
  positiveEmpty : Branch
  positiveCons : Branch
deriving Repr

def ShapeTree.branch {Branch : Type v} (tree : ShapeTree Branch) (input : Shape) : Branch :=
  if input.positive then
    if input.nonempty then tree.positiveCons else tree.positiveEmpty
  else
    if input.nonempty then tree.zeroCons else tree.zeroEmpty

abbrev DecisionTree (Value : Type v) := ShapeTree (Code Value)

def DecisionTree.branch (tree : DecisionTree Value) (input : Shape) : Code Value :=
  ShapeTree.branch tree input

def DecisionTree.code (tree : DecisionTree Value) : Code Value :=
  .ifZero (.ifEmpty tree.zeroEmpty tree.zeroCons)
    (.ifEmpty tree.positiveEmpty tree.positiveCons)

def compileBranch (input : Shape) (program : List (Equation Value)) : Option (Code Value) := do
  let body ← select input program
  if check input.nonempty input.positive body then some body else none

def compileTree (program : List (Equation Value)) : Option (DecisionTree Value) := do
  let zeroEmpty ← compileBranch ⟨false, false⟩ program
  let zeroCons ← compileBranch ⟨true, false⟩ program
  let positiveEmpty ← compileBranch ⟨false, true⟩ program
  let positiveCons ← compileBranch ⟨true, true⟩ program
  pure ⟨zeroEmpty, zeroCons, positiveEmpty, positiveCons⟩

def compile (program : List (Equation Value)) : Option (Code Value) :=
  (compileTree program).map DecisionTree.code

theorem compileBranch_sound (input : Shape) (program : List (Equation Value))
    (body : Code Value) (accepted : compileBranch input program = some body) :
    select input program = some body ∧ check input.nonempty input.positive body = true := by
  unfold compileBranch at accepted
  cases selected : select input program with
  | none => simp [selected] at accepted
  | some selectedBody =>
      simp [selected] at accepted
      rcases accepted with ⟨good, rfl⟩
      exact ⟨rfl, good⟩

theorem compileTree_branches (program : List (Equation Value)) (tree : DecisionTree Value)
    (accepted : compileTree program = some tree) (input : Shape) :
    compileBranch input program = some (tree.branch input) := by
  unfold compileTree at accepted
  cases he : compileBranch ⟨false, false⟩ program <;> simp [he] at accepted
  rename_i ze
  cases hc : compileBranch ⟨true, false⟩ program <;> simp [hc] at accepted
  rename_i zc
  cases pe : compileBranch ⟨false, true⟩ program <;> simp [pe] at accepted
  rename_i ne
  cases pc : compileBranch ⟨true, true⟩ program <;> simp [pc] at accepted
  rename_i nc
  cases accepted
  rcases input with ⟨nonempty, positive⟩
  cases nonempty <;> cases positive <;> simp_all [DecisionTree.branch, ShapeTree.branch]

theorem compileTree_checked (program : List (Equation Value)) (tree : DecisionTree Value)
    (accepted : compileTree program = some tree) : check false false tree.code = true := by
  have ze := (compileBranch_sound _ _ _
    (compileTree_branches program tree accepted ⟨false, false⟩)).2
  have zc := (compileBranch_sound _ _ _
    (compileTree_branches program tree accepted ⟨true, false⟩)).2
  have pe := (compileBranch_sound _ _ _
    (compileTree_branches program tree accepted ⟨false, true⟩)).2
  have pc := (compileBranch_sound _ _ _
    (compileTree_branches program tree accepted ⟨true, true⟩)).2
  simpa [DecisionTree.code, DecisionTree.branch, ShapeTree.branch, check] using
    And.intro (And.intro ze zc) (And.intro pe pc)

/-- Once recursive tail calls agree, the eager relational source body has
exactly the compiled body's single collection. This is an induction through
Cartesian products and complete maps, not a list-prefix assumption. -/
theorem bodyResults_of_eager (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (compiled : Code Value)
    (items : List Item) (parameter : Nat) (tailResults : Nat → List (List Value))
    (tailCorrect : ∀ head tail, items = head :: tail → ∀ count result,
      eager construct callbackConstruct compiled tail count compiled = some result →
        tailResults count = [result]) (body : Code Value) (result : List Value)
    (done : eager construct callbackConstruct compiled items parameter body = some result) :
    bodyResults construct callbackConstruct tailResults items parameter body = [result] := by
  induction body generalizing result with
  | empty =>
      simp only [eager, Option.some.injEq] at done
      subst result
      rfl
  | singleton value =>
      simp only [eager, Option.some.injEq] at done
      subst result
      rfl
  | append left right leftIH rightIH =>
      cases first : eager construct callbackConstruct compiled items parameter left with
      | none => simp [eager, first] at done
      | some earlier =>
          cases second : eager construct callbackConstruct compiled items parameter right with
          | none => simp [eager, first, second] at done
          | some later =>
              simp [eager, first, second] at done
              subst result
              simp [bodyResults, leftIH _ first, rightIH _ second]
  | mapHead body ih =>
      cases items with
      | nil => simp [eager] at done
      | cons head tail =>
          cases answer : eager construct callbackConstruct compiled (head :: tail) parameter body with
          | none => simp [eager, answer] at done
          | some values =>
              simp [eager, answer] at done
              subst result
              simp [bodyResults, ih _ answer]
  | map callback body ih =>
      cases answer : eager construct callbackConstruct compiled items parameter body with
      | none => simp [eager, answer] at done
      | some values =>
          simp [eager, answer] at done
          subst result
          simp [bodyResults, ih _ answer]
  | ifZero yes no yesIH noIH =>
      by_cases zero : parameter = 0
      · rw [eager, if_pos zero] at done
        simpa [bodyResults, zero] using yesIH result done
      · rw [eager, if_neg zero] at done
        simpa [bodyResults, zero] using noIH result done
  | ifEmpty yes no yesIH noIH =>
      by_cases empty : items = []
      · rw [eager, if_pos empty] at done
        simpa [bodyResults, empty] using yesIH result done
      · rw [eager, if_neg empty] at done
        simpa [bodyResults, empty] using noIH result done
  | callTail =>
      cases items with
      | nil => simp [eager] at done
      | cons head tail =>
          exact tailCorrect head tail rfl parameter result (by simpa [eager] using done)
  | callPredecessor =>
      cases items with
      | nil => simp [eager] at done
      | cons head tail =>
          cases parameter with
          | zero => simp [eager] at done
          | succ count =>
              exact tailCorrect head tail rfl count result (by simpa [eager] using done)
  | unsupported => simp [eager] at done

theorem DecisionTree.eager_branch (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (tree : DecisionTree Value)
    (items : List Item) (parameter : Nat) :
    eager construct callbackConstruct tree.code items parameter tree.code =
      eager construct callbackConstruct tree.code items parameter
        (tree.branch (shape items parameter)) := by
  cases items <;> cases parameter <;>
    simp [DecisionTree.code, DecisionTree.branch, ShapeTree.branch, shape, eager]

theorem source_equations_shape (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    source construct callbackConstruct program items parameter =
      equationsResults (fun head => head.accepts (shape items parameter))
        (bodyResults construct callbackConstruct
          (match items with
            | [] => fun _ => []
            | _ :: tail => source construct callbackConstruct program tail)
          items parameter) program := by
  cases items <;> simp only [source, Head.matches_eq_accepts]

/-- Admission proves the source's complete eager relation has exactly one
collection, equal to the independently compiled recursive execution. The
source's local cuts, overlapping heads and list of alternatives are all
interpreted before the equality is established. -/
theorem compileTree_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value))
    (tree : DecisionTree Value) (accepted : compileTree program = some tree)
    (items : List Item) (parameter : Nat) :
    ∃ result,
      eager construct callbackConstruct tree.code items parameter tree.code = some result ∧
      source construct callbackConstruct program items parameter = [result] := by
  have checked := compileTree_checked program tree accepted
  induction items generalizing parameter with
  | nil =>
      obtain ⟨result, done⟩ := checked_eager_total construct callbackConstruct tree.code checked [] parameter
      refine ⟨result, done, ?_⟩
      rw [source_equations_shape]
      have selected := (compileBranch_sound _ _ _
        (compileTree_branches program tree accepted (shape ([] : List Item) parameter))).1
      rw [select_sound _ _ _ selected]
      exact bodyResults_of_eager construct callbackConstruct tree.code [] parameter (fun _ => [])
        (by intro head tail impossible; cases impossible) _ result
        (by rwa [DecisionTree.eager_branch] at done)
  | cons head tail ih =>
      obtain ⟨result, done⟩ := checked_eager_total construct callbackConstruct tree.code checked
        (head :: tail) parameter
      refine ⟨result, done, ?_⟩
      rw [source_equations_shape]
      have selected := (compileBranch_sound _ _ _
        (compileTree_branches program tree accepted (shape (head :: tail) parameter))).1
      rw [select_sound _ _ _ selected]
      apply bodyResults_of_eager construct callbackConstruct tree.code (head :: tail) parameter
        (source construct callbackConstruct program tail) ?_ _ result
        (by rwa [DecisionTree.eager_branch] at done)
      intro otherHead otherTail same count values evaluated
      cases same
      obtain ⟨actual, actualDone, actualSource⟩ := ih count
      rw [evaluated] at actualDone
      cases actualDone
      exact actualSource

theorem compile_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value))
    (compiled : Code Value) (accepted : compile program = some compiled)
    (items : List Item) (parameter : Nat) :
    check false false compiled = true ∧
      ∃ result,
        eager construct callbackConstruct compiled items parameter compiled = some result ∧
        source construct callbackConstruct program items parameter = [result] := by
  cases built : compileTree program with
  | none => simp [compile, built] at accepted
  | some tree =>
      simp [compile, built] at accepted
      subst compiled
      exact ⟨compileTree_checked program tree built,
        compileTree_source construct callbackConstruct program tree built items parameter⟩

/-- The compiler's checked equation selection composes with the executable
shared-code cursor: every bound preserves the requested occurrence prefix
of the source's unique complete collection. -/
theorem compile_bounded_correct (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (program : List (Equation Value))
    (compiled : Code Value) (accepted : compile program = some compiled)
    (items : List Item) (parameter : Nat) :
    ∃ result, source construct callbackConstruct program items parameter = [result] ∧
      ∀ bound, takePrefix construct callbackConstruct compiled bound
        (initial compiled items parameter) = some (result.take bound) := by
  obtain ⟨checked, result, done, sourceDone⟩ :=
    compile_source construct callbackConstruct program compiled accepted items parameter
  obtain ⟨actual, actualDone, prefixes⟩ :=
    checked_bounded_correct construct callbackConstruct compiled checked items parameter
  rw [done] at actualDone
  cases actualDone
  exact ⟨result, sourceDone, prefixes⟩

/-! The following comparison ties the source's entry-commit behavior to the
existing independent continuation and frame semantics. Complete body results
are primitives here; the theorem concerns head selection and cut scope. -/

def cutEquation (input : Shape) (runBody : Code Value → List (List Value))
    (equation : Equation Value) : EquationCut.Body (List Value) :=
  let body := EquationCut.Body.prim (fun _ => runBody equation.body) .done
  .branch (fun _ => equation.head.accepts input)
    (if equation.commit then .cut body else body)
    (.prim (fun _ => []) .done)

theorem cutEquation_eval (input : Shape) (runBody : Code Value → List (List Value))
    (equation : Equation Value) (initialValue : List Value)
    (pending saved : List (List Value)) :
    EquationCut.den (fun _ => []) 0 (cutEquation input runBody equation)
        initialValue (fun value rest => value :: rest) pending saved =
      if equation.head.accepts input then
        runBody equation.body ++ (if equation.commit then saved else pending)
      else pending := by
  cases matched : equation.head.accepts input <;> cases committed : equation.commit <;>
    simp [cutEquation, EquationCut.den, matched, committed]

/-- The saved caller alternatives survive a local entry cut. A later matching
source equation survives exactly when the earlier equation did not commit. -/
theorem equationsResults_eq_cut (input : Shape) (runBody : Code Value → List (List Value))
    (program : List (Equation Value)) (initialValue : List Value)
    (outside : List (List Value)) :
    EquationCut.equations (fun _ => []) 0 ((program.map (cutEquation input runBody)))
        initialValue (fun value rest => value :: rest) outside =
      equationsResults (fun head => head.accepts input) runBody program ++ outside := by
  induction program with
  | nil => simp [EquationCut.equations, equationsResults]
  | cons equation rest ih =>
      simp only [List.map_cons, EquationCut.equations, List.foldr_cons] at ih ⊢
      rw [cutEquation_eval]
      cases matched : equation.head.accepts input <;> cases committed : equation.commit <;>
        simp [equationsResults, matched, committed, ih, List.append_assoc]

namespace Examples

/-- The three overlapping heads and local cuts of include-first sublist
selection. Names are absent from this alpha-resolved presentation. -/
def combinations : List (Equation (List Item)) :=
  [⟨⟨.any, .zero⟩, true, .singleton []⟩,
   ⟨⟨.empty, .any⟩, true, .empty⟩,
   ⟨⟨.cons, .any⟩, false, .append (.mapHead .callPredecessor) .callTail⟩]

def combinationsTree : DecisionTree (List Item) :=
  ⟨.singleton [], .singleton [], .empty,
    .append (.mapHead .callPredecessor) .callTail⟩

theorem combinations_accepted :
    compile (combinations (Item := Item)) = some combinationsTree.code := rfl

theorem combinations_prefixes (callbackConstruct : Nat → List Item → List Item → List Item)
    (items : List Item) (parameter : Nat) :
    ∃ result, source List.cons callbackConstruct combinations items parameter = [result] ∧
      ∀ bound, takePrefix List.cons callbackConstruct combinationsTree.code bound
        (initial combinationsTree.code items parameter) = some (result.take bound) :=
  compile_bounded_correct List.cons callbackConstruct combinations combinationsTree.code
    combinations_accepted items parameter

/-- A second source family duplicates a tail call. Its head patterns are
disjoint, so no source cut is needed for deterministic collection production. -/
def repeated (value : Value) : List (Equation Value) :=
  [⟨⟨.empty, .any⟩, false, .singleton value⟩,
   ⟨⟨.cons, .any⟩, false, .append .callTail .callTail⟩]

def repeatedTree (value : Value) : DecisionTree Value :=
  ⟨.singleton value, .append .callTail .callTail,
    .singleton value, .append .callTail .callTail⟩

theorem repeated_accepted (value : Value) :
    compile (repeated value) = some (repeatedTree value).code := rfl

theorem repeated_source_cardinality (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (value : Value)
    (items : List Item) (parameter : Nat) :
    source construct callbackConstruct (repeated value) items parameter =
      [List.replicate (2 ^ items.length) value] := by
  induction items with
  | nil => simp [source, repeated, equationsResults, Head.matches, bodyResults]
  | cons head tail ih =>
      simp only [repeated] at ih
      simp [source, repeated, equationsResults, Head.matches, bodyResults, ih,
        Nat.pow_succ, Nat.mul_two]

/-- Without the base cuts, the overlapping source equations must retain
their alternatives. The compiler rejects this whole equation family. -/
def uncommittedCombinations : List (Equation (List Item)) :=
  (combinations (Item := Item)).map (fun equation => {equation with commit := false})

theorem uncommitted_rejected :
    compile (uncommittedCombinations (Item := Item)) = none := rfl

theorem overlap_has_two_collection_answers
    (callbackConstruct : Nat → List Item → List Item → List Item) :
    source List.cons callbackConstruct uncommittedCombinations ([] : List Item) 0 =
      [[[]], []] := rfl

theorem committed_overlap_keeps_first
    (callbackConstruct : Nat → List Item → List Item → List Item) :
    source List.cons callbackConstruct combinations ([] : List Item) 0 = [[[]]] := rfl

theorem swapping_committed_bases_changes_result
    (callbackConstruct : Nat → List Item → List Item → List Item) :
    source List.cons callbackConstruct
      [⟨⟨.empty, .any⟩, true, .empty⟩,
       ⟨⟨.any, .zero⟩, true, .singleton []⟩,
       ⟨⟨.cons, .any⟩, false, .append (.mapHead .callPredecessor) .callTail⟩]
      ([] : List Item) 0 = [[]] := rfl

theorem matching_body_without_positive_guard_rejected :
    compile ([⟨⟨.empty, .any⟩, false, .empty⟩,
      ⟨⟨.cons, .any⟩, false, .callPredecessor⟩] : List (Equation Nat)) = none := rfl

/-- A later cut cannot erase an answer already produced by an earlier
uncommitted equation. Selecting only the later committed equation is invalid. -/
theorem earlier_uncommitted_answer_survives_later_cut :
    source (fun _ value => value) (fun _ left _ => left)
      [⟨⟨.any, .any⟩, false, .singleton 1⟩,
       ⟨⟨.any, .any⟩, true, .singleton 2⟩]
      ([] : List Nat) 0 = [[1], [2]] := rfl

theorem earlier_uncommitted_then_cut_rejected :
    compile ([⟨⟨.any, .any⟩, false, .singleton 1⟩,
      ⟨⟨.any, .any⟩, true, .singleton 2⟩] : List (Equation Nat)) = none := rfl

/-- Entry commitment happens before the body: failure in the committed body
does not restore the later equation. Such a body fails the admission check. -/
theorem committed_failure_does_not_retry :
    source (fun _ value => value) (fun _ left _ => left)
      [⟨⟨.any, .any⟩, true, .unsupported⟩,
       ⟨⟨.any, .any⟩, false, .singleton 2⟩]
      ([] : List Nat) 0 = [] ∧
    compile ([⟨⟨.any, .any⟩, true, .unsupported⟩,
      ⟨⟨.any, .any⟩, false, .singleton 2⟩] : List (Equation Nat)) = none := by
  constructor <;> rfl

theorem duplicate_occurrences_preserved :
    source List.cons (fun _ left _ => left) combinations [1, 1, 2] 2 =
      [[[1, 1], [1, 2], [1, 2]]] := by decide

theorem local_commit_keeps_outer_answers :
    EquationCut.equations (fun _ => []) 0
      ((combinations (Item := Nat)).map
        (cutEquation ⟨false, false⟩
          (bodyResults List.cons (fun _ left _ => left) (fun _ => []) [] 0)))
      [] (fun value rest => value :: rest) [[[99]]] = [[[]], [[99]]] := by
  rw [equationsResults_eq_cut]
  rfl

end Examples

/-! Optional workers retain the same instruction grammar and shape classes.
They distinguish no answer from a returned empty collection. Unsupported
instructions refuse compilation; no-match observation remains a separate
dialect boundary. These are finite pure workers, not effect permissions. -/

def optionalSupported : Code Value → Bool
  | .unsupported => false
  | .append left right | .ifZero left right | .ifEmpty left right =>
      optionalSupported left && optionalSupported right
  | .mapHead body | .map _ body => optionalSupported body
  | _ => true

/-- No matching family is represented explicitly. Ambiguous uncommitted
equations refuse admission even if a particular body might fail. -/
def compileOptionalBranch (input : Shape) (program : List (Equation Value)) :
    Option (Option (Code Value)) :=
  if noMatch input program then some none
  else do
    let body ← select input program
    if optionalSupported body then some (some body) else none

def compileOptionalTree (program : List (Equation Value)) :
    Option (ShapeTree (Option (Code Value))) := do
  let zeroEmpty ← compileOptionalBranch ⟨false, false⟩ program
  let zeroCons ← compileOptionalBranch ⟨true, false⟩ program
  let positiveEmpty ← compileOptionalBranch ⟨false, true⟩ program
  let positiveCons ← compileOptionalBranch ⟨true, true⟩ program
  pure ⟨zeroEmpty, zeroCons, positiveEmpty, positiveCons⟩

/-- An independent optional execution fold. Sequencing propagates an empty
result; its recursive invocations are supplied by the compiled shape tree. -/
def optionalBody (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailRun : Nat → Option (List Value)) (items : List Item) (parameter : Nat) :
    Code Value → Option (List Value)
  | .empty => some []
  | .singleton value => some [value]
  | .append left right => do
      let earlier ← optionalBody construct callbackConstruct tailRun items parameter left
      let later ← optionalBody construct callbackConstruct tailRun items parameter right
      pure (earlier ++ later)
  | .mapHead body => match items with
      | [] => none
      | head :: _ => (optionalBody construct callbackConstruct tailRun items parameter body).map
          (List.map (construct head))
  | .map callback body =>
      (optionalBody construct callbackConstruct tailRun items parameter body).map
        (List.map (callback.run callbackConstruct))
  | .ifZero yes no => if parameter = 0 then
      optionalBody construct callbackConstruct tailRun items parameter yes
      else optionalBody construct callbackConstruct tailRun items parameter no
  | .ifEmpty yes no => if items = [] then
      optionalBody construct callbackConstruct tailRun items parameter yes
      else optionalBody construct callbackConstruct tailRun items parameter no
  | .callTail => match items with
      | [] => none
      | _ :: _ => tailRun parameter
  | .callPredecessor => match items, parameter with
      | _ :: _, count + 1 => tailRun count
      | _, _ => none
  | .unsupported => none

def optionalRun (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tree : ShapeTree (Option (Code Value))) : List Item → Nat → Option (List Value)
  | [], parameter => (tree.branch (shape ([] : List Item) parameter)).bind
      (optionalBody construct callbackConstruct (fun _ => none) [] parameter)
  | head :: tail, parameter => (tree.branch (shape (head :: tail) parameter)).bind
      (optionalBody construct callbackConstruct
        (optionalRun construct callbackConstruct tree tail) (head :: tail) parameter)

theorem optionalBody_occurrences (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailRun : Nat → Option (List Value)) (items : List Item) (parameter : Nat)
    (body : Code Value) :
    (optionalBody construct callbackConstruct tailRun items parameter body).toList =
      bodyResults construct callbackConstruct (fun count => (tailRun count).toList)
        items parameter body := by
  induction body with
  | empty => rfl
  | singleton value => rfl
  | append left right leftIH rightIH =>
      cases earlier : optionalBody construct callbackConstruct tailRun items parameter left <;>
        cases later : optionalBody construct callbackConstruct tailRun items parameter right <;>
        simp [optionalBody, bodyResults, ←leftIH, ←rightIH, earlier, later]
  | mapHead body ih =>
      cases items with
      | nil => rfl
      | cons head tail =>
          cases done : optionalBody construct callbackConstruct tailRun (head :: tail) parameter body <;>
            simp [optionalBody, bodyResults, ←ih, done]
  | map callback body ih =>
      cases done : optionalBody construct callbackConstruct tailRun items parameter body <;>
        simp [optionalBody, bodyResults, ←ih, done]
  | ifZero yes no yesIH noIH =>
      by_cases zero : parameter = 0
      · rw [optionalBody, if_pos zero, bodyResults, if_pos zero]; exact yesIH
      · rw [optionalBody, if_neg zero, bodyResults, if_neg zero]; exact noIH
  | ifEmpty yes no yesIH noIH =>
      by_cases empty : items = []
      · rw [optionalBody, if_pos empty, bodyResults, if_pos empty]; exact yesIH
      · rw [optionalBody, if_neg empty, bodyResults, if_neg empty]; exact noIH
  | callTail => cases items <;> rfl
  | callPredecessor => cases items <;> cases parameter <;> rfl
  | unsupported => rfl

theorem compileOptionalBranch_occurrences (input : Shape) (program : List (Equation Value))
    (branch : Option (Code Value))
    (accepted : compileOptionalBranch input program = some branch)
    (construct : Item → Value → Value) (callbackConstruct : Nat → Value → Value → Value)
    (tailRun : Nat → Option (List Value)) (items : List Item) (parameter : Nat) :
    (branch.bind (optionalBody construct callbackConstruct tailRun items parameter)).toList =
      equationsResults (fun head => head.accepts input)
        (bodyResults construct callbackConstruct (fun count => (tailRun count).toList)
          items parameter) program := by
  unfold compileOptionalBranch at accepted
  split at accepted
  next absent =>
    cases accepted
    simpa using (equationsResults_noMatch input program _ absent).symm
  next present =>
    cases selected : select input program with
    | none => simp [selected] at accepted
    | some body =>
        simp [selected] at accepted
        rcases accepted with ⟨_, rfl⟩
        simpa using (optionalBody_occurrences construct callbackConstruct tailRun
          items parameter body).trans (select_sound input program body selected _).symm

theorem compileOptionalTree_branches (program : List (Equation Value))
    (tree : ShapeTree (Option (Code Value)))
    (accepted : compileOptionalTree program = some tree) (input : Shape) :
    compileOptionalBranch input program = some (tree.branch input) := by
  unfold compileOptionalTree at accepted
  cases he : compileOptionalBranch ⟨false, false⟩ program <;> simp [he] at accepted
  rename_i ze
  cases hc : compileOptionalBranch ⟨true, false⟩ program <;> simp [hc] at accepted
  rename_i zc
  cases pe : compileOptionalBranch ⟨false, true⟩ program <;> simp [pe] at accepted
  rename_i ne
  cases pc : compileOptionalBranch ⟨true, true⟩ program <;> simp [pc] at accepted
  rename_i nc
  cases accepted
  rcases input with ⟨nonempty, positive⟩
  cases nonempty <;> cases positive <;> simp_all [ShapeTree.branch]

/-- Compiled recursion re-enters the shared shape tree; source recursion
re-enters every equation. The compiler, not a caller assertion, relates them. -/
theorem optionalRun_refines_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (program : List (Equation Value)) (tree : ShapeTree (Option (Code Value)))
    (accepted : compileOptionalTree program = some tree) (items : List Item) (parameter : Nat) :
    (optionalRun construct callbackConstruct tree items parameter).toList =
      source construct callbackConstruct program items parameter := by
  induction items generalizing parameter with
  | nil =>
      rw [optionalRun, source_equations_shape]
      exact compileOptionalBranch_occurrences _ _ _
        (compileOptionalTree_branches program tree accepted _) _ _ (fun _ => none) [] parameter
  | cons head tail ih =>
      rw [optionalRun, source_equations_shape]
      have compared := compileOptionalBranch_occurrences _ _ _
        (compileOptionalTree_branches program tree accepted (shape (head :: tail) parameter))
        construct callbackConstruct (optionalRun construct callbackConstruct tree tail)
        (head :: tail) parameter
      simpa only [ih] using compared

namespace OptionalControls

def maybeHead : List (Equation Nat) := [⟨⟨.cons, .any⟩, false, .mapHead (.singleton 7)⟩]

theorem maybeHead_compiles : compileOptionalTree maybeHead =
    some ⟨none, some (.mapHead (.singleton 7)), none, some (.mapHead (.singleton 7))⟩ := by rfl

theorem no_answer_differs_from_empty_collection :
    optionalRun Nat.add (fun _ left _ => left)
      ⟨none, some .empty, none, some .empty⟩ ([] : List Nat) 0 = none ∧
    optionalRun Nat.add (fun _ left _ => left)
      ⟨none, some .empty, none, some .empty⟩ [1] 0 = some [] := by decide

theorem duplicate_equations_refuse :
    compileOptionalTree ([⟨⟨.any, .any⟩, false, .singleton 7⟩,
      ⟨⟨.any, .any⟩, false, .singleton 7⟩] : List (Equation Nat)) = none := by decide

theorem unsupported_refuses :
    compileOptionalTree ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat)) = none := by decide

end OptionalControls

/-! ### Equation publication, not a body or call cursor

One invocation retains its authored equations, the ordinal of the next
untried occurrence, and the captured items and parameter. A matching
equation is published by one call to `bodyResults`. Commit seals later
occurrences without deleting them. An empty residual is finished only by
the closing step. Answer evidence is the yielded occurrence list; it is
not the phase.

This is not the producer worker. `RecursiveFiniteProducer.step` already
suspends `append`, `mapHead`, `map`, `ifZero`, `ifEmpty`, `callTail` and
`callPredecessor` for one admitted collection. Those frames are absent
here, and that cursor does not retain authored equation occurrences or the
source product of `bodyResults` append. A stepper that yields inside a
source call would need a body frame and a call frame whose callee is a
fresh equation frontier. Native body continuations are not represented.
-/

section RetainedFrontier

open AnswerCardinality

inductive NoRuleReading where
  | observe (policy : NoRulePolicy)
  | decline
  deriving DecidableEq, Repr

inductive FrontierPhase where
  | running
  | finished
  | declined
  deriving DecidableEq, Repr

/-- Authored equations stay in `authored`. `items` and `parameter` are the
captured invocation bindings. `ordinal` is the next untried occurrence. -/
structure RetainedFrontier (Item : Type u) (Value : Type v) where
  authored : List (Equation Value)
  ordinal : Nat
  matched : Bool
  sealed : Bool
  items : List Item
  parameter : Nat
  reading : NoRuleReading
  phase : FrontierPhase
  deriving Repr

def openFrontier (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (reading : NoRuleReading) : RetainedFrontier Item Value where
  authored := program
  ordinal := 0
  matched := false
  sealed := false
  items := items
  parameter := parameter
  reading := reading
  phase := .running

/-- Untried authored occurrences remain. A sealed commit and a closing step
are not pending. -/
def RetainedFrontier.isPending (frontier : RetainedFrontier Item Value) : Bool :=
  match frontier.phase with
  | .running => !frontier.sealed && decide (frontier.ordinal < frontier.authored.length)
  | .finished | .declined => false

inductive FrontierPulse (Item : Type u) (Value : Type v) where
  | observed (occurrences : List (List Value)) (next : RetainedFrontier Item Value)
  | skipped (next : RetainedFrontier Item Value)
  | finished (occurrences : List (List Value)) (next : RetainedFrontier Item Value)
  | declined (next : RetainedFrontier Item Value)
  deriving Repr

def matchesAny (headOk : Head → Bool) : List (Equation Value) → Bool
  | [] => false
  | equation :: rest => headOk equation.head || matchesAny headOk rest

def stepFrontier (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) : FrontierPulse Item Value :=
  match frontier.phase with
  | .finished => .finished [] frontier
  | .declined => .declined frontier
  | .running =>
      if frontier.sealed then
        .finished [] { frontier with phase := .finished }
      else
        match frontier.authored.drop frontier.ordinal with
        | [] =>
            if frontier.matched then
              .finished [] { frontier with phase := .finished }
            else
              match frontier.reading with
              | .decline => .declined { frontier with phase := .declined }
              | .observe policy =>
                  .finished (observeRuleBodies policy fallback [])
                    { frontier with phase := .finished }
        | equation :: _ =>
            if equation.head.matches frontier.items frontier.parameter then
              .observed
                (bodyResults construct callbackConstruct tailResults frontier.items
                  frontier.parameter equation.body)
                { frontier with
                    ordinal := frontier.ordinal + 1
                    matched := true
                    sealed := equation.commit }
            else
              .skipped { frontier with ordinal := frontier.ordinal + 1 }

/-- Step budget. Fuel `0` returns the same frontier and is not completion.
A skip or an observation consumes one step. Extra fuel on a finished or
declined frontier does not replay. -/
def driveFrontier (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value) :
    Nat → RetainedFrontier Item Value → List (List Value) × RetainedFrontier Item Value
  | 0, frontier => ([], frontier)
  | fuel + 1, frontier =>
      match stepFrontier construct callbackConstruct tailResults fallback frontier with
      | .observed occurrences next =>
          let later := driveFrontier construct callbackConstruct tailResults fallback fuel next
          (occurrences ++ later.1, later.2)
      | .skipped next =>
          driveFrontier construct callbackConstruct tailResults fallback fuel next
      | .finished occurrences next => (occurrences, next)
      | .declined next => ([], next)

def suffixOccurrences (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) : List (List Value) :=
  match frontier.phase with
  | .finished | .declined => []
  | .running =>
      if frontier.sealed then []
      else
        let remaining := frontier.authored.drop frontier.ordinal
        let answers := equationsResults (fun head => head.matches frontier.items frontier.parameter)
          (bodyResults construct callbackConstruct tailResults frontier.items frontier.parameter)
          remaining
        if frontier.matched ||
            matchesAny (fun head => head.matches frontier.items frontier.parameter) remaining then
          answers
        else
          match frontier.reading with
          | .decline => []
          | .observe policy => observeRuleBodies policy fallback []

private theorem drop_succ_of_drop_cons {α : Type _} {xs : List α} {index : Nat}
    {head : α} {tail : List α} (exposed : xs.drop index = head :: tail) :
    xs.drop (index + 1) = tail := by
  induction index generalizing xs with
  | zero =>
      cases xs with
      | nil =>
          simp only [List.drop_nil] at exposed
          cases exposed
      | cons item rest =>
          simp only [List.drop_zero] at exposed
          cases exposed
          simp only [List.drop_succ_cons, List.drop_zero]
  | succ index ih =>
      cases xs with
      | nil =>
          simp only [List.drop_nil] at exposed
          cases exposed
      | cons _ rest =>
          simp only [List.drop_succ_cons] at exposed
          simpa only [List.drop_succ_cons] using ih exposed

theorem equationsResults_of_no_match (headOk : Head → Bool)
    (runBody : Code Value → List (List Value)) (program : List (Equation Value))
    (absent : matchesAny headOk program = false) :
    equationsResults headOk runBody program = [] := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      have headMiss : headOk equation.head = false := by
        cases hit : headOk equation.head
        · rfl
        · simp only [matchesAny, hit, Bool.true_or] at absent
          cases absent
      have restMiss : matchesAny headOk rest = false := by
        simp only [matchesAny, headMiss, Bool.false_or] at absent
        exact absent
      simp only [equationsResults, headMiss, ih restMiss]
      rfl

theorem driveFrontier_zero (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) :
    driveFrontier construct callbackConstruct tailResults fallback 0 frontier = ([], frontier) := rfl

theorem driveFrontier_finished_stable (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (done : frontier.phase = .finished) (fuel : Nat) :
    driveFrontier construct callbackConstruct tailResults fallback fuel frontier = ([], frontier) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [driveFrontier, stepFrontier, done]

theorem driveFrontier_declined_stable (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (stopped : frontier.phase = .declined) (fuel : Nat) :
    driveFrontier construct callbackConstruct tailResults fallback fuel frontier = ([], frontier) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [driveFrontier, stepFrontier, stopped]

theorem driveFrontier_succ (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (fuel : Nat) (frontier : RetainedFrontier Item Value) :
    driveFrontier construct callbackConstruct tailResults fallback (fuel + 1) frontier =
      match stepFrontier construct callbackConstruct tailResults fallback frontier with
      | .observed occurrences next =>
          (occurrences ++
              (driveFrontier construct callbackConstruct tailResults fallback fuel next).1,
            (driveFrontier construct callbackConstruct tailResults fallback fuel next).2)
      | .skipped next =>
          driveFrontier construct callbackConstruct tailResults fallback fuel next
      | .finished occurrences next => (occurrences, next)
      | .declined next => ([], next) := rfl

private theorem fuel_add_succ (earlier later : Nat) :
    earlier + 1 + later = (earlier + later) + 1 := by
  rw [Nat.add_assoc, Nat.add_comm 1 later, ← Nat.add_assoc]

theorem driveFrontier_sealed_finishes (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (running : frontier.phase = .running)
    (isSealed : frontier.sealed = true) (extra : Nat) :
    driveFrontier construct callbackConstruct tailResults fallback (extra + 1) frontier =
      ([], { frontier with phase := .finished }) := by
  rw [driveFrontier_succ]
  simp only [stepFrontier, running, isSealed, ↓reduceIte]

theorem stepFrontier_preserves_capture (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) :
    match stepFrontier construct callbackConstruct tailResults fallback frontier with
    | .observed _ next | .skipped next | .finished _ next | .declined next =>
        next.authored = frontier.authored ∧ next.items = frontier.items ∧
          next.parameter = frontier.parameter := by
  cases phase : frontier.phase
  · cases sealed : frontier.sealed
    · cases remaining : frontier.authored.drop frontier.ordinal with
      | nil =>
          cases matched : frontier.matched <;> cases reading : frontier.reading <;>
            simp [stepFrontier, phase, sealed, remaining, matched, reading]
      | cons equation rest =>
          cases headMatch : equation.head.matches frontier.items frontier.parameter <;>
            simp [stepFrontier, phase, sealed, remaining, headMatch]
    · simp [stepFrontier, phase, sealed]
  · simp [stepFrontier, phase]
  · simp [stepFrontier, phase]

theorem observed_step_remains_running (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (occurrences : List (List Value))
    (next : RetainedFrontier Item Value)
    (stepped : stepFrontier construct callbackConstruct tailResults fallback frontier =
      .observed occurrences next) :
    next.phase = .running ∧ next.authored = frontier.authored ∧
      next.items = frontier.items ∧ next.parameter = frontier.parameter := by
  unfold stepFrontier at stepped
  (repeat' split at stepped) <;> simp_all
  all_goals rcases stepped with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem finished_step_phase (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (occurrences : List (List Value))
    (next : RetainedFrontier Item Value)
    (stepped : stepFrontier construct callbackConstruct tailResults fallback frontier =
      .finished occurrences next) : next.phase = .finished := by
  unfold stepFrontier at stepped
  (repeat' split at stepped) <;> simp_all
  all_goals rcases stepped with ⟨_, rfl⟩; rfl

private theorem declined_step_phase (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (next : RetainedFrontier Item Value)
    (stepped : stepFrontier construct callbackConstruct tailResults fallback frontier =
      .declined next) : next.phase = .declined := by
  unfold stepFrontier at stepped
  (repeat' split at stepped) <;> simp_all
  all_goals subst next; rfl

/-- Fuel splits into a loaned equation-publication prefix and the residual
frontier. Resuming that residual does not replay the prefix. The loan is one
whole `bodyResults` list per matched equation, not a yield inside the body. -/
theorem driveFrontier_split_resumes (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (earlier later : Nat) (frontier : RetainedFrontier Item Value) :
    ((driveFrontier construct callbackConstruct tailResults fallback earlier frontier).1 ++
        (driveFrontier construct callbackConstruct tailResults fallback later
          (driveFrontier construct callbackConstruct tailResults fallback earlier frontier).2).1,
      (driveFrontier construct callbackConstruct tailResults fallback later
        (driveFrontier construct callbackConstruct tailResults fallback earlier frontier).2).2) =
      driveFrontier construct callbackConstruct tailResults fallback (earlier + later) frontier := by
  induction earlier generalizing frontier with
  | zero => simp only [driveFrontier, Nat.zero_add, List.nil_append]
  | succ earlier ih =>
      cases pulse : stepFrontier construct callbackConstruct tailResults fallback frontier with
      | observed occurrences next =>
          rw [driveFrontier_succ (fuel := earlier)]
          simp only [pulse]
          rw [fuel_add_succ earlier later, driveFrontier_succ (fuel := earlier + later)]
          simp only [pulse]
          have resumed := ih next
          rw [← resumed]
          simp only [List.append_assoc]
      | skipped next =>
          rw [driveFrontier_succ (fuel := earlier)]
          simp only [pulse]
          rw [fuel_add_succ earlier later, driveFrontier_succ (fuel := earlier + later)]
          simp only [pulse]
          exact ih next
      | finished occurrences next =>
          have done := finished_step_phase construct callbackConstruct tailResults
            fallback frontier occurrences next pulse
          have stable := driveFrontier_finished_stable construct callbackConstruct tailResults
            fallback next done later
          rw [driveFrontier_succ (fuel := earlier)]
          simp only [pulse]
          rw [fuel_add_succ earlier later, driveFrontier_succ (fuel := earlier + later)]
          simp only [pulse, stable, List.append_nil]
      | declined next =>
          have done := declined_step_phase construct callbackConstruct tailResults
            fallback frontier next pulse
          have stable := driveFrontier_declined_stable construct callbackConstruct tailResults
            fallback next done later
          rw [driveFrontier_succ (fuel := earlier)]
          simp only [pulse]
          rw [fuel_add_succ earlier later, driveFrontier_succ (fuel := earlier + later)]
          simp only [pulse, stable, List.nil_append]

theorem driveFrontier_running_eq (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (List Value)) (fallback : List Value)
    (frontier : RetainedFrontier Item Value) (running : frontier.phase = .running)
    (openSeal : frontier.sealed = false) :
    let remaining := frontier.authored.drop frontier.ordinal
    let result := driveFrontier construct callbackConstruct tailResults fallback
      (remaining.length + 1) frontier
    result.1 = suffixOccurrences construct callbackConstruct tailResults fallback frontier ∧
      result.2.authored = frontier.authored ∧ result.2.items = frontier.items ∧
      result.2.parameter = frontier.parameter ∧
      result.2.phase = if frontier.matched ||
          matchesAny (fun head => head.matches frontier.items frontier.parameter) remaining then
        .finished else match frontier.reading with
          | .decline => .declined
          | .observe _ => .finished := by
  intro remaining result
  suffices ∀ (frontier : RetainedFrontier Item Value), frontier.phase = .running →
      frontier.sealed = false →
      ∀ (suffix : List (Equation Value)), frontier.authored.drop frontier.ordinal = suffix →
        (driveFrontier construct callbackConstruct tailResults fallback (suffix.length + 1)
            frontier).1 =
          suffixOccurrences construct callbackConstruct tailResults fallback frontier ∧
        (driveFrontier construct callbackConstruct tailResults fallback (suffix.length + 1)
            frontier).2.authored = frontier.authored ∧
        (driveFrontier construct callbackConstruct tailResults fallback (suffix.length + 1)
            frontier).2.items = frontier.items ∧
        (driveFrontier construct callbackConstruct tailResults fallback (suffix.length + 1)
            frontier).2.parameter = frontier.parameter ∧
        (driveFrontier construct callbackConstruct tailResults fallback (suffix.length + 1)
            frontier).2.phase = if frontier.matched ||
            matchesAny (fun head => head.matches frontier.items frontier.parameter) suffix then
          .finished else match frontier.reading with
            | .decline => .declined
            | .observe _ => .finished from
    this frontier running openSeal remaining rfl
  intro frontier running openSeal suffix exposed
  induction suffix generalizing frontier with
  | nil =>
      cases matched : frontier.matched <;> cases reading : frontier.reading <;>
        simp [exposed, List.length_nil, driveFrontier_succ, stepFrontier, running,
          openSeal, matched, reading, suffixOccurrences, matchesAny, equationsResults,
          observeRuleBodies, Bool.or_false, ↓reduceIte]
  | cons equation rest ih =>
      have nextDrop : frontier.authored.drop (frontier.ordinal + 1) = rest :=
        drop_succ_of_drop_cons exposed
      cases headMatch : equation.head.matches frontier.items frontier.parameter
      · have stepSkip : stepFrontier construct callbackConstruct tailResults fallback frontier =
            .skipped { frontier with ordinal := frontier.ordinal + 1 } := by
          simp [stepFrontier, running, openSeal, exposed, headMatch, ↓reduceIte]
        have later := ih { frontier with ordinal := frontier.ordinal + 1 } running openSeal nextDrop
        have anyRest :
            matchesAny (fun head => head.matches frontier.items frontier.parameter)
              (equation :: rest) =
            matchesAny (fun head => head.matches frontier.items frontier.parameter) rest := by
          simp [matchesAny, headMatch, Bool.false_or]
        have fuel : (equation :: rest).length + 1 = (rest.length + 1) + 1 := by
          simp [List.length_cons]
        rw [fuel, driveFrontier_succ, stepSkip]
        simp [suffixOccurrences, running, openSeal, exposed, nextDrop, anyRest, equationsResults,
          headMatch, ↓reduceIte] at later ⊢
        exact later
      · cases committed : equation.commit
        · have stepObs : stepFrontier construct callbackConstruct tailResults fallback frontier =
              .observed
                (bodyResults construct callbackConstruct tailResults frontier.items
                  frontier.parameter equation.body)
                { frontier with
                    ordinal := frontier.ordinal + 1
                    matched := true
                    sealed := false } := by
            simp [stepFrontier, running, openSeal, exposed, headMatch, committed, ↓reduceIte]
          have later := ih
            { frontier with
                ordinal := frontier.ordinal + 1
                matched := true
                sealed := false }
            running rfl nextDrop
          have fuel : (equation :: rest).length + 1 = (rest.length + 1) + 1 := by
            simp [List.length_cons]
          rw [fuel, driveFrontier_succ, stepObs]
          simp [suffixOccurrences, running, openSeal, exposed, nextDrop, matchesAny, headMatch,
            Bool.or_true, equationsResults, committed, ↓reduceIte] at later ⊢
          simp [later.1, later.2.1, later.2.2.1, later.2.2.2.1, later.2.2.2.2]
        · have stepObs : stepFrontier construct callbackConstruct tailResults fallback frontier =
              .observed
                (bodyResults construct callbackConstruct tailResults frontier.items
                  frontier.parameter equation.body)
                { frontier with
                    ordinal := frontier.ordinal + 1
                    matched := true
                    sealed := true } := by
            simp [stepFrontier, running, openSeal, exposed, headMatch, committed, ↓reduceIte]
          have closed := driveFrontier_sealed_finishes construct callbackConstruct tailResults
            fallback
            { frontier with
                ordinal := frontier.ordinal + 1
                matched := true
                sealed := true }
            running rfl rest.length
          simp only [running] at closed
          have fuel : (equation :: rest).length + 1 = (rest.length + 1) + 1 := by
            simp [List.length_cons]
          rw [fuel, driveFrontier_succ, stepObs]
          simp [closed, suffixOccurrences, running, openSeal, exposed, matchesAny, headMatch,
            equationsResults, committed]

#print axioms driveFrontier_split_resumes
#print axioms driveFrontier_running_eq
#print axioms observed_step_remains_running
#print axioms driveFrontier_finished_stable
#print axioms equationsResults_of_no_match

end RetainedFrontier

/-!
## Body/call execution

`BodyCall.step` is the runnable cursor. A body cursor is an existing
`RecursiveFiniteProducer.Frame` plus one append consumer. A call does not
receive `source` or `sourceTail`; it pushes `openFrontier` on the captured
tail. Append streams `first ++ second` for each saved left occurrence and
keeps the right code's own items, parameter and maps. The coarse
`stepFrontier` observer remains available and is not this transition.

`.decline` returns the whole stack, including the caller and any undelivered
append choice. `.unsupported` is a handoff of every current frame. An unmatched
`.retainFallback` reads `fallback items parameter` for that invocation and
applies that invocation's maps before the append or outer consumer.
`.observe .noAnswers` remains the source observer. `optionalSupported` excludes
`.unsupported` when completion is required. `bodyResults` is unchanged.

`State` stores the work stack and the stop phase together. Fuel exhaustion
leaves that phase unchanged, so a pending empty loan is `.running`. A finished
empty loan is `.finished`. Decline and handoff keep the frames and use their
own phases. The phase is not recomputed from the bottom frame.

The source correspondence does not establish native cursor refinement or a
Prime eager/lazy equivalence. Native argument-shape admission remains a
separate implementation contract.
-/

namespace BodyCall

open AnswerCardinality RecursiveFiniteProducer

/-- Right-hand append continuation. `times` saves the append context.
`concat` is the saved left occurrence waiting on the next right occurrence. -/
inductive Consumer (Item : Type u) (Value : Type v) where
  | emit
  | concat (first : List Value) (outer : Consumer Item Value)
  | times (right : Code Value) (items : List Item) (parameter : Nat)
      (maps : List (Mapper Item Value)) (outer : Consumer Item Value)

/-- Invocation cursor, or one suspended `Frame` plus its append consumer.
`authored` and `reading` are the captured call context, not a second grammar. -/
inductive Cursor (Item : Type u) (Value : Type v) where
  | invoke (frontier : RetainedFrontier Item Value) (maps : List (Mapper Item Value))
      (consumer : Consumer Item Value)
  | body (authored : List (Equation Value)) (reading : NoRuleReading)
      (frame : Frame Item Value) (consumer : Consumer Item Value)

/-- Cursor stop. `.running` is pending, including a pending empty loan.
`.finished` is completion, including a finished empty loan. Decline and
handoff keep the work stack. -/
inductive Phase where
  | running
  | finished
  | declined
  | handoff
  deriving DecidableEq, Repr

structure State (Item : Type u) (Value : Type v) where
  work : List (Cursor Item Value)
  phase : Phase

inductive Move (Item : Type u) (Value : Type v) where
  | advance (next : State Item Value)
  | yield (occurrence : List Value) (next : State Item Value)
  | finish (occurrences : List (List Value)) (next : State Item Value)
  | decline (next : State Item Value)
  | handoff (next : State Item Value)

def withPhase (phase : Phase) (work : List (Cursor Item Value)) : State Item Value :=
  { work, phase }

def openState (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (reading : NoRuleReading) : State Item Value :=
  { work := [.invoke (openFrontier program items parameter reading) [] .emit]
    phase := .running }

def deliver (authored : List (Equation Value)) (reading : NoRuleReading)
    (occurrence : List Value) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) : Move Item Value :=
  match consumer with
  | .emit => .yield occurrence (withPhase .running rest)
  | .concat first outer => deliver authored reading (first ++ occurrence) outer rest
  | .times right items parameter maps outer =>
      .advance (withPhase .running
        (.body authored reading ⟨right, items, parameter, maps⟩ (.concat occurrence outer) :: rest))

def finishInvoke (frontier : RetainedFrontier Item Value) (maps : List (Mapper Item Value))
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (occurrences : List (List Value)) : Move Item Value :=
  let closed := { frontier with phase := .finished }
  if rest.isEmpty then .finish occurrences (withPhase .finished [.invoke closed maps consumer])
  else .advance (withPhase .running rest)

/-- Logical failure keeps the caller continuation and any consumer still holding
an undelivered choice. It does not pop into that caller. -/
def declineInvoke (frontier : RetainedFrontier Item Value) (maps : List (Mapper Item Value))
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value)) : Move Item Value :=
  .decline (withPhase .declined
    (.invoke { frontier with phase := .declined } maps consumer :: rest))

/-- One transition. Calls push an authored invocation. Append parks `right`
on the left frame and yields `first ++ second` one pair at a time.
`fallback` is read at the failing invocation's own items and parameter. -/
def stepRunning (construct : Item → Value → Value) (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) : List (Cursor Item Value) → Move Item Value
  | [] => .finish [] (withPhase .finished [])
  | .invoke frontier maps consumer :: rest =>
      match frontier.phase with
      | .finished =>
          if rest.isEmpty then .finish [] (withPhase .finished (.invoke frontier maps consumer :: rest))
          else .advance (withPhase .running rest)
      | .declined =>
          .decline (withPhase .declined (.invoke frontier maps consumer :: rest))
      | .running =>
          if frontier.sealed then finishInvoke frontier maps consumer rest []
          else
            match frontier.authored.drop frontier.ordinal with
            | [] =>
                if frontier.matched then finishInvoke frontier maps consumer rest []
                else
                  match frontier.reading with
                  | .decline => declineInvoke frontier maps consumer rest
                  | .observe policy =>
                      let family := observeRuleBodies policy
                        (fallback frontier.items frontier.parameter) []
                      match family with
                      | [] =>
                          if rest.isEmpty then finishInvoke frontier maps consumer rest []
                          else .advance (withPhase .running rest)
                      | raw :: _ =>
                          let occurrence :=
                            raw.map (applyMaps construct callbackConstruct maps)
                          if rest.isEmpty then
                            finishInvoke frontier maps consumer rest [occurrence]
                          else
                            deliver frontier.authored frontier.reading occurrence consumer rest
            | equation :: _ =>
                if equation.head.matches frontier.items frontier.parameter then
                  let nextFrontier := { frontier with
                    ordinal := frontier.ordinal + 1
                    matched := true
                    sealed := equation.commit }
                  .advance (withPhase .running
                    (.body frontier.authored frontier.reading
                        ⟨equation.body, frontier.items, frontier.parameter, maps⟩ consumer ::
                      .invoke nextFrontier maps consumer :: rest))
                else
                  .advance (withPhase .running
                    (.invoke { frontier with ordinal := frontier.ordinal + 1 } maps consumer :: rest))
  | .body authored reading frame consumer :: rest =>
      match frame.code with
      | .empty => deliver authored reading [] consumer rest
      | .singleton value =>
          deliver authored reading [applyMaps construct callbackConstruct frame.maps value]
            consumer rest
      | .append left right =>
          .advance (withPhase .running
            (.body authored reading { frame with code := left }
                (.times right frame.items frame.parameter frame.maps consumer) :: rest))
      | .mapHead inner =>
          match frame.items with
          | [] => .advance (withPhase .running rest)
          | head :: _ =>
              .advance (withPhase .running
                (.body authored reading
                    { frame with code := inner, maps := .head head :: frame.maps } consumer :: rest))
      | .map callback inner =>
          .advance (withPhase .running
            (.body authored reading
                { frame with code := inner, maps := .callback callback :: frame.maps }
                consumer :: rest))
      | .ifZero yes no =>
          if frame.parameter = 0 then
            .advance (withPhase .running
              (.body authored reading { frame with code := yes } consumer :: rest))
          else
            .advance (withPhase .running
              (.body authored reading { frame with code := no } consumer :: rest))
      | .ifEmpty yes no =>
          match frame.items with
          | [] =>
              .advance (withPhase .running
                (.body authored reading { frame with code := yes } consumer :: rest))
          | _ :: _ =>
              .advance (withPhase .running
                (.body authored reading { frame with code := no } consumer :: rest))
      | .callTail =>
          match frame.items with
          | [] => .advance (withPhase .running rest)
          | _ :: tail =>
              .advance (withPhase .running
                (.invoke (openFrontier authored tail frame.parameter reading) frame.maps consumer ::
                  rest))
      | .callPredecessor =>
          match frame.items, frame.parameter with
          | _ :: tail, count + 1 =>
              .advance (withPhase .running
                (.invoke (openFrontier authored tail count reading) frame.maps consumer :: rest))
          | _, _ => .advance (withPhase .running rest)
      | .unsupported =>
          .handoff (withPhase .handoff (.body authored reading frame consumer :: rest))

/-- The stored phase is authoritative. A terminal phase does not walk the
stack, so a declined or handed-off frame is not reported as pending. -/
def step (construct : Item → Value → Value) (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : State Item Value) : Move Item Value :=
  match state.phase with
  | .running => stepRunning construct callbackConstruct fallback state.work
  | .finished => .finish [] state
  | .declined => .decline state
  | .handoff => .handoff state

/-- `.unsupported` is outside `optionalSupported`. The cursor keeps that frame.
`bodyResults` still maps the same instruction to `[]`. -/
theorem unsupported_hands_off
    (construct : Item → Value → Value) (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (reading : NoRuleReading) (frame : Frame Item Value) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) (alien : frame.code = .unsupported) :
    step construct callbackConstruct fallback
        { work := .body authored reading frame consumer :: rest, phase := .running } =
      .handoff { work := .body authored reading frame consumer :: rest, phase := .handoff } := by
  cases frame with
  | mk code _ _ _ =>
      cases code
      case unsupported => rfl
      case empty => cases alien
      case singleton _ => cases alien
      case append _ _ => cases alien
      case mapHead _ => cases alien
      case map _ _ => cases alien
      case ifZero _ _ => cases alien
      case ifEmpty _ _ => cases alien
      case callTail => cases alien
      case callPredecessor => cases alien

/-- Fuel `0` keeps the cursor, including its phase. A yield is one occurrence.
Finish, decline, and handoff loan nothing further and leave their phase on
the same state. -/
def drive (construct : Item → Value → Value) (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) :
    Nat → State Item Value → List (List Value) × State Item Value
  | 0, state => ([], state)
  | fuel + 1, state =>
      match step construct callbackConstruct fallback state with
      | .advance next => drive construct callbackConstruct fallback fuel next
      | .yield occurrence next =>
          let later := drive construct callbackConstruct fallback fuel next
          (occurrence :: later.1, later.2)
      | .finish occurrences next => (occurrences, next)
      | .decline next => ([], next)
      | .handoff next => ([], next)

/-- A terminal phase is the resume boundary. Extra fuel does not turn decline,
handoff, or finished empty back into a pending loan, and it does not drop frames. -/
theorem drive_keeps_a_terminal_phase
    (construct : Item → Value → Value) (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (fuel : Nat) (state : State Item Value)
    (stopped : state.phase ≠ .running) :
    drive construct callbackConstruct fallback fuel state = ([], state) := by
  cases fuel with
  | zero => rfl
  | succ _ =>
      cases h : state.phase
      · exact False.elim (stopped h)
      · simp only [drive, step, h]
      · simp only [drive, step, h]
      · simp only [drive, step, h]


/-! The following finite answer view is a specification of retained pure work.
It never runs in `step` or `drive`. The stored stop phase remains an independent
observation; projecting a work stack does not authorize a declined or handed-off
cursor to run. Source comparison uses the supported, no-answer-reading profile. -/

def bodyRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (authored : List (Equation Value)) (items : List Item) (parameter : Nat)
    (code : Code Value) : List (List Value) :=
  bodyResults construct callbackConstruct
    (match items with
     | [] => fun _ => []
     | _ :: tail => source construct callbackConstruct authored tail)
    items parameter code

def mappedRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (maps : List (Mapper Item Value)) (rows : List (List Value)) : List (List Value) :=
  rows.map (List.map (applyMaps construct callbackConstruct maps))

/-- A saved append context interprets the right code at its own captures.
The outer consumer receives each pair in left-to-right occurrence order. -/
def bindConsumer (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (authored : List (Equation Value)) :
    Consumer Item Value → List Value → List (List Value)
  | .emit, row => [row]
  | .concat first outer, row =>
      bindConsumer construct callbackConstruct authored outer (first ++ row)
  | .times right items parameter maps outer, row =>
      (mappedRows construct callbackConstruct maps
        (bodyRows construct callbackConstruct authored items parameter right)).flatMap
          (fun second => bindConsumer construct callbackConstruct authored outer (row ++ second))

def invokeRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (frontier : RetainedFrontier Item Value) : List (List Value) :=
  match frontier.phase with
  | .running =>
      if frontier.sealed then [] else
        equationsResults (fun head => head.matches frontier.items frontier.parameter)
          (bodyRows construct callbackConstruct frontier.authored frontier.items frontier.parameter)
          (frontier.authored.drop frontier.ordinal)
  | .finished | .declined => []

def cursorRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) : Cursor Item Value → List (List Value)
  | .invoke frontier maps consumer =>
      (mappedRows construct callbackConstruct maps
        (invokeRows construct callbackConstruct frontier)).flatMap
          (bindConsumer construct callbackConstruct frontier.authored consumer)
  | .body authored _ frame consumer =>
      (mappedRows construct callbackConstruct frame.maps
        (bodyRows construct callbackConstruct authored frame.items frame.parameter frame.code)).flatMap
          (bindConsumer construct callbackConstruct authored consumer)

def workRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (work : List (Cursor Item Value)) : List (List Value) :=
  work.flatMap (cursorRows construct callbackConstruct)

def Move.next (move : Move Item Value) : State Item Value :=
  match move with
  | .advance next | .yield _ next | .finish _ next | .decline next | .handoff next => next

def Move.rows (move : Move Item Value) : List (List Value) :=
  match move with
  | .yield row _ => [row]
  | .finish rows _ => rows
  | .advance _ | .decline _ | .handoff _ => []

theorem mappedRows_append (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (maps : List (Mapper Item Value))
    (left right : List (List Value)) :
    mappedRows construct callbackConstruct maps (left ++ right) =
      mappedRows construct callbackConstruct maps left ++
        mappedRows construct callbackConstruct maps right := by
  simp [mappedRows]

theorem workRows_cons (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (cursor : Cursor Item Value)
    (rest : List (Cursor Item Value)) :
    workRows construct callbackConstruct (cursor :: rest) =
      cursorRows construct callbackConstruct cursor ++ workRows construct callbackConstruct rest := by
  simp [workRows]

/-- Delivery consumes only its current row. The saved right code and all
sibling cursors remain the exact residual required by the source answer view. -/
theorem deliver_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (authored : List (Equation Value))
    (reading : NoRuleReading) (consumer : Consumer Item Value) (row : List Value)
    (rest : List (Cursor Item Value)) :
    let moved := deliver authored reading row consumer rest
    moved.rows ++ workRows construct callbackConstruct moved.next.work =
      bindConsumer construct callbackConstruct authored consumer row ++
        workRows construct callbackConstruct rest := by
  induction consumer generalizing row with
  | emit => rfl
  | concat first outer ih =>
      exact ih (first ++ row)
  | times right items parameter maps outer ih =>
      simp [deliver, Move.rows, Move.next, withPhase, workRows_cons, cursorRows, bindConsumer]

/-- This source comparison uses the source's no-answer reading for an
unmatched call. Retain-fallback and decline remain separate dialect policies. -/
def Cursor.sourceReading : Cursor Item Value → Prop
  | .invoke frontier _ _ => frontier.reading = .observe .noAnswers
  | .body _ reading _ _ => reading = .observe .noAnswers

def sourceReadings (work : List (Cursor Item Value)) : Prop :=
  ∀ cursor ∈ work, cursor.sourceReading

@[simp] theorem sourceReadings_nil : sourceReadings ([] : List (Cursor Item Value)) := by
  simp [sourceReadings]

@[simp] theorem sourceReadings_cons (cursor : Cursor Item Value)
    (rest : List (Cursor Item Value)) :
    sourceReadings (cursor :: rest) ↔ cursor.sourceReading ∧ sourceReadings rest := by
  simp [sourceReadings]

theorem source_eq_equationsRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    source construct callbackConstruct authored items parameter =
      equationsResults (fun head => head.matches items parameter)
        (bodyRows construct callbackConstruct authored items parameter) authored := by
  cases items <;> rfl

/-- A body instruction preserves the ordered answer view and every saved
append/call continuation. Unsupported code retains its handoff phase. -/
theorem body_step_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (frame : Frame Item Value) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) :
    let cursor := Cursor.body authored (.observe .noAnswers) frame consumer
    let moved := stepRunning construct callbackConstruct fallback (cursor :: rest)
    moved.rows ++ workRows construct callbackConstruct moved.next.work =
      workRows construct callbackConstruct (cursor :: rest) := by
  rcases frame with ⟨code, items, parameter, maps⟩
  cases code <;> cases items <;> cases parameter <;>
    simp only [stepRunning]
  all_goals try rw [deliver_preserves_rows]
  all_goals simp [Move.rows, Move.next, withPhase, workRows_cons, cursorRows,
    bindConsumer, bodyRows, bodyResults, mappedRows, applyMaps, List.map_map,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_append,
    Function.comp_def, invokeRows, openFrontier]
  all_goals rw [← source_eq_equationsRows]

theorem finishInvoke_empty_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (frontier : RetainedFrontier Item Value) (maps : List (Mapper Item Value))
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value)) :
    let moved := finishInvoke frontier maps consumer rest []
    moved.rows ++ workRows construct callbackConstruct moved.next.work =
      workRows construct callbackConstruct rest := by
  cases rest <;>
    simp [finishInvoke, Move.rows, Move.next, withPhase, workRows, cursorRows, invokeRows,
      mappedRows]

/-- Equation selection contributes its body once and retains exactly the
uncommitted suffix. A cut closes only this invocation's remaining choices. -/
theorem invoke_step_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) (reading : frontier.reading = .observe .noAnswers) :
    let cursor := Cursor.invoke frontier maps consumer
    let moved := stepRunning construct callbackConstruct fallback (cursor :: rest)
    moved.rows ++ workRows construct callbackConstruct moved.next.work =
      workRows construct callbackConstruct (cursor :: rest) := by
  cases phase : frontier.phase with
  | finished =>
      cases rest <;>
        simp [stepRunning, phase, Move.rows, Move.next, withPhase, workRows_cons,
          cursorRows, invokeRows, mappedRows]
  | declined =>
      simp [stepRunning, phase, Move.rows, Move.next, withPhase]
  | running =>
      cases sealed : frontier.sealed with
      | true =>
          simpa [stepRunning, phase, sealed, workRows_cons, cursorRows, invokeRows,
            mappedRows] using
              finishInvoke_empty_preserves_rows construct callbackConstruct frontier maps consumer rest
      | false =>
          cases exposed : frontier.authored.drop frontier.ordinal with
          | nil =>
              cases matched : frontier.matched <;> cases rest <;>
                simp [stepRunning, phase, sealed, exposed, matched, reading,
                  observeRuleBodies, finishInvoke, Move.rows, Move.next, withPhase,
                  workRows_cons, cursorRows, invokeRows, equationsResults, mappedRows]
          | cons equation remaining =>
              have dropNext := drop_succ_of_drop_cons exposed
              cases hit : equation.head.matches frontier.items frontier.parameter <;>
                cases committed : equation.commit <;>
                simp [stepRunning, phase, sealed, exposed, hit, committed,
                  dropNext, Move.rows, Move.next, withPhase, workRows_cons, cursorRows,
                  invokeRows, equationsResults, mappedRows, List.map_append,
                  List.append_assoc]

/-- One running instruction preserves the source view of the entire retained
stack, including pending siblings and append consumers. -/
theorem stepRunning_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (work : List (Cursor Item Value))
    (readings : sourceReadings work) :
    let moved := stepRunning construct callbackConstruct fallback work
    moved.rows ++ workRows construct callbackConstruct moved.next.work =
      workRows construct callbackConstruct work := by
  cases work with
  | nil => rfl
  | cons cursor rest =>
      have first := (sourceReadings_cons cursor rest).mp readings |>.1
      cases cursor with
      | invoke frontier maps consumer =>
          exact invoke_step_preserves_rows construct callbackConstruct fallback
            frontier maps consumer rest first
      | body authored reading frame consumer =>
          change reading = .observe .noAnswers at first
          subst reading
          exact body_step_preserves_rows construct callbackConstruct fallback
            authored frame consumer rest

theorem deliver_preserves_sourceReadings (authored : List (Equation Value))
    (consumer : Consumer Item Value) (row : List Value)
    (rest : List (Cursor Item Value)) (readings : sourceReadings rest) :
    sourceReadings (deliver authored (.observe .noAnswers) row consumer rest).next.work := by
  induction consumer generalizing row with
  | emit => exact readings
  | concat first outer ih => exact ih (first ++ row)
  | times right items parameter maps outer ih =>
      simpa [deliver, Move.next, withPhase, sourceReadings_cons, Cursor.sourceReading]
        using readings

theorem finishInvoke_preserves_sourceReadings (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) (rows : List (List Value))
    (reading : frontier.reading = .observe .noAnswers) (readings : sourceReadings rest) :
    sourceReadings (finishInvoke frontier maps consumer rest rows).next.work := by
  cases rest <;>
    simp_all [finishInvoke, Move.next, withPhase, sourceReadings_cons, Cursor.sourceReading]

theorem stepRunning_preserves_sourceReadings (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (work : List (Cursor Item Value))
    (readings : sourceReadings work) :
    sourceReadings (stepRunning construct callbackConstruct fallback work).next.work := by
  cases work with
  | nil => exact sourceReadings_nil
  | cons cursor rest =>
      rcases (sourceReadings_cons cursor rest).mp readings with ⟨first, remaining⟩
      cases cursor with
      | invoke frontier maps consumer =>
          change frontier.reading = .observe .noAnswers at first
          cases phase : frontier.phase with
          | finished =>
              cases rest <;>
                simp [stepRunning, phase, Move.next, withPhase, Cursor.sourceReading,
                  first, remaining]
          | declined =>
              simpa [stepRunning, phase, Move.next, withPhase] using readings
          | running =>
              cases sealed : frontier.sealed with
              | true =>
                  simpa [stepRunning, phase, sealed] using
                    finishInvoke_preserves_sourceReadings frontier maps consumer rest [] first remaining
              | false =>
                  cases exposed : frontier.authored.drop frontier.ordinal with
                  | nil =>
                      cases matched : frontier.matched
                      · cases rest <;>
                          simp [stepRunning, phase, sealed, exposed, matched, first,
                            observeRuleBodies, finishInvoke, Move.next, withPhase,
                            sourceReadings_cons, Cursor.sourceReading, remaining]
                      · simpa [stepRunning, phase, sealed, exposed, matched] using
                          finishInvoke_preserves_sourceReadings frontier maps consumer rest [] first remaining
                  | cons equation later =>
                      cases hit : equation.head.matches frontier.items frontier.parameter <;>
                        simp [stepRunning, phase, sealed, exposed, hit, Move.next,
                          withPhase, sourceReadings_cons, Cursor.sourceReading, first, remaining]
      | body authored reading frame consumer =>
          change reading = .observe .noAnswers at first
          subst reading
          rcases frame with ⟨code, items, parameter, maps⟩
          cases code <;> cases items <;> cases parameter <;> simp only [stepRunning]
          all_goals first
            | exact deliver_preserves_sourceReadings authored consumer _ rest remaining
            | simpa [Move.next, withPhase, sourceReadings_cons, Cursor.sourceReading,
                openFrontier] using remaining

theorem step_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : State Item Value)
    (readings : sourceReadings state.work) :
    let moved := step construct callbackConstruct fallback state
    moved.rows ++ workRows construct callbackConstruct moved.next.work =
      workRows construct callbackConstruct state.work := by
  cases phase : state.phase with
  | running =>
      simpa [step, phase] using
        stepRunning_preserves_rows construct callbackConstruct fallback state.work readings
  | finished => simp [step, phase, Move.rows, Move.next]
  | declined => simp [step, phase, Move.rows, Move.next]
  | handoff => simp [step, phase, Move.rows, Move.next]

theorem step_preserves_sourceReadings (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : State Item Value)
    (readings : sourceReadings state.work) :
    sourceReadings (step construct callbackConstruct fallback state).next.work := by
  cases phase : state.phase with
  | running =>
      simpa [step, phase] using
        stepRunning_preserves_sourceReadings construct callbackConstruct fallback state.work readings
  | finished => simpa [step, phase, Move.next] using readings
  | declined => simpa [step, phase, Move.next] using readings
  | handoff => simpa [step, phase, Move.next] using readings

/-- Any finite allowance preserves every ordered occurrence: already emitted
rows followed by the retained computation equal the original source view.
The returned phase separately reports pending, completion, decline or handoff. -/
theorem drive_preserves_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (fuel : Nat) (state : State Item Value)
    (readings : sourceReadings state.work) :
    let result := drive construct callbackConstruct fallback fuel state
    result.1 ++ workRows construct callbackConstruct result.2.work =
      workRows construct callbackConstruct state.work := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have one := step_preserves_rows construct callbackConstruct fallback state readings
      have kept := step_preserves_sourceReadings construct callbackConstruct fallback state readings
      cases moved : step construct callbackConstruct fallback state with
      | advance next =>
          simp only [moved, Move.next] at kept
          simpa only [drive, moved, Move.rows, Move.next, List.nil_append] using
            (ih next kept).trans (by simpa only [moved, Move.rows, Move.next,
              List.nil_append] using one)
      | yield row next =>
          simp only [moved, Move.next] at kept
          have later := ih next kept
          simpa only [drive, moved, Move.rows, Move.next, List.cons_append,
            List.singleton_append, List.nil_append, later] using one
      | finish rows next => simpa only [drive, moved, Move.rows, Move.next] using one
      | decline next => simpa only [drive, moved, Move.rows, Move.next] using one
      | handoff next => simpa only [drive, moved, Move.rows, Move.next] using one

theorem drive_preserves_sourceReadings (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (fuel : Nat) (state : State Item Value)
    (readings : sourceReadings state.work) :
    sourceReadings (drive construct callbackConstruct fallback fuel state).2.work := by
  induction fuel generalizing state with
  | zero => exact readings
  | succ fuel ih =>
      have kept := step_preserves_sourceReadings construct callbackConstruct fallback state readings
      cases moved : step construct callbackConstruct fallback state with
      | advance next =>
          simp only [moved, Move.next] at kept
          simpa only [drive, moved] using ih next kept
      | yield row next =>
          simp only [moved, Move.next] at kept
          simpa only [drive, moved] using ih next kept
      | finish rows next => simpa only [drive, moved, Move.next] using kept
      | decline next => simpa only [drive, moved, Move.next] using kept
      | handoff next => simpa only [drive, moved, Move.next] using kept

theorem deliver_next_running (authored : List (Equation Value)) (reading : NoRuleReading)
    (consumer : Consumer Item Value) (row : List Value) (rest : List (Cursor Item Value)) :
    (deliver authored reading row consumer rest).next.phase = .running := by
  induction consumer generalizing row with
  | emit => rfl
  | concat first outer ih => exact ih (first ++ row)
  | times => rfl

theorem finishInvoke_finished_empty (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (frontier : RetainedFrontier Item Value) (maps : List (Mapper Item Value))
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (rows : List (List Value)) :
    (finishInvoke frontier maps consumer rest rows).next.phase = .finished →
      workRows construct callbackConstruct
        (finishInvoke frontier maps consumer rest rows).next.work = [] := by
  cases rest <;>
    simp [finishInvoke, Move.next, withPhase, workRows, cursorRows, invokeRows, mappedRows]

theorem stepRunning_finished_empty (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (work : List (Cursor Item Value)) :
    (stepRunning construct callbackConstruct fallback work).next.phase = .finished →
      workRows construct callbackConstruct
        (stepRunning construct callbackConstruct fallback work).next.work = [] := by
  fun_cases stepRunning construct callbackConstruct fallback work
  all_goals first
    | exact finishInvoke_finished_empty construct callbackConstruct _ _ _ _ _
    | solve
        | rw [deliver_next_running]
          intro impossible
          cases impossible
    | simp_all [declineInvoke, Move.next, withPhase, workRows, cursorRows,
        invokeRows, mappedRows]

theorem step_finished_empty (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : State Item Value)
    (initial : state.phase = .finished → workRows construct callbackConstruct state.work = []) :
    (step construct callbackConstruct fallback state).next.phase = .finished →
      workRows construct callbackConstruct
        (step construct callbackConstruct fallback state).next.work = [] := by
  cases phase : state.phase with
  | running =>
      simpa [step, phase] using
        stepRunning_finished_empty construct callbackConstruct fallback state.work
  | finished => simpa [step, phase, Move.next] using initial phase
  | declined => simp [step, phase, Move.next]
  | handoff => simp [step, phase, Move.next]

theorem drive_finished_empty (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (fuel : Nat) (state : State Item Value)
    (initial : state.phase = .finished → workRows construct callbackConstruct state.work = []) :
    (drive construct callbackConstruct fallback fuel state).2.phase = .finished →
      workRows construct callbackConstruct
        (drive construct callbackConstruct fallback fuel state).2.work = [] := by
  induction fuel generalizing state with
  | zero => exact initial
  | succ fuel ih =>
      have kept := step_finished_empty construct callbackConstruct fallback state initial
      cases moved : step construct callbackConstruct fallback state with
      | advance next =>
          simp only [moved, Move.next] at kept
          simpa only [drive, moved] using ih next kept
      | yield row next =>
          simp only [moved, Move.next] at kept
          simpa only [drive, moved] using ih next kept
      | finish rows next => simpa only [drive, moved, Move.next] using kept
      | decline next => simpa only [drive, moved, Move.next] using kept
      | handoff next => simpa only [drive, moved, Move.next] using kept

/-- Opening the shared cursor exposes the independent authored-equation
source, rather than a precomputed tail oracle or a new batch interpreter. -/
theorem openState_rows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) :
    workRows construct callbackConstruct
        (openState authored items parameter (.observe .noAnswers)).work =
      source construct callbackConstruct authored items parameter := by
  rw [source_eq_equationsRows]
  simp [openState, workRows, cursorRows, invokeRows, openFrontier, mappedRows,
    applyMaps, bindConsumer]

/-- The prefix and exact retained suffix of any bounded authored call have
the full source meaning. Exhausted allowance is not an empty source result. -/
theorem drive_open_preserves_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (items : List Item) (parameter fuel : Nat) :
    let result := drive construct callbackConstruct fallback fuel
      (openState authored items parameter (.observe .noAnswers))
    result.1 ++ workRows construct callbackConstruct result.2.work =
      source construct callbackConstruct authored items parameter := by
  rw [← openState_rows construct callbackConstruct authored items parameter]
  apply drive_preserves_rows
  simp [openState, sourceReadings_cons, Cursor.sourceReading, openFrontier]

/-- Every emitted finite prefix is a source prefix, including duplicates and
empty returned collections. Pending work is the witness for the suffix. -/
theorem drive_open_source_prefix (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (items : List Item) (parameter fuel : Nat) :
    (drive construct callbackConstruct fallback fuel
      (openState authored items parameter (.observe .noAnswers))).1.IsPrefix
        (source construct callbackConstruct authored items parameter) := by
  exact ⟨_, drive_open_preserves_source construct callbackConstruct fallback
    authored items parameter fuel⟩

/-- A completed bounded call has every source occurrence, in source order.
This theorem does not assert that an arbitrary allowance reaches completion. -/
theorem drive_open_finished_eq_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (items : List Item) (parameter fuel : Nat)
    (finished : (drive construct callbackConstruct fallback fuel
      (openState authored items parameter (.observe .noAnswers))).2.phase = .finished) :
    (drive construct callbackConstruct fallback fuel
      (openState authored items parameter (.observe .noAnswers))).1 =
        source construct callbackConstruct authored items parameter := by
  have empty := drive_finished_empty construct callbackConstruct fallback fuel
    (openState authored items parameter (.observe .noAnswers))
    (by simp [openState]) finished
  have correct := drive_open_preserves_source construct callbackConstruct fallback
    authored items parameter fuel
  simpa only [empty, List.append_nil] using correct

#print axioms drive_open_preserves_source
#print axioms drive_open_source_prefix
#print axioms drive_open_finished_eq_source
#print axioms drive_preserves_rows
#print axioms stepRunning_preserves_rows
#print axioms stepRunning_preserves_sourceReadings
#print axioms deliver_preserves_rows

#print axioms unsupported_hands_off
#print axioms drive_keeps_a_terminal_phase

/-! Total execution and suspension laws for the same body/call transition. -/

private theorem deliver_terminal_phase (authored : List (Equation Value))
    (reading : NoRuleReading) (consumer : Consumer Item Value) (occurrence : List Value)
    (rest : List (Cursor Item Value)) :
    match deliver authored reading occurrence consumer rest with
    | .advance _ | .yield _ _ => True
    | .finish _ next | .decline next | .handoff next => next.phase ≠ .running := by
  induction consumer generalizing occurrence with
  | emit => trivial
  | concat first outer ih => exact ih (first ++ occurrence)
  | times right items parameter maps outer ih => trivial

private theorem stepRunning_terminal_phase (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (work : List (Cursor Item Value)) :
    match stepRunning construct callbackConstruct fallback work with
    | .advance _ | .yield _ _ => True
    | .finish _ next | .decline next | .handoff next => next.phase ≠ .running := by
  cases work with
  | nil => simp [stepRunning, withPhase]
  | cons cursor rest =>
      cases cursor with
      | invoke frontier maps consumer =>
          cases phase : frontier.phase with
          | finished =>
              cases rest <;> simp [stepRunning, phase, withPhase]
          | declined => simp [stepRunning, phase, withPhase]
          | running =>
              cases sealed : frontier.sealed with
              | true =>
                  cases rest <;> simp [stepRunning, phase, sealed, finishInvoke, withPhase]
              | false =>
                  cases remaining : frontier.authored.drop frontier.ordinal with
                  | cons equation tail =>
                      cases hit : equation.head.matches frontier.items frontier.parameter <;>
                        simp [stepRunning, phase, sealed, remaining, hit]
                  | nil =>
                      cases matched : frontier.matched with
                      | true =>
                          cases rest <;>
                            simp [stepRunning, phase, sealed, remaining, matched,
                              finishInvoke, withPhase]
                      | false =>
                          cases reading : frontier.reading with
                          | decline =>
                              simp [stepRunning, phase, sealed, remaining, matched,
                                reading, declineInvoke, withPhase]
                          | observe policy =>
                              cases policy <;> cases rest <;>
                                simp only [stepRunning, phase, sealed, remaining,
                                  matched, reading, observeRuleBodies, List.isEmpty,
                                  Bool.false_eq_true, ↓reduceIte,
                                  finishInvoke, withPhase]
                              all_goals first
                                | exact deliver_terminal_phase _ _ _ _ _
                                | simp
      | body authored reading frame consumer =>
          rcases frame with ⟨code, items, parameter, maps⟩
          cases code <;> cases items <;> cases parameter <;>
            simp [stepRunning, withPhase]
          all_goals exact deliver_terminal_phase _ _ _ _ _

private theorem step_terminal_phase (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value) :
    match BodyCall.step construct callbackConstruct fallback state with
    | .advance _ | .yield _ _ => True
    | .finish _ next | .decline next | .handoff next => next.phase ≠ .running := by
  cases phase : state.phase with
  | running =>
      simpa only [BodyCall.step, phase] using
        stepRunning_terminal_phase construct callbackConstruct fallback state.work
  | finished => simp [BodyCall.step, phase]
  | declined => simp [BodyCall.step, phase]
  | handoff => simp [BodyCall.step, phase]

/-- Splitting a body/call allowance retains exactly the same ordered
occurrences and full cursor state as one combined drive. Terminal, declined
and handed-off residuals keep their stored phase and every saved frame. -/
theorem drive_split_resumes (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (earlier later : Nat)
    (state : BodyCall.State Item Value) :
    ((BodyCall.drive construct callbackConstruct fallback earlier state).1 ++
        (BodyCall.drive construct callbackConstruct fallback later
          (BodyCall.drive construct callbackConstruct fallback earlier state).2).1,
      (BodyCall.drive construct callbackConstruct fallback later
        (BodyCall.drive construct callbackConstruct fallback earlier state).2).2) =
      BodyCall.drive construct callbackConstruct fallback (earlier + later) state := by
  induction earlier generalizing state with
  | zero => simp only [BodyCall.drive, Nat.zero_add, List.nil_append]
  | succ earlier ih =>
      have add : earlier + 1 + later = (earlier + later) + 1 := by
        rw [Nat.add_assoc, Nat.add_comm 1 later, ← Nat.add_assoc]
      cases moved : BodyCall.step construct callbackConstruct fallback state with
      | advance next =>
          simp only [BodyCall.drive, moved, add]
          exact ih next
      | yield occurrence next =>
          simp only [BodyCall.drive, moved, add]
          rw [← ih next]
          simp only [List.cons_append]
      | finish occurrences next =>
          have stopped := step_terminal_phase construct callbackConstruct fallback state
          simp only [moved] at stopped
          have stable := drive_keeps_a_terminal_phase construct callbackConstruct fallback
            later next stopped
          simp only [BodyCall.drive, moved, add, stable, List.append_nil]
      | decline next =>
          have stopped := step_terminal_phase construct callbackConstruct fallback state
          simp only [moved] at stopped
          have stable := drive_keeps_a_terminal_phase construct callbackConstruct fallback
            later next stopped
          simp only [BodyCall.drive, moved, add, stable, List.nil_append]
      | handoff next =>
          have stopped := step_terminal_phase construct callbackConstruct fallback state
          simp only [moved] at stopped
          have stable := drive_keeps_a_terminal_phase construct callbackConstruct fallback
            later next stopped
          simp only [BodyCall.drive, moved, add, stable, List.nil_append]

#print axioms drive_split_resumes

/-- Extending the allowance after any terminal result preserves its complete
output and stored state, including finished, declined and handoff phases. -/
theorem drive_terminal_extension (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (earlier later : Nat)
    (state : BodyCall.State Item Value)
    (stopped : (BodyCall.drive construct callbackConstruct fallback earlier state).2.phase ≠
      .running) :
    BodyCall.drive construct callbackConstruct fallback (earlier + later) state =
      BodyCall.drive construct callbackConstruct fallback earlier state := by
  have split := drive_split_resumes construct callbackConstruct fallback earlier later state
  rw [drive_keeps_a_terminal_phase construct callbackConstruct fallback later _ stopped] at split
  simpa only [List.append_nil] using split.symm

#print axioms drive_terminal_extension

private def rankBase (authored : List (Equation Value)) : Nat → Nat
  | 0 => 2
  | depth + 1 =>
      3 + (authored.map (fun equation =>
        rankBase authored depth ^ equation.body.weight + 1)).sum

private def codeRank (authored : List (Equation Value)) (items : List Item)
    (code : Code Value) : Nat :=
  rankBase authored items.length ^ code.weight

private def invokeRank (authored : List (Equation Value)) (items : List Item)
    (ordinal : Nat) : Nat :=
  2 + ((authored.drop ordinal).map (fun equation => codeRank authored items equation.body + 1)).sum

private def consumerRank (authored : List (Equation Value)) : Consumer Item Value → Nat
  | .emit => 1
  | .concat _ outer => consumerRank authored outer
  | .times right items _ _ outer =>
      1 + codeRank authored items right * consumerRank authored outer

private def cursorRank : Cursor Item Value → Nat
  | .invoke frontier _ consumer =>
      invokeRank frontier.authored frontier.items frontier.ordinal *
        consumerRank frontier.authored consumer
  | .body authored _ frame consumer =>
      codeRank authored frame.items frame.code * consumerRank authored consumer

private def workRank : List (Cursor Item Value) → Nat
  | [] => 0
  | cursor :: rest => cursorRank cursor + workRank rest

private theorem rankBase_two_le (authored : List (Equation Value)) (depth : Nat) :
    2 ≤ rankBase authored depth := by
  cases depth <;> simp only [rankBase] <;> omega

private theorem codeRank_two_le (authored : List (Equation Value)) (items : List Item)
    (code : Code Value) : 2 ≤ codeRank authored items code :=
  (rankBase_two_le authored items.length).trans (Nat.le_pow code.weight_pos)

private theorem consumerRank_pos (authored : List (Equation Value))
    (consumer : Consumer Item Value) : 0 < consumerRank authored consumer := by
  cases consumer <;> simp [consumerRank]
  case concat first outer => exact consumerRank_pos authored outer

private theorem cursorRank_pos (cursor : Cursor Item Value) : 0 < cursorRank cursor := by
  cases cursor with
  | invoke frontier maps consumer =>
      exact Nat.mul_pos (by simp [invokeRank]) (consumerRank_pos _ _)
  | body authored reading frame consumer =>
      exact Nat.mul_pos (by have := codeRank_two_le authored frame.items frame.code; omega)
        (consumerRank_pos _ _)

private theorem codeRank_lt (authored : List (Equation Value)) (items : List Item)
    (earlier later : Code Value) (smaller : earlier.weight < later.weight) :
    codeRank authored items earlier < codeRank authored items later := by
  exact Nat.pow_lt_pow_right (by have := rankBase_two_le authored items.length; omega) smaller

private theorem invokeRank_next (authored : List (Equation Value)) (items : List Item)
    (ordinal : Nat) (equation : Equation Value) (remaining : List (Equation Value))
    (exposed : authored.drop ordinal = equation :: remaining) :
    invokeRank authored items ordinal = codeRank authored items equation.body + 1 +
      invokeRank authored items (ordinal + 1) := by
  simp [invokeRank, List.drop_add_one_eq_tail_drop, exposed]
  omega

private theorem callRank_decreases (authored : List (Equation Value))
    (head : Item) (tail : List Item) :
    invokeRank authored tail 0 < codeRank authored (head :: tail) .callTail := by
  simp [invokeRank, codeRank, Code.weight, rankBase]

private theorem appendRank_decreases (authored : List (Equation Value)) (items : List Item)
    (left right : Code Value) (consumer : Consumer Item Value) :
    codeRank authored items left *
        (1 + codeRank authored items right * consumerRank authored consumer) <
      codeRank authored items (.append left right) * consumerRank authored consumer := by
  have base := rankBase_two_le authored items.length
  have rightTwo := codeRank_two_le authored items right
  have positive := consumerRank_pos authored consumer
  have productTwo : 2 ≤ codeRank authored items right * consumerRank authored consumer :=
    rightTwo.trans (Nat.le_mul_of_pos_right _ positive)
  have scaled := Nat.mul_le_mul_right
    (codeRank authored items right * consumerRank authored consumer) base
  have growth : 1 + codeRank authored items right * consumerRank authored consumer <
      codeRank authored items right * rankBase authored items.length *
        consumerRank authored consumer := by
    nlinarith
  have leftPositive : 0 < codeRank authored items left := by
    have := codeRank_two_le authored items left
    omega
  have scaledGrowth := Nat.mul_lt_mul_of_pos_left growth leftPositive
  simpa only [codeRank, Code.weight, Nat.pow_add, Nat.pow_one, Nat.mul_assoc] using scaledGrowth

private def advancesBelow (moved : Move Item Value) (before : Nat) : Prop :=
  match moved with
  | .advance next | .yield _ next => workRank next.work < before
  | .finish _ _ | .decline _ | .handoff _ => True

private theorem advancesBelow_mono (moved : Move Item Value) (earlier later : Nat)
    (decreases : advancesBelow moved earlier) (enough : earlier ≤ later) :
    advancesBelow moved later := by
  cases moved <;> simp only [advancesBelow] at * <;> omega

private theorem deliver_rank_decreases (authored : List (Equation Value))
    (reading : NoRuleReading) (consumer : Consumer Item Value) (row : List Value)
    (rest : List (Cursor Item Value)) :
    advancesBelow (deliver authored reading row consumer rest)
      (consumerRank authored consumer + workRank rest) := by
  induction consumer generalizing row with
  | emit => simp [deliver, advancesBelow, withPhase, consumerRank]
  | concat first outer ih => exact ih (first ++ row)
  | times right items parameter maps outer ih =>
      simp [deliver, advancesBelow, withPhase, consumerRank, workRank, cursorRank]

private theorem workRank_tail_lt (cursor : Cursor Item Value)
    (rest : List (Cursor Item Value)) : workRank rest < workRank (cursor :: rest) := by
  simp only [workRank]
  have := cursorRank_pos cursor
  omega

private theorem finishInvoke_rank_decreases (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) (rows : List (List Value)) :
    advancesBelow (finishInvoke frontier maps consumer rest rows)
      (workRank (.invoke frontier maps consumer :: rest)) := by
  cases rest with
  | nil => trivial
  | cons cursor rest =>
      exact workRank_tail_lt (.invoke frontier maps consumer) (cursor :: rest)

private theorem deliver_body_rank_decreases (authored : List (Equation Value))
    (reading : NoRuleReading) (frame : Frame Item Value) (consumer : Consumer Item Value)
    (row : List Value) (rest : List (Cursor Item Value)) :
    advancesBelow (deliver authored reading row consumer rest)
      (workRank (.body authored reading frame consumer :: rest)) := by
  apply advancesBelow_mono _ _ _ (deliver_rank_decreases authored reading consumer row rest)
  simp only [workRank, cursorRank]
  exact Nat.add_le_add_right
    (Nat.le_mul_of_pos_left _ (by have := codeRank_two_le authored frame.items frame.code; omega)) _

private theorem deliver_invoke_rank_decreases (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value)
    (row : List Value) (rest : List (Cursor Item Value)) :
    advancesBelow (deliver frontier.authored frontier.reading row consumer rest)
      (workRank (.invoke frontier maps consumer :: rest)) := by
  apply advancesBelow_mono _ _ _
    (deliver_rank_decreases frontier.authored frontier.reading consumer row rest)
  simp only [workRank, cursorRank]
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by simp [invokeRank])) _

private theorem invoke_body_rank_decreases (authored : List (Equation Value))
    (items : List Item) (ordinal : Nat) (equation : Equation Value)
    (remaining : List (Equation Value)) (consumer : Consumer Item Value) (suffix : Nat)
    (exposed : authored.drop ordinal = equation :: remaining) :
    codeRank authored items equation.body * consumerRank authored consumer +
        (invokeRank authored items (ordinal + 1) * consumerRank authored consumer + suffix) <
      invokeRank authored items ordinal * consumerRank authored consumer + suffix := by
  rw [invokeRank_next authored items ordinal equation remaining exposed]
  have := consumerRank_pos authored consumer
  nlinarith

private theorem invoke_skip_rank_decreases (authored : List (Equation Value))
    (items : List Item) (ordinal : Nat) (equation : Equation Value)
    (remaining : List (Equation Value)) (consumer : Consumer Item Value) (suffix : Nat)
    (exposed : authored.drop ordinal = equation :: remaining) :
    invokeRank authored items (ordinal + 1) * consumerRank authored consumer + suffix <
      invokeRank authored items ordinal * consumerRank authored consumer + suffix := by
  rw [invokeRank_next authored items ordinal equation remaining exposed]
  have := consumerRank_pos authored consumer
  nlinarith

private theorem stepRunning_rank_decreases (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (work : List (Cursor Item Value)) :
    advancesBelow (stepRunning construct callbackConstruct fallback work) (workRank work) := by
  fun_cases stepRunning construct callbackConstruct fallback work
  all_goals first
    | exact True.intro
    | exact finishInvoke_rank_decreases _ _ _ _ _
    | exact deliver_body_rank_decreases _ _ _ _ _ _
    | exact deliver_invoke_rank_decreases _ _ _ _ _
    | exact workRank_tail_lt _ _
    | simp only [advancesBelow, withPhase, workRank, cursorRank]
  case case12 =>
    rename_i frontier maps consumer rest phase unsealed equation remaining exposed hit nextFrontier
    exact invoke_body_rank_decreases _ _ _ _ _ _ _ exposed
  case case13 =>
    rename_i frontier maps consumer rest phase unsealed equation remaining exposed miss
    exact invoke_skip_rank_decreases _ _ _ _ _ _ _ exposed
  all_goals simp_all only [openFrontier, consumerRank]
  all_goals first
    | exact Nat.add_lt_add_right (appendRank_decreases _ _ _ _ _) _
    | exact Nat.add_lt_add_right
        (Nat.mul_lt_mul_of_pos_right (callRank_decreases _ _ _) (consumerRank_pos _ _)) _
    | solve
        | apply Nat.add_lt_add_right
          apply Nat.mul_lt_mul_of_pos_right _ (consumerRank_pos _ _)
          apply codeRank_lt
          simp_all only [Code.weight]
          omega

private theorem step_rank_decreases (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value) :
    advancesBelow (BodyCall.step construct callbackConstruct fallback state)
      (workRank state.work) := by
  cases phase : state.phase with
  | running =>
      simpa only [BodyCall.step, phase] using
        stepRunning_rank_decreases construct callbackConstruct fallback state.work
  | finished => simp [BodyCall.step, phase, advancesBelow]
  | declined => simp [BodyCall.step, phase, advancesBelow]
  | handoff => simp [BodyCall.step, phase, advancesBelow]

/-- Every finite body/call cursor reaches a stored stop phase after some
finite allowance. The proof rank uses authored syntax and captures only;
it neither computes source answers nor supplies an executable fuel bound. -/
theorem drive_eventually_stops (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value) :
    ∃ fuel, (BodyCall.drive construct callbackConstruct fallback fuel state).2.phase ≠ .running := by
  by_cases running : state.phase = .running
  · have terminal := step_terminal_phase construct callbackConstruct fallback state
    cases moved : BodyCall.step construct callbackConstruct fallback state with
    | advance next =>
        obtain ⟨fuel, stopped⟩ := drive_eventually_stops construct callbackConstruct fallback next
        exact ⟨fuel + 1, by simpa only [BodyCall.drive, moved] using stopped⟩
    | yield row next =>
        obtain ⟨fuel, stopped⟩ := drive_eventually_stops construct callbackConstruct fallback next
        exact ⟨fuel + 1, by simpa only [BodyCall.drive, moved] using stopped⟩
    | finish rows next =>
        simp only [moved] at terminal
        exact ⟨1, by simpa only [BodyCall.drive, moved] using terminal⟩
    | decline next =>
        simp only [moved] at terminal
        exact ⟨1, by simpa only [BodyCall.drive, moved] using terminal⟩
    | handoff next =>
        simp only [moved] at terminal
        exact ⟨1, by simpa only [BodyCall.drive, moved] using terminal⟩
  · exact ⟨0, running⟩
termination_by workRank state.work
decreasing_by
  all_goals
    have decreases := step_rank_decreases construct callbackConstruct fallback state
    simpa only [moved, advancesBelow] using decreases

#print axioms drive_eventually_stops

/-- Run the existing transition until its stored terminal result. The rank
proves recursion terminates; no numerical fuel bound is computed at runtime. -/
def collect (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value) :
    List (List Value) × BodyCall.State Item Value :=
  match _moved : BodyCall.step construct callbackConstruct fallback state with
  | .advance next => collect construct callbackConstruct fallback next
  | .yield row next =>
      let later := collect construct callbackConstruct fallback next
      (row :: later.1, later.2)
  | .finish rows next => (rows, next)
  | .decline next => ([], next)
  | .handoff next => ([], next)
termination_by workRank state.work
decreasing_by
  all_goals
    have decreases := step_rank_decreases construct callbackConstruct fallback state
    simpa only [_moved, advancesBelow] using decreases

/-- The total collector is exactly a finite drive, with the same ordered
occurrences and complete terminal State. -/
theorem collect_eq_drive (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value) :
    ∃ fuel, collect construct callbackConstruct fallback state =
        BodyCall.drive construct callbackConstruct fallback fuel state ∧
      (BodyCall.drive construct callbackConstruct fallback fuel state).2.phase ≠ .running := by
  have terminal := step_terminal_phase construct callbackConstruct fallback state
  cases moved : BodyCall.step construct callbackConstruct fallback state with
  | advance next =>
      obtain ⟨fuel, same, stopped⟩ := collect_eq_drive construct callbackConstruct fallback next
      refine ⟨fuel + 1, ?_, ?_⟩
      · rw [collect, moved, BodyCall.drive, moved]
        exact same
      · simpa only [BodyCall.drive, moved] using stopped
  | yield row next =>
      obtain ⟨fuel, same, stopped⟩ := collect_eq_drive construct callbackConstruct fallback next
      refine ⟨fuel + 1, ?_, ?_⟩
      · rw [collect, moved, BodyCall.drive, moved]
        exact congrArg
          (fun later : List (List Value) × BodyCall.State Item Value => (row :: later.1, later.2)) same
      · simpa only [BodyCall.drive, moved] using stopped
  | finish rows next =>
      simp only [moved] at terminal
      exact ⟨1, by rw [collect, moved, BodyCall.drive, moved],
        by simpa only [BodyCall.drive, moved] using terminal⟩
  | decline next =>
      simp only [moved] at terminal
      exact ⟨1, by rw [collect, moved, BodyCall.drive, moved],
        by simpa only [BodyCall.drive, moved] using terminal⟩
  | handoff next =>
      simp only [moved] at terminal
      exact ⟨1, by rw [collect, moved, BodyCall.drive, moved],
        by simpa only [BodyCall.drive, moved] using terminal⟩
termination_by workRank state.work
decreasing_by
  all_goals
    have decreases := step_rank_decreases construct callbackConstruct fallback state
    simpa only [moved, advancesBelow] using decreases

#print axioms collect
#print axioms collect_eq_drive

/-- The existing finite instruction grammar, checked once per authored
program before choosing the total body/call execution path. -/
def supportedProgram (authored : List (Equation Value)) : Bool :=
  authored.all (fun equation => optionalSupported equation.body)

theorem supportedProgram_iff (authored : List (Equation Value)) :
    supportedProgram authored = true ↔
      ∀ equation ∈ authored, optionalSupported equation.body = true := by
  simp [supportedProgram, List.all_eq_true]

private def consumerSupported : Consumer Item Value → Prop
  | .emit => True
  | .concat _ outer => consumerSupported outer
  | .times right _ _ _ outer => optionalSupported right = true ∧ consumerSupported outer

private def cursorSupported : Cursor Item Value → Prop
  | .invoke frontier _ consumer =>
      (∀ equation ∈ frontier.authored, optionalSupported equation.body = true) ∧
        frontier.phase ≠ .declined ∧ consumerSupported consumer
  | .body authored _ frame consumer =>
      (∀ equation ∈ authored, optionalSupported equation.body = true) ∧
        optionalSupported frame.code = true ∧ consumerSupported consumer

private def workSupported : List (Cursor Item Value) → Prop
  | [] => True
  | cursor :: rest => cursorSupported cursor ∧ workSupported rest

private theorem deliver_supported (authored : List (Equation Value))
    (reading : NoRuleReading) (consumer : Consumer Item Value) (row : List Value)
    (rest : List (Cursor Item Value))
    (program : ∀ equation ∈ authored, optionalSupported equation.body = true)
    (context : consumerSupported consumer) (remaining : workSupported rest) :
    workSupported (deliver authored reading row consumer rest).next.work ∧
      (deliver authored reading row consumer rest).next.phase = .running := by
  induction consumer generalizing row with
  | emit => exact ⟨remaining, rfl⟩
  | concat first outer ih => exact ih (first ++ row) context
  | times right items parameter maps outer ih =>
      exact ⟨⟨⟨program, context.1, context.2⟩, remaining⟩, rfl⟩

private theorem finishInvoke_supported (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) (rows : List (List Value))
    (supports : workSupported (.invoke frontier maps consumer :: rest)) :
    workSupported (finishInvoke frontier maps consumer rest rows).next.work ∧
      ((finishInvoke frontier maps consumer rest rows).next.phase = .running ∨
        (finishInvoke frontier maps consumer rest rows).next.phase = .finished) := by
  cases rest <;>
    simp_all [finishInvoke, Move.next, withPhase, workSupported, cursorSupported]

private theorem exposed_body_supported (authored : List (Equation Value)) (ordinal : Nat)
    (equation : Equation Value) (remaining : List (Equation Value))
    (program : ∀ equation ∈ authored, optionalSupported equation.body = true)
    (exposed : authored.drop ordinal = equation :: remaining) :
    optionalSupported equation.body = true := by
  apply program equation
  apply List.mem_of_mem_drop (i := ordinal)
  simp [exposed]

private theorem stepRunning_supported (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (work : List (Cursor Item Value))
    (supports : workSupported work) (readings : sourceReadings work) :
    workSupported (stepRunning construct callbackConstruct fallback work).next.work ∧
      ((stepRunning construct callbackConstruct fallback work).next.phase = .running ∨
        (stepRunning construct callbackConstruct fallback work).next.phase = .finished) := by
  fun_cases stepRunning construct callbackConstruct fallback work
  all_goals first
    | exact finishInvoke_supported _ _ _ _ _ supports
    | simp_all [Move.next, withPhase, workSupported, cursorSupported, consumerSupported,
        sourceReadings_cons, Cursor.sourceReading, optionalSupported, openFrontier]
  case case12 =>
    constructor
    · exact exposed_body_supported _ _ _ _ supports.1.1 (by assumption)
    · exact ⟨supports.1.1, by simp_all +zetaDelta⟩
  all_goals
    obtain ⟨kept, running⟩ :=
      deliver_supported _ _ _ _ _ supports.1.1 supports.1.2 supports.2
    exact ⟨kept, Or.inl running⟩

private def sourceSafe (state : BodyCall.State Item Value) : Prop :=
  workSupported state.work ∧ sourceReadings state.work ∧
    (state.phase = .running ∨ state.phase = .finished)

private theorem step_sourceSafe (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value)
    (safe : sourceSafe state) :
    sourceSafe (BodyCall.step construct callbackConstruct fallback state).next := by
  obtain ⟨supports, readings, phases⟩ := safe
  have keptReadings := step_preserves_sourceReadings construct callbackConstruct fallback state readings
  rcases phases with running | finished
  · obtain ⟨kept, phases⟩ := stepRunning_supported construct callbackConstruct fallback
      state.work supports readings
    exact ⟨by simpa only [BodyCall.step, running] using kept, keptReadings,
      by simpa only [BodyCall.step, running] using phases⟩
  · simpa only [BodyCall.step, finished, Move.next] using
      (show sourceSafe state from ⟨supports, readings, Or.inr finished⟩)

private theorem drive_sourceSafe (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (fuel : Nat) (state : BodyCall.State Item Value)
    (safe : sourceSafe state) :
    sourceSafe (BodyCall.drive construct callbackConstruct fallback fuel state).2 := by
  induction fuel generalizing state with
  | zero => exact safe
  | succ fuel ih =>
      have kept := step_sourceSafe construct callbackConstruct fallback state safe
      cases moved : BodyCall.step construct callbackConstruct fallback state with
      | advance next =>
          simp only [moved, Move.next] at kept
          simpa only [BodyCall.drive, moved] using ih next kept
      | yield row next =>
          simp only [moved, Move.next] at kept
          simpa only [BodyCall.drive, moved] using ih next kept
      | finish rows next => simpa only [BodyCall.drive, moved, Move.next] using kept
      | decline next => simpa only [BodyCall.drive, moved, Move.next] using kept
      | handoff next => simpa only [BodyCall.drive, moved, Move.next] using kept

private theorem openState_sourceSafe (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) (supported : supportedProgram authored = true) :
    sourceSafe (BodyCall.openState authored items parameter (.observe .noAnswers)) := by
  have program := (supportedProgram_iff authored).mp supported
  simpa [sourceSafe, BodyCall.openState, workSupported, cursorSupported, consumerSupported,
    sourceReadings_cons, Cursor.sourceReading, openFrontier] using program

/-- Supported source-reading execution reaches `finished`, rather than
merely stopping at decline or unsupported handoff. -/
theorem drive_open_eventually_finished (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) (supported : supportedProgram authored = true) :
    ∃ fuel, (BodyCall.drive construct callbackConstruct fallback fuel
      (BodyCall.openState authored items parameter (.observe .noAnswers))).2.phase = .finished := by
  obtain ⟨fuel, stopped⟩ := drive_eventually_stops construct callbackConstruct fallback
    (BodyCall.openState authored items parameter (.observe .noAnswers))
  have safe := drive_sourceSafe construct callbackConstruct fallback fuel _
    (openState_sourceSafe authored items parameter supported)
  exact ⟨fuel, safe.2.2.resolve_left stopped⟩

theorem collect_open_finished (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) (supported : supportedProgram authored = true) :
    (collect construct callbackConstruct fallback
      (BodyCall.openState authored items parameter (.observe .noAnswers))).2.phase = .finished := by
  obtain ⟨fuel, same, stopped⟩ := collect_eq_drive construct callbackConstruct fallback
    (BodyCall.openState authored items parameter (.observe .noAnswers))
  have safe := drive_sourceSafe construct callbackConstruct fallback fuel _
    (openState_sourceSafe authored items parameter supported)
  rw [same]
  exact safe.2.2.resolve_left stopped

/-- The total supported body/call collector returns every occurrence of
the independent authored source in its original order. -/
theorem collect_open_eq_source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) (supported : supportedProgram authored = true) :
    (collect construct callbackConstruct fallback
      (BodyCall.openState authored items parameter (.observe .noAnswers))).1 =
        source construct callbackConstruct authored items parameter := by
  obtain ⟨fuel, same, stopped⟩ := collect_eq_drive construct callbackConstruct fallback
    (BodyCall.openState authored items parameter (.observe .noAnswers))
  have finished := collect_open_finished construct callbackConstruct fallback authored items parameter supported
  rw [same] at finished ⊢
  exact drive_open_finished_eq_source construct callbackConstruct fallback authored items parameter fuel finished

#print axioms drive_open_eventually_finished
#print axioms collect_open_finished
#print axioms collect_open_eq_source

/-- Any known stopped allowance computes the exact same pair as the total
collector. This compares the complete retained State as well as its rows. -/
theorem collect_eq_stopped_drive (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value)
    (fuel : Nat)
    (stopped : (BodyCall.drive construct callbackConstruct fallback fuel state).2.phase ≠ .running) :
    collect construct callbackConstruct fallback state =
      BodyCall.drive construct callbackConstruct fallback fuel state := by
  obtain ⟨enough, same, stoppedEnough⟩ :=
    collect_eq_drive construct callbackConstruct fallback state
  rw [same]
  calc
    BodyCall.drive construct callbackConstruct fallback enough state =
        BodyCall.drive construct callbackConstruct fallback (enough + fuel) state :=
      (drive_terminal_extension construct callbackConstruct fallback enough fuel state stoppedEnough).symm
    _ = BodyCall.drive construct callbackConstruct fallback (fuel + enough) state := by
      rw [Nat.add_comm enough fuel]
    _ = BodyCall.drive construct callbackConstruct fallback fuel state :=
      drive_terminal_extension construct callbackConstruct fallback fuel enough state stopped

/-- A bounded caller and the total collector compose through the same
retained cursor; no emitted occurrence or caller frame is replayed. -/
theorem drive_then_collect (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (fallback : List Item → Nat → List Value) (state : BodyCall.State Item Value)
    (fuel : Nat) :
    ((BodyCall.drive construct callbackConstruct fallback fuel state).1 ++
      (collect construct callbackConstruct fallback
        (BodyCall.drive construct callbackConstruct fallback fuel state).2).1,
      (collect construct callbackConstruct fallback
        (BodyCall.drive construct callbackConstruct fallback fuel state).2).2) =
        collect construct callbackConstruct fallback state := by
  obtain ⟨later, same, stopped⟩ := collect_eq_drive construct callbackConstruct fallback
    (BodyCall.drive construct callbackConstruct fallback fuel state).2
  rw [same, drive_split_resumes]
  apply (collect_eq_stopped_drive construct callbackConstruct fallback state (fuel + later) ?_).symm
  have split := drive_split_resumes construct callbackConstruct fallback fuel later state
  rw [← split]
  exact stopped

#print axioms collect_eq_stopped_drive
#print axioms drive_then_collect

namespace Graded

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler

/-- A physical source equation activation, before executing its body. The
capture retains the actual ordinal, inputs and lexical continuation. -/
structure Activation (Item : Type u) (Value : Type v) where
  frontier : RetainedFrontier Item Value
  maps : List (Mapper Item Value)
  consumer : Consumer Item Value
  equation : Equation Value

def activation? (state : BodyCall.State Item Value) : Option (Activation Item Value) :=
  match state.phase, state.work with
  | .running, .invoke frontier maps consumer :: _ =>
      match frontier.phase with
      | .running =>
          if frontier.sealed then none
          else match frontier.authored.drop frontier.ordinal with
            | equation :: _ =>
                if equation.head.matches frontier.items frontier.parameter then
                  some ⟨frontier, maps, consumer, equation⟩
                else none
            | [] => none
      | _ => none
  | _, _ => none

theorem activation_at (frontier : RetainedFrontier Item Value) (maps : List (Mapper Item Value))
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (equation : Equation Value) (later : List (Equation Value))
    (running : frontier.phase = .running) (unsealed : frontier.sealed = false)
    (selected : frontier.authored.drop frontier.ordinal = equation :: later)
    (matched : equation.head.matches frontier.items frontier.parameter = true) :
    activation? (withPhase .running (.invoke frontier maps consumer :: rest)) =
      some ⟨frontier, maps, consumer, equation⟩ := by
  simp [activation?, withPhase, running, unsealed, selected, matched]

/-- An activation extracted from the actual cursor is licensed by the
captured authored equation and its actual input match. -/
theorem activation_origin (state : BodyCall.State Item Value) (activation : Activation Item Value)
    (selected : activation? state = some activation) :
    ∃ rest later, state.phase = .running ∧
      state.work = .invoke activation.frontier activation.maps activation.consumer :: rest ∧
      activation.frontier.phase = .running ∧ activation.frontier.sealed = false ∧
      activation.frontier.authored.drop activation.frontier.ordinal = activation.equation :: later ∧
      activation.equation.head.matches activation.frontier.items activation.frontier.parameter = true := by
  cases phase : state.phase <;> simp only [activation?, phase] at selected
  all_goals first | contradiction | skip
  cases work : state.work with
  | nil => simp [work] at selected
  | cons cursor rest =>
      cases cursor with
      | body authored reading frame consumer => simp [work] at selected
      | invoke frontier maps consumer =>
          cases running : frontier.phase <;> simp only [work, running] at selected
          all_goals first | contradiction | skip
          cases sealed : frontier.sealed <;> simp only [sealed, Bool.false_eq_true, ↓reduceIte] at selected
          all_goals first | contradiction | skip
          cases remaining : frontier.authored.drop frontier.ordinal with
          | nil => simp [remaining] at selected
          | cons equation later =>
              cases matched : equation.head.matches frontier.items frontier.parameter <;>
                simp only [remaining, matched, Bool.false_eq_true, ↓reduceIte] at selected
              all_goals first | contradiction | skip
              cases selected
              exact ⟨rest, later, rfl, rfl, running, sealed, remaining, matched⟩

/-- The sole firing edge pushes the actual body and preserves an independent
alternative invocation. No body instruction or answer probe is performed. -/
theorem activation_pushes (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Item → Nat → List Value)
    (state : BodyCall.State Item Value) (activation : Activation Item Value)
    (selected : activation? state = some activation) :
    ∃ rest, state.work = .invoke activation.frontier activation.maps activation.consumer :: rest ∧
      BodyCall.step construct callbackConstruct fallback state =
        .advance (withPhase .running
          (.body activation.frontier.authored activation.frontier.reading
            ⟨activation.equation.body, activation.frontier.items, activation.frontier.parameter, activation.maps⟩
            activation.consumer ::
            .invoke {activation.frontier with
              ordinal := activation.frontier.ordinal + 1
              matched := true
              sealed := activation.equation.commit} activation.maps activation.consumer :: rest)) := by
  obtain ⟨rest, later, phase, work, running, unsealed, remaining, matched⟩ := activation_origin state activation selected
  exact ⟨rest, work, by simp [BodyCall.step, phase, stepRunning, work, running, unsealed, remaining, matched]⟩

variable {Weight : Type} [Semiring Weight]

abbrev Factors := Ledger Nat (Activation Item Value) Weight

/-- Retained grading metadata decorates the existing work stack. `paid`
records actual activations, including failing ones; `branches` keeps their
independent lineages. A loan carries its producing branch, not that whole work
account. The source instruction algorithm remains `BodyCall.step`. -/
structure State (Item : Type u) (Value : Type v) (Weight : Type) where
  core : BodyCall.State Item Value
  branches : List (Factors (Item := Item) (Value := Value) (Weight := Weight))
  paid : Factors (Item := Item) (Value := Value) (Weight := Weight)
  loan : Factors (Item := Item) (Value := Value) (Weight := Weight)

variable (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Item → Nat → List Value)
    (clause : WeighClause Weight (Activation Item Value))

def openState (program : List (Equation Value)) (items : List Item) (parameter : Nat)
    (reading : NoRuleReading) : State Item Value Weight :=
  ⟨BodyCall.openState program items parameter reading, [[]], [], []⟩

def branchPrefix (state : State Item Value Weight) : Factors (Item := Item) (Value := Value) (Weight := Weight) :=
  state.branches.headD []

def factor (state : State Item Value Weight) (activation : Activation Item Value) :
    Factor Nat (Activation Item Value) Weight :=
  ⟨state.paid.length, activation, WeighClause.eval activation clause⟩

/-- One actual source transition plus its branch metadata. Equal-length work
replaces the current cursor; a shorter work stack pops that same cursor. Only
the proved activation edge adds a cursor and a physical factor. -/
def step (state : State Item Value Weight) : BodyCall.Move Item Value × State Item Value Weight :=
  let moved := BodyCall.step construct callbackConstruct fallback state.core
  let loan := if moved.rows.isEmpty then [] else branchPrefix state
  match activation? state.core with
  | some activation =>
      let produced := factor clause state activation
      (moved, ⟨moved.next, (branchPrefix state ++ [produced]) :: branchPrefix state :: state.branches.tail,
        state.paid ++ [produced], loan⟩)
  | none =>
      (moved, ⟨moved.next,
        if moved.next.work.length = state.core.work.length then state.branches else state.branches.tail,
        state.paid, loan⟩)

theorem step_move (state : State Item Value Weight) :
    (step construct callbackConstruct fallback clause state).1 =
      BodyCall.step construct callbackConstruct fallback state.core := by
  unfold step
  cases activation? state.core <;> rfl

theorem step_core (state : State Item Value Weight) :
    (step construct callbackConstruct fallback clause state).2.core =
      (BodyCall.step construct callbackConstruct fallback state.core).next := by
  unfold step
  cases activation? state.core <;> rfl

/-- The branch that enters the RHS gets the actual source factor. Its saved
alternative retains precisely the earlier prefix. -/
theorem activation_lineages (state : State Item Value Weight) (activation : Activation Item Value)
    (selected : activation? state.core = some activation) :
    (step construct callbackConstruct fallback clause state).2.branches =
      (branchPrefix state ++ [factor clause state activation]) :: branchPrefix state :: state.branches.tail ∧
      (step construct callbackConstruct fallback clause state).2.paid = state.paid ++ [factor clause state activation] ∧
      (step construct callbackConstruct fallback clause state).1.rows = [] := by
  obtain ⟨_, _, pushed⟩ := activation_pushes construct callbackConstruct fallback state.core activation selected
  simp [step, selected, pushed, Move.rows]

theorem quiet_keeps_paid (state : State Item Value Weight) (quiet : activation? state.core = none) :
    (step construct callbackConstruct fallback clause state).2.paid = state.paid := by
  simp [step, quiet]

/-- Coefficients are derived from actual captured equation activations. -/
def Sound (state : State Item Value Weight) : Prop :=
  identities state.paid = List.range state.paid.length ∧
    (∀ produced ∈ state.paid, produced.coefficient = WeighClause.eval produced.dependency clause) ∧
    (∀ branch ∈ state.branches, branch.Sublist state.paid) ∧ state.loan.Sublist state.paid

theorem open_sound (program : List (Equation Value)) (items : List Item) (parameter : Nat) (reading : NoRuleReading) :
    Sound clause (openState (Weight := Weight) program items parameter reading) := by
  simp [Sound, openState, identities]

theorem prefix_supported (state : State Item Value Weight) (sound : Sound clause state) :
    (branchPrefix state).Sublist state.paid := by
  cases branches : state.branches with
  | nil => simp [branchPrefix, branches]
  | cons branch rest => simpa [branchPrefix, branches] using sound.2.2.1 branch (by simp [branches])

theorem step_sound (state : State Item Value Weight) (sound : Sound clause state) :
    Sound clause (step construct callbackConstruct fallback clause state).2 := by
  have head := prefix_supported clause state sound
  unfold step
  cases selected : activation? state.core with
  | none =>
      dsimp only
      refine ⟨sound.1, sound.2.1, ?_, ?_⟩
      · intro branch present
        split at present
        · exact sound.2.2.1 branch present
        · exact sound.2.2.1 branch (List.mem_of_mem_tail present)
      · change (if (BodyCall.step construct callbackConstruct fallback state.core).rows.isEmpty then [] else branchPrefix state).Sublist state.paid
        split
        · exact List.nil_sublist _
        · exact head
  | some activation =>
      dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩
      · have ids := sound.1
        simp only [identities] at ids
        simpa [identities, List.map_append, factor, List.range_succ] using ids
      · intro produced present
        rcases List.mem_append.mp present with old | fresh
        · exact sound.2.1 produced old
        · have equal := List.mem_singleton.mp fresh
          subst produced
          rfl
      · intro branch present
        rcases List.mem_cons.mp present with rfl | next
        · exact head.append (List.Sublist.refl _)
        · rcases List.mem_cons.mp next with rfl | old
          · exact head.trans (List.sublist_append_left _ _)
          · exact (sound.2.2.1 branch (List.mem_of_mem_tail old)).trans (List.sublist_append_left _ _)
      · change (if (BodyCall.step construct callbackConstruct fallback state.core).rows.isEmpty then [] else branchPrefix state).Sublist (state.paid ++ [factor clause state activation])
        split
        · exact List.nil_sublist _
        · exact head.trans (List.sublist_append_left _ _)

/-- The dependency is a genuinely matched equation at its captured ordinal. -/
def Licensed (activation : Activation Item Value) : Prop :=
  activation.frontier.phase = .running ∧ activation.frontier.sealed = false ∧
    (∃ later, activation.frontier.authored.drop activation.frontier.ordinal = activation.equation :: later) ∧
    activation.equation.head.matches activation.frontier.items activation.frontier.parameter = true

theorem activation_licensed (state : BodyCall.State Item Value) (activation : Activation Item Value)
    (selected : activation? state = some activation) : Licensed activation := by
  obtain ⟨_, later, _, _, running, unsealed, remaining, matched⟩ := activation_origin state activation selected
  exact ⟨running, unsealed, ⟨later, remaining⟩, matched⟩

def Authentic (state : State Item Value Weight) : Prop :=
  ∀ produced ∈ state.paid, Licensed produced.dependency

omit [Semiring Weight] in
theorem open_authentic (program : List (Equation Value)) (items : List Item) (parameter : Nat) (reading : NoRuleReading) :
    Authentic (openState (Weight := Weight) program items parameter reading) := by
  simp [Authentic, openState]

theorem step_authentic (state : State Item Value Weight) (authentic : Authentic state) :
    Authentic (step construct callbackConstruct fallback clause state).2 := by
  unfold Authentic step
  cases selected : activation? state.core with
  | none => exact authentic
  | some activation =>
      intro produced present
      rcases List.mem_append.mp present with old | fresh
      · exact authentic produced old
      · have equal := List.mem_singleton.mp fresh
        subst produced
        exact activation_licensed state.core activation selected

private theorem deliver_length (authored : List (Equation Value)) (reading : NoRuleReading)
    (row : List Value) (consumer : Consumer Item Value) (rest : List (Cursor Item Value)) :
    (deliver authored reading row consumer rest).next.work.length = rest.length ∨
      (deliver authored reading row consumer rest).next.work.length = rest.length + 1 := by
  induction consumer generalizing row with
  | emit => exact Or.inl rfl
  | concat first outer ih => exact ih _
  | times right items parameter maps outer => exact Or.inr rfl

private theorem finishInvoke_length (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value)
    (rest : List (Cursor Item Value)) (rows : List (List Value)) :
    (finishInvoke frontier maps consumer rest rows).next.work.length = rest.length + 1 ∨
      (finishInvoke frontier maps consumer rest rows).next.work.length + 1 = rest.length + 1 := by
  cases rest <;> simp [finishInvoke, Move.next, withPhase]

/-- Apart from the separately identified activation, the actual algorithm
replaces or pops its current work cursor. -/
theorem quiet_work_length (state : BodyCall.State Item Value) (quiet : activation? state = none) :
    (BodyCall.step construct callbackConstruct fallback state).next.work.length = state.work.length ∨
      (BodyCall.step construct callbackConstruct fallback state).next.work.length + 1 = state.work.length := by
  cases state with
  | mk work phase =>
      cases phase <;> try { exact Or.inl rfl }
      change (stepRunning construct callbackConstruct fallback work).next.work.length = work.length ∨
        (stepRunning construct callbackConstruct fallback work).next.work.length + 1 = work.length
      fun_cases stepRunning construct callbackConstruct fallback work
      all_goals first
        | exact finishInvoke_length _ _ _ _ _
        | simp_all [activation?, Move.next, withPhase, declineInvoke]
      all_goals
        obtain shorter | same := deliver_length (Item := Item) _ _ _ _ _
        · exact Or.inr (by simpa only [List.length_cons, shorter])
        · exact Or.inl (by simpa only [List.length_cons, same])

/-- There is exactly one retained lineage per actual source work cursor. -/
def Aligned (state : State Item Value Weight) : Prop := state.branches.length = state.core.work.length

omit [Semiring Weight] in
theorem open_aligned (program : List (Equation Value)) (items : List Item) (parameter : Nat) (reading : NoRuleReading) :
    Aligned (openState (Weight := Weight) program items parameter reading) := rfl

theorem step_aligned (state : State Item Value Weight) (aligned : Aligned state) :
    Aligned (step construct callbackConstruct fallback clause state).2 := by
  have lengths : state.branches.length = state.core.work.length := aligned
  cases selected : activation? state.core with
  | none =>
      obtain same | popped := quiet_work_length construct callbackConstruct fallback state.core selected
      · simp [Aligned, step, selected, same, lengths]
      · have different : (BodyCall.step construct callbackConstruct fallback state.core).next.work.length ≠ state.core.work.length := by omega
        simp only [Aligned, step, selected, different, ↓reduceIte, List.length_tail]
        omega
  | some activation =>
      obtain ⟨rest, work, pushed⟩ := activation_pushes construct callbackConstruct fallback state.core activation selected
      simp only [Aligned, step, selected, pushed, Move.next, withPhase, List.length_cons, List.length_tail]
      simp only [work, List.length_cons] at lengths
      omega

theorem paid_valid (state : State Item Value Weight) (sound : Sound clause state) : Valid state.paid := by
  unfold Valid
  rw [sound.1]
  exact List.nodup_range

theorem loan_valid (state : State Item Value Weight) (sound : Sound clause state) : Valid state.loan := by
  exact (paid_valid clause state sound).sublist (sound.2.2.2.map Factor.identity)

theorem loan_source_coefficients (state : State Item Value Weight) (sound : Sound clause state) :
    state.loan.map Factor.coefficient = state.loan.map (fun produced => WeighClause.eval produced.dependency clause) := by
  apply List.map_congr_left
  intro produced present
  exact sound.2.1 produced (sound.2.2.2.subset present)

theorem step_link (state : State Item Value Weight) :
    (step construct callbackConstruct fallback clause state).2.core =
      (step construct callbackConstruct fallback clause state).1.next := by
  rw [step_core, step_move]

/-- The returned coefficient is the ordered fold of the actual branch's
source-derived firing factors. It is independent of delivery counts. -/
def loanWeight (state : State Item Value Weight) : Weight := denote state.loan

theorem loan_weight_source (state : State Item Value Weight) (sound : Sound clause state) :
    loanWeight state = (state.loan.map (fun produced => WeighClause.eval produced.dependency clause)).prod := by
  unfold loanWeight Mettapedia.Algebra.SharedCoefficientLedger.denote
  rw [loan_source_coefficients clause state sound]

#print axioms loan_weight_source


/-- A saved Cartesian right continuation keeps the current lineage; an
outer emission pops it. Concatenation follows its actual outer consumer. -/
def keepsLineage : Consumer Item Value → Bool
  | .emit => false
  | .concat _ outer => keepsLineage outer
  | .times _ _ _ _ _ => true

private theorem deliver_metadata (authored : List (Equation Value)) (reading : NoRuleReading)
    (row : List Value) (consumer : Consumer Item Value) (rest : List (Cursor Item Value)) :
    (deliver authored reading row consumer rest).next.work.length =
        (if keepsLineage consumer then rest.length + 1 else rest.length) ∧
      (deliver authored reading row consumer rest).rows.isEmpty = keepsLineage consumer := by
  induction consumer generalizing row with
  | emit => exact ⟨rfl, rfl⟩
  | concat first outer ih => exact ih _
  | times right items parameter maps outer => exact ⟨rfl, rfl⟩

/-- Actual empty-collection and singleton delivery preserve the entire left
lineage into a Cartesian right continuation, including nested concatenation.
Emission loans that exact lineage and removes only the current cursor. -/
theorem body_delivery_lineages (authored : List (Equation Value)) (reading : NoRuleReading)
    (items : List Item) (parameter : Nat) (maps : List (Mapper Item Value)) (value : Option Value)
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (branch : Factors (Item := Item) (Value := Value) (Weight := Weight)) (siblings : List (Factors (Item := Item) (Value := Value) (Weight := Weight)))
    (paid loan : Factors (Item := Item) (Value := Value) (Weight := Weight)) :
    let frame : Frame Item Value := ⟨value.elim .empty .singleton, items, parameter, maps⟩
    let state : State Item Value Weight :=
      ⟨withPhase .running (.body authored reading frame consumer :: rest), branch :: siblings, paid, loan⟩
    let next := step construct callbackConstruct fallback clause state
    next.1 = deliver authored reading (value.toList.map (applyMaps construct callbackConstruct maps)) consumer rest ∧
      next.2.branches = (if keepsLineage consumer then branch :: siblings else siblings) ∧
      next.2.loan = (if keepsLineage consumer then [] else branch) ∧ next.2.paid = paid := by
  have metadata := deliver_metadata authored reading (value.toList.map (applyMaps construct callbackConstruct maps)) consumer rest
  dsimp only
  cases value <;> cases kept : keepsLineage consumer <;>
    simp_all [step, activation?, branchPrefix, BodyCall.step, stepRunning, withPhase]

/-- A non-firing replacement keeps every factor of the current branch;
a pop discards only that cursor's lineage. No activation is invented. -/
theorem quiet_lineages (state : State Item Value Weight) (quiet : activation? state.core = none) :
    (step construct callbackConstruct fallback clause state).2.branches =
      (if (BodyCall.step construct callbackConstruct fallback state.core).next.work.length = state.core.work.length
        then state.branches else state.branches.tail) ∧
      (step construct callbackConstruct fallback clause state).2.paid = state.paid := by
  simp [step, quiet]

#print axioms body_delivery_lineages
#print axioms quiet_lineages

namespace Compact

/-- Executable grading state retains the current source and live branch
lineages, with a constant-time fresh ordinal. Failed activation history is
absent; it belongs only to the erased proof/account view. -/
structure State (Item : Type u) (Value : Type v) (Weight : Type) where
  core : BodyCall.State Item Value
  branches : List (Factors (Item := Item) (Value := Value) (Weight := Weight))
  nextOrdinal : Nat
  loan : Factors (Item := Item) (Value := Value) (Weight := Weight)

def erase (state : Graded.State Item Value Weight) : State Item Value Weight :=
  ⟨state.core, state.branches, state.paid.length, state.loan⟩

/-- One shared compact algorithm accepts optional source attachments.
Every activation advances its firing ordinal, including an unannotated one. -/
def stepWith (attachment : Activation Item Value → Option Weight) (state : State Item Value Weight) :
    BodyCall.Move Item Value × State Item Value Weight :=
  let moved := BodyCall.step construct callbackConstruct fallback state.core
  let branch := state.branches.headD []
  let loan := if moved.rows.isEmpty then [] else branch
  match activation? state.core with
  | some activation =>
      let produced := (attachment activation).toList.map
        (fun coefficient => (⟨state.nextOrdinal, activation, coefficient⟩ : Factor Nat (Activation Item Value) Weight))
      (moved, ⟨moved.next, (branch ++ produced) :: branch :: state.branches.tail,
        state.nextOrdinal + 1, loan⟩)
  | none =>
      (moved, ⟨moved.next,
        if moved.next.work.length = state.core.work.length then state.branches else state.branches.tail,
        state.nextOrdinal, loan⟩)

def step (state : State Item Value Weight) : BodyCall.Move Item Value × State Item Value Weight :=
  stepWith construct callbackConstruct fallback (fun activation => some (WeighClause.eval activation clause)) state

omit [Semiring Weight] in
theorem stepWith_link (attachment : Activation Item Value → Option Weight) (state : State Item Value Weight) :
    (stepWith construct callbackConstruct fallback attachment state).2.core =
      (stepWith construct callbackConstruct fallback attachment state).1.next := by
  unfold stepWith
  cases activation? state.core <;> rfl

omit [Semiring Weight] in
theorem stepWith_move (attachment : Activation Item Value → Option Weight) (state : State Item Value Weight) :
    (stepWith construct callbackConstruct fallback attachment state).1 =
      BodyCall.step construct callbackConstruct fallback state.core := by
  unfold stepWith
  cases activation? state.core <;> rfl

#print axioms stepWith_link
#print axioms stepWith_move

/-- Erasure commutes with the actual source transition and retains its exact
physical next identity, phase, stack, lineages and current loan. -/
theorem step_erases (state : Graded.State Item Value Weight) :
    ((Graded.step construct callbackConstruct fallback clause state).1,
      erase (Graded.step construct callbackConstruct fallback clause state).2) =
      step construct callbackConstruct fallback clause (erase state) := by
  unfold Graded.step step stepWith erase
  cases activation? state.core <;> simp [factor, branchPrefix]

theorem step_link (state : State Item Value Weight) :
    (step construct callbackConstruct fallback clause state).2.core =
      (step construct callbackConstruct fallback clause state).1.next := by
  unfold step stepWith
  cases activation? state.core <;> rfl

theorem step_move (state : State Item Value Weight) :
    (step construct callbackConstruct fallback clause state).1 =
      BodyCall.step construct callbackConstruct fallback state.core := by
  unfold step stepWith
  cases activation? state.core <;> rfl

#print axioms step_erases
#print axioms step_link
#print axioms step_move

namespace Attachment

variable (selection : Activation Item Value → Option (WeighClause Weight (Activation Item Value)))

def values (activation : Activation Item Value) : Option Weight :=
  (selection activation).map (WeighClause.eval activation)

/-- Absent annotations have unit value only in the reference proof view.
An explicit unit annotation remains present in the executable factor ledger. -/
def valuation : WeighClause Weight (Activation Item Value) :=
  .observe (fun activation => (values selection activation).getD 1)

def selected (ledger : Factors (Item := Item) (Value := Value) (Weight := Weight)) :=
  ledger.filter (fun produced => (selection produced.dependency).isSome)

def erase (state : State Item Value Weight) : State Item Value Weight :=
  { state with
    branches := state.branches.map (selected selection)
    loan := selected selection state.loan }

/-- The compact transition and ordinal are shared with total attachment;
only the factor-production interface selects absent versus present grades. -/
theorem step_erases (state : State Item Value Weight) :
    ((Compact.step construct callbackConstruct fallback (valuation selection) state).1,
      erase selection (Compact.step construct callbackConstruct fallback (valuation selection) state).2) =
      stepWith construct callbackConstruct fallback (values selection) (erase selection state) := by
  unfold Compact.step stepWith erase
  cases firing : activation? state.core with
  | none =>
      by_cases same : (BodyCall.step construct callbackConstruct fallback state.core).next.work.length = state.core.work.length
      all_goals cases rows : (BodyCall.step construct callbackConstruct fallback state.core).rows.isEmpty <;>
        cases branches : state.branches <;>
          simp [same, rows, selected]
  | some activation =>
      cases attached : selection activation <;>
        cases rows : (BodyCall.step construct callbackConstruct fallback state.core).rows.isEmpty <;>
        cases branches : state.branches <;>
          simp [values, valuation, WeighClause.eval, attached, rows, selected, List.filter_append]

/-- Every matched source firing advances its own ordinal. Factor production
is optional and does not change the forked source continuation. -/
theorem activation_metadata (state : State Item Value Weight) (activation : Activation Item Value)
    (firing : activation? state.core = some activation) :
    let actual := stepWith construct callbackConstruct fallback (values selection) state
    actual.2.nextOrdinal = state.nextOrdinal + 1 ∧
      actual.2.branches =
        (state.branches.headD [] ++ (values selection activation).toList.map
          (fun coefficient => (⟨state.nextOrdinal, activation, coefficient⟩ : Factor Nat (Activation Item Value) Weight))) ::
          state.branches.headD [] :: state.branches.tail ∧ actual.2.loan = [] := by
  obtain ⟨_, _, pushed⟩ := activation_pushes construct callbackConstruct fallback state.core activation firing
  simp [stepWith, firing, pushed, Move.rows]

theorem unannotated_firing (state : State Item Value Weight) (activation : Activation Item Value)
    (firing : activation? state.core = some activation) (absent : selection activation = none) :
    let actual := stepWith construct callbackConstruct fallback (values selection) state
    actual.2.nextOrdinal = state.nextOrdinal + 1 ∧
      actual.2.branches = state.branches.headD [] :: state.branches.headD [] :: state.branches.tail := by
  have actual := activation_metadata construct callbackConstruct fallback selection state activation firing
  exact ⟨actual.1, by simpa [values, absent] using actual.2.1⟩

/-- Explicit unit attachment is a real physical factor, even though its
multiplicative readout equals an unannotated activation's readout. -/
theorem unit_firing (state : State Item Value Weight) (activation : Activation Item Value)
    (firing : activation? state.core = some activation) (unit : selection activation = some (.scalar 1)) :
    (stepWith construct callbackConstruct fallback (values selection) state).2.branches =
      (state.branches.headD [] ++ [⟨state.nextOrdinal, activation, 1⟩]) ::
        state.branches.headD [] :: state.branches.tail := by
  have actual := activation_metadata construct callbackConstruct fallback selection state activation firing
  simpa [values, unit, WeighClause.eval] using actual.2.1

#print axioms activation_metadata
#print axioms unannotated_firing
#print axioms unit_firing

theorem source_step_erases (state : Graded.State Item Value Weight) :
    ((Graded.step construct callbackConstruct fallback (valuation selection) state).1,
      erase selection (Compact.erase (Graded.step construct callbackConstruct fallback (valuation selection) state).2)) =
      stepWith construct callbackConstruct fallback (values selection) (erase selection (Compact.erase state)) := by
  exact (congrArg (fun result => (result.1, erase selection result.2))
    (Compact.step_erases construct callbackConstruct fallback (valuation selection) state)).trans
      (step_erases construct callbackConstruct fallback selection (Compact.erase state))

/-- The same arbitrary nested Cartesian/concatenation continuation law holds
in the sparse executor. Unit erasure never drops a selected left factor. -/
theorem delivery_inherits (authored : List (Equation Value)) (reading : NoRuleReading)
    (items : List Item) (parameter : Nat) (maps : List (Mapper Item Value)) (value : Option Value)
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (branch : Factors (Item := Item) (Value := Value) (Weight := Weight))
    (siblings : List (Factors (Item := Item) (Value := Value) (Weight := Weight)))
    (paid loan : Factors (Item := Item) (Value := Value) (Weight := Weight)) :
    let frame : Frame Item Value := ⟨value.elim .empty .singleton, items, parameter, maps⟩
    let full : Graded.State Item Value Weight :=
      ⟨withPhase .running (.body authored reading frame consumer :: rest), branch :: siblings, paid, loan⟩
    let actual := stepWith construct callbackConstruct fallback (values selection) (erase selection (Compact.erase full))
    actual.2.branches = (if keepsLineage consumer then selected selection branch :: siblings.map (selected selection)
      else siblings.map (selected selection)) ∧
      actual.2.loan = (if keepsLineage consumer then [] else selected selection branch) := by
  have original := Graded.body_delivery_lineages construct callbackConstruct fallback (valuation selection)
    authored reading items parameter maps value consumer rest branch siblings paid loan
  dsimp only
  rw [← source_step_erases]
  change (Graded.step construct callbackConstruct fallback (valuation selection) _).2.branches.map (selected selection) = _ ∧
    selected selection (Graded.step construct callbackConstruct fallback (valuation selection) _).2.loan = _
  rw [original.2.1, original.2.2.1]
  cases keepsLineage consumer <;> simp [selected]

#print axioms source_step_erases
#print axioms delivery_inherits

omit [Semiring Weight] in
theorem selected_sublist (ledger : Factors (Item := Item) (Value := Value) (Weight := Weight)) :
    (selected selection ledger).Sublist ledger := List.filter_sublist

omit [Semiring Weight] in
theorem selected_valid (ledger : Factors (Item := Item) (Value := Value) (Weight := Weight))
    (valid : Valid ledger) : Valid (selected selection ledger) :=
  valid.sublist ((selected_sublist selection ledger).map Factor.identity)

/-- Erasing unannotated unit factors preserves the ordered product without
commutativity. This local valuation hypothesis is supplied by actual Sound. -/
theorem selected_denote (ledger : Factors (Item := Item) (Value := Value) (Weight := Weight))
    (valued : ∀ produced ∈ ledger, produced.coefficient = WeighClause.eval produced.dependency (valuation selection)) :
    Mettapedia.Algebra.SharedCoefficientLedger.denote (selected selection ledger) =
      Mettapedia.Algebra.SharedCoefficientLedger.denote ledger := by
  induction ledger with
  | nil => rfl
  | cons produced rest ih =>
      have tail := ih (fun next member => valued next (List.mem_cons_of_mem _ member))
      have coefficient := valued produced List.mem_cons_self
      cases attached : selection produced.dependency with
      | none =>
          have unit : produced.coefficient = 1 := by
            simpa [valuation, values, WeighClause.eval, attached] using coefficient
          simpa [selected, attached, Mettapedia.Algebra.SharedCoefficientLedger.denote, unit] using tail
      | some expression =>
          simpa [selected, attached, Mettapedia.Algebra.SharedCoefficientLedger.denote] using congrArg (produced.coefficient * ·) tail

/-- Every real source loan supplies the valuation premise; the factor filter
is not justified by an assumed equality of whole-source answers or grades. -/
theorem loan_denote (state : Graded.State Item Value Weight)
    (sound : Sound (valuation selection) state) :
    Mettapedia.Algebra.SharedCoefficientLedger.denote (selected selection state.loan) = loanWeight state := by
  apply selected_denote selection
  intro produced present
  exact sound.2.1 produced (sound.2.2.2.subset present)

omit [Semiring Weight] in
/-- Physical firing identities are preserved, including gaps left by erased
unannotated activations. A selection never coalesces two equal answers. -/
theorem selected_identity_sublist (ledger : Factors (Item := Item) (Value := Value) (Weight := Weight)) :
    (identities (selected selection ledger)).Sublist (identities ledger) :=
  (selected_sublist selection ledger).map Factor.identity

#print axioms step_erases
#print axioms selected_sublist
#print axioms selected_valid
#print axioms selected_denote
#print axioms loan_denote
#print axioms selected_identity_sublist

end Attachment

end Compact

#print axioms activation_at
#print axioms activation_origin
#print axioms activation_pushes
#print axioms step_move
#print axioms step_core
#print axioms activation_lineages
#print axioms quiet_keeps_paid
#print axioms open_sound
#print axioms prefix_supported
#print axioms step_sound
#print axioms activation_licensed
#print axioms open_authentic
#print axioms step_authentic
#print axioms quiet_work_length
#print axioms open_aligned
#print axioms step_aligned
#print axioms paid_valid
#print axioms loan_valid
#print axioms loan_source_coefficients
#print axioms step_link

end Graded

/-! Independent authored weighted meaning. Its annotations see only source
equation identity and call arguments. Ordered coefficient words retain absent
versus explicit unit attachments before any semiring product is taken. -/
namespace WeightedSource

variable {Weight : Type}

abbrev Row (Value : Type v) (Weight : Type) := List Value × List Weight

abbrev Attachment (Item : Type u) (Value : Type v) (Weight : Type) :=
  Nat → Equation Value → List Item → Nat → Option Weight

def prepend (factors : List Weight) (rows : List (Row Value Weight)) : List (Row Value Weight) :=
  rows.map (fun row => (row.1, factors ++ row.2))

def mapped (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (maps : List (Mapper Item Value)) (rows : List (Row Value Weight)) : List (Row Value Weight) :=
  rows.map (fun row => (row.1.map (applyMaps construct callbackConstruct maps), row.2))

/-- Cartesian body meaning, recursively on the existing authored Code. No
cursor, factor identity, physical firing count or future loan is inspected. -/
def body (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (tailResults : Nat → List (Row Value Weight)) (items : List Item) (parameter : Nat) :
    Code Value → List (Row Value Weight)
  | .empty => [([], [])]
  | .singleton value => [([value], [])]
  | .append left right =>
      (body construct callbackConstruct tailResults items parameter left).flatMap (fun first =>
        (body construct callbackConstruct tailResults items parameter right).map (fun second =>
          (first.1 ++ second.1, first.2 ++ second.2)))
  | .mapHead inner =>
      match items with
      | [] => []
      | head :: _ => (body construct callbackConstruct tailResults items parameter inner).map
          (fun row => (row.1.map (construct head), row.2))
  | .map callback inner => (body construct callbackConstruct tailResults items parameter inner).map
      (fun row => (row.1.map (callback.run callbackConstruct), row.2))
  | .ifZero yes no => if parameter = 0 then body construct callbackConstruct tailResults items parameter yes
      else body construct callbackConstruct tailResults items parameter no
  | .ifEmpty yes no => if items = [] then body construct callbackConstruct tailResults items parameter yes
      else body construct callbackConstruct tailResults items parameter no
  | .callTail => match items with | [] => [] | _ :: _ => tailResults parameter
  | .callPredecessor => match items, parameter with | _ :: _, count + 1 => tailResults count | _, _ => []
  | .unsupported => []

/-- A cut discards this invocation's suffix even if its weighted body fails.
Zero coefficients and empty returned collections are still occurrences. -/
def equations (attachment : Attachment Item Value Weight) (items : List Item) (parameter : Nat)
    (runBody : Code Value → List (Row Value Weight)) : Nat → List (Equation Value) → List (Row Value Weight)
  | _, [] => []
  | ordinal, equation :: rest =>
      if equation.head.matches items parameter then
        let current := prepend (attachment ordinal equation items parameter).toList (runBody equation.body)
        if equation.commit then current
        else current ++ equations attachment items parameter runBody (ordinal + 1) rest
      else equations attachment items parameter runBody (ordinal + 1) rest

def source (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (attachment : Attachment Item Value Weight) (authored : List (Equation Value)) :
    List Item → Nat → List (Row Value Weight)
  | [], parameter => equations attachment [] parameter
      (body construct callbackConstruct (fun _ => []) [] parameter) 0 authored
  | head :: tail, parameter => equations attachment (head :: tail) parameter
      (body construct callbackConstruct (source construct callbackConstruct attachment authored tail)
        (head :: tail) parameter) 0 authored

def bodyRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (attachment : Attachment Item Value Weight) (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) (code : Code Value) : List (Row Value Weight) :=
  body construct callbackConstruct
    (match items with | [] => fun _ => [] | _ :: tail => source construct callbackConstruct attachment authored tail)
    items parameter code

def bindConsumer (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (attachment : Attachment Item Value Weight) (authored : List (Equation Value)) :
    Consumer Item Value → Row Value Weight → List (Row Value Weight)
  | .emit, row => [row]
  | .concat first outer, row =>
      bindConsumer construct callbackConstruct attachment authored outer (first ++ row.1, row.2)
  | .times right items parameter maps outer, row =>
      (mapped construct callbackConstruct maps
        (bodyRows construct callbackConstruct attachment authored items parameter right)).flatMap
          (fun second => bindConsumer construct callbackConstruct attachment authored outer
            (row.1 ++ second.1, row.2 ++ second.2))

def invokeRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (attachment : Attachment Item Value Weight) (frontier : RetainedFrontier Item Value) : List (Row Value Weight) :=
  match frontier.phase with
  | .running => if frontier.sealed then [] else
      equations attachment frontier.items frontier.parameter
        (bodyRows construct callbackConstruct attachment frontier.authored frontier.items frontier.parameter)
        frontier.ordinal (frontier.authored.drop frontier.ordinal)
  | .finished | .declined => []

def cursorRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (attachment : Attachment Item Value Weight) (factors : List Weight) : Cursor Item Value → List (Row Value Weight)
  | .invoke frontier maps consumer =>
      (prepend factors (mapped construct callbackConstruct maps (invokeRows construct callbackConstruct attachment frontier))).flatMap
        (bindConsumer construct callbackConstruct attachment frontier.authored consumer)
  | .body authored _ frame consumer =>
      (prepend factors (mapped construct callbackConstruct frame.maps
        (bodyRows construct callbackConstruct attachment authored frame.items frame.parameter frame.code))).flatMap
          (bindConsumer construct callbackConstruct attachment authored consumer)

/-- Proof-only residual view pairs the actual stack and its actual retained
branch factors. It supplies no runtime completion or scheduling oracle. -/
def workRows (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value)
    (attachment : Attachment Item Value Weight) :
    List (Cursor Item Value) → List (Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)) → List (Row Value Weight)
  | cursor :: rest, branch :: siblings =>
      cursorRows construct callbackConstruct attachment (branch.map (·.coefficient)) cursor ++
        workRows construct callbackConstruct attachment rest siblings
  | _, _ => []

def activationValue (attachment : Attachment Item Value Weight) (activation : Graded.Activation Item Value) : Option Weight :=
  attachment activation.frontier.ordinal activation.equation activation.frontier.items activation.frontier.parameter

def emitted (moved : Move Item Value)
    (loan : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)) : List (Row Value Weight) :=
  moved.rows.map (fun row => (row, loan.map (·.coefficient)))

theorem source_eq_equations (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (attachment : Attachment Item Value Weight)
    (authored : List (Equation Value)) (items : List Item) (parameter : Nat) :
    source construct callbackConstruct attachment authored items parameter =
      equations attachment items parameter (bodyRows construct callbackConstruct attachment authored items parameter) 0 authored := by
  cases items <;> rfl

theorem body_erase (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (tailResults : Nat → List (Row Value Weight))
    (items : List Item) (parameter : Nat) (code : Code Value) :
    (body construct callbackConstruct tailResults items parameter code).map Prod.fst =
      bodyResults construct callbackConstruct (fun count => (tailResults count).map Prod.fst) items parameter code := by
  induction code generalizing items parameter with
  | empty | singleton _ | unsupported => rfl
  | append left right leftIH rightIH =>
      simp [body, bodyResults, List.map_flatMap, List.flatMap_map, List.map_map,
        ← leftIH, ← rightIH, Function.comp_def]
  | mapHead inner ih => cases items <;> simp [body, bodyResults, List.map_map, ← ih, Function.comp_def]
  | map callback inner ih => simp [body, bodyResults, List.map_map, ← ih, Function.comp_def]
  | ifZero yes no yesIH noIH => cases parameter <;> simp [body, bodyResults, yesIH, noIH]
  | ifEmpty yes no yesIH noIH => cases items <;> simp [body, bodyResults, yesIH, noIH]
  | callTail => cases items <;> rfl
  | callPredecessor => cases items <;> cases parameter <;> rfl

theorem equations_erase (attachment : Attachment Item Value Weight)
    (items : List Item) (parameter : Nat) (runBody : Code Value → List (Row Value Weight))
    (ordinal : Nat) (authored : List (Equation Value)) :
    (equations attachment items parameter runBody ordinal authored).map Prod.fst =
      equationsResults (fun head => head.matches items parameter)
        (fun code => (runBody code).map Prod.fst) authored := by
  induction authored generalizing ordinal with
  | nil => rfl
  | cons equation rest ih =>
      cases matched : equation.head.matches items parameter <;> cases committed : equation.commit <;>
        simp [equations, equationsResults, matched, committed, prepend, List.map_map, Function.comp_def, ih]

theorem source_erase (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (attachment : Attachment Item Value Weight)
    (authored : List (Equation Value)) (items : List Item) (parameter : Nat) :
    (source construct callbackConstruct attachment authored items parameter).map Prod.fst =
      SourceProducerAdmission.source construct callbackConstruct authored items parameter := by
  induction items generalizing parameter with
  | nil =>
      simp only [source, SourceProducerAdmission.source, equations_erase, body_erase, List.map_nil]
  | cons head tail ih =>
      simp only [source, SourceProducerAdmission.source, equations_erase, body_erase, ih]

variable (construct : Item → Value → Value)
    (callbackConstruct : Nat → Value → Value → Value) (fallback : List Item → Nat → List Value)
    (attachment : Attachment Item Value Weight)

private theorem deliver_metadata (authored : List (Equation Value)) (reading : NoRuleReading)
    (row : List Value) (consumer : Consumer Item Value) (rest : List (Cursor Item Value)) :
    (deliver authored reading row consumer rest).next.work.length =
        (if Graded.keepsLineage consumer then rest.length + 1 else rest.length) ∧
      (deliver authored reading row consumer rest).rows.isEmpty = Graded.keepsLineage consumer := by
  induction consumer generalizing row with
  | emit => exact ⟨rfl, rfl⟩
  | concat first outer ih => exact ih _
  | times right items parameter maps outer => exact ⟨rfl, rfl⟩

theorem deliver_preserves_rows (authored : List (Equation Value)) (reading : NoRuleReading)
    (consumer : Consumer Item Value) (row : List Value) (rest : List (Cursor Item Value))
    (branch : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))
    (siblings : List (Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))) :
    let moved := deliver authored reading row consumer rest
    emitted moved (if Graded.keepsLineage consumer then [] else branch) ++
        workRows construct callbackConstruct attachment moved.next.work
          (if Graded.keepsLineage consumer then branch :: siblings else siblings) =
      bindConsumer construct callbackConstruct attachment authored consumer (row, branch.map (·.coefficient)) ++
        workRows construct callbackConstruct attachment rest siblings := by
  induction consumer generalizing row with
  | emit => simp [deliver, Graded.keepsLineage, emitted, Move.rows, Move.next, withPhase, bindConsumer]
  | concat first outer ih => exact ih (first ++ row)
  | times right items parameter maps outer =>
      simp [deliver, Graded.keepsLineage, emitted, Move.rows, Move.next, withPhase, workRows,
        cursorRows, bindConsumer, prepend, List.flatMap_map]

private theorem delivery_step (authored : List (Equation Value))
    (items : List Item) (parameter : Nat) (maps : List (Mapper Item Value))
    (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (branch : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))
    (siblings : List (Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)))
    (ordinal : Nat) (loan : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))
    (value : Option Value) :
    let frame : Frame Item Value := ⟨value.elim .empty .singleton, items, parameter, maps⟩
    let state : Graded.Compact.State Item Value Weight :=
      ⟨withPhase .running (.body authored (.observe .noAnswers) frame consumer :: rest), branch :: siblings, ordinal, loan⟩
    let actual := Graded.Compact.stepWith construct callbackConstruct fallback (activationValue attachment) state
    emitted actual.1 actual.2.loan ++
        workRows construct callbackConstruct attachment actual.2.core.work actual.2.branches =
      workRows construct callbackConstruct attachment state.core.work state.branches := by
  have metadata := deliver_metadata authored (.observe .noAnswers)
    (value.toList.map (applyMaps construct callbackConstruct maps)) consumer rest
  have conserved := deliver_preserves_rows construct callbackConstruct attachment authored (.observe .noAnswers)
    consumer (value.toList.map (applyMaps construct callbackConstruct maps)) rest branch siblings
  cases value <;> cases kept : Graded.keepsLineage consumer <;>
    simp_all [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
      withPhase, workRows, cursorRows, bodyRows, body, mapped, prepend]

/-- Every actual body transition conserves the ordered weighted residual,
including all nested Cartesian consumers and already acquired left factors. -/
theorem body_step_preserves_rows (authored : List (Equation Value))
    (frame : Frame Item Value) (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (branch : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))
    (siblings : List (Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)))
    (ordinal : Nat) (loan : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)) :
    let state : Graded.Compact.State Item Value Weight :=
      ⟨withPhase .running (.body authored (.observe .noAnswers) frame consumer :: rest), branch :: siblings, ordinal, loan⟩
    let actual := Graded.Compact.stepWith construct callbackConstruct fallback (activationValue attachment) state
    emitted actual.1 actual.2.loan ++
        workRows construct callbackConstruct attachment actual.2.core.work actual.2.branches =
      workRows construct callbackConstruct attachment state.core.work state.branches := by
  rcases frame with ⟨code, items, parameter, maps⟩
  cases code
  case empty => exact delivery_step construct callbackConstruct fallback attachment authored items parameter maps consumer rest branch siblings ordinal loan none
  case singleton value => exact delivery_step construct callbackConstruct fallback attachment authored items parameter maps consumer rest branch siblings ordinal loan (some value)
  all_goals cases items <;> cases parameter
  all_goals simp [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
    emitted, Move.rows, Move.next, withPhase, workRows, cursorRows,
    bindConsumer, bodyRows, body, mapped, prepend, applyMaps, List.map_map,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_append,
    List.append_assoc, Function.comp_def, invokeRows, openFrontier]
  all_goals rw [← source_eq_equations]

theorem invoke_step_preserves_rows (frontier : RetainedFrontier Item Value)
    (maps : List (Mapper Item Value)) (consumer : Consumer Item Value) (rest : List (Cursor Item Value))
    (branch : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))
    (siblings : List (Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)))
    (ordinal : Nat) (loan : Graded.Factors (Item := Item) (Value := Value) (Weight := Weight))
    (reading : frontier.reading = .observe .noAnswers) :
    let state : Graded.Compact.State Item Value Weight :=
      ⟨withPhase .running (.invoke frontier maps consumer :: rest), branch :: siblings, ordinal, loan⟩
    let actual := Graded.Compact.stepWith construct callbackConstruct fallback (activationValue attachment) state
    emitted actual.1 actual.2.loan ++
        workRows construct callbackConstruct attachment actual.2.core.work actual.2.branches =
      workRows construct callbackConstruct attachment state.core.work state.branches := by
  cases phase : frontier.phase with
  | finished =>
      cases rest <;> simp [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
        phase, emitted, Move.rows, Move.next, withPhase, workRows, cursorRows, invokeRows, mapped, prepend]
  | declined =>
      simp [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
        phase, emitted, Move.rows, Move.next, withPhase]
  | running =>
      cases sealed : frontier.sealed with
      | true =>
          cases rest <;> simp [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
            phase, sealed, finishInvoke, emitted, Move.rows, Move.next, withPhase,
            workRows, cursorRows, invokeRows, mapped, prepend]
      | false =>
          cases exposed : frontier.authored.drop frontier.ordinal with
          | nil =>
              cases matched : frontier.matched <;> cases rest <;>
                simp [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
                  phase, sealed, exposed, matched, reading, observeRuleBodies, finishInvoke,
                  emitted, Move.rows, Move.next, withPhase, workRows, cursorRows, invokeRows,
                  equations, mapped, prepend]
          | cons equation remaining =>
              have dropNext := drop_succ_of_drop_cons exposed
              cases hit : equation.head.matches frontier.items frontier.parameter <;>
                cases committed : equation.commit <;>
                simp [Graded.Compact.stepWith, Graded.activation?, BodyCall.step, stepRunning,
                  phase, sealed, exposed, hit, committed, dropNext, activationValue,
                  emitted, Move.rows, Move.next, withPhase, workRows, cursorRows,
                  invokeRows, equations, mapped, prepend, List.map_map, List.map_append,
                  List.flatMap_map, List.flatMap_append, List.append_assoc, Function.comp_def]

/-- The independently recursive weighted meaning is conserved by the actual
compact cursor, rather than an equality supplied by a completed return. -/
theorem step_preserves_rows (state : Graded.Compact.State Item Value Weight)
    (aligned : state.branches.length = state.core.work.length)
    (readings : sourceReadings state.core.work) :
    let actual := Graded.Compact.stepWith construct callbackConstruct fallback (activationValue attachment) state
    emitted actual.1 actual.2.loan ++
        workRows construct callbackConstruct attachment actual.2.core.work actual.2.branches =
      workRows construct callbackConstruct attachment state.core.work state.branches := by
  rcases state with ⟨⟨work, phase⟩, branches, ordinal, loan⟩
  cases phase
  case finished => simp [Graded.Compact.stepWith, BodyCall.step, Graded.activation?, emitted, Move.rows, Move.next]
  case declined => simp [Graded.Compact.stepWith, BodyCall.step, Graded.activation?, emitted, Move.rows, Move.next]
  case handoff => simp [Graded.Compact.stepWith, BodyCall.step, Graded.activation?, emitted, Move.rows, Move.next]
  case running =>
    cases work with
    | nil =>
        have empty : branches = [] := by simpa using aligned
        subst branches
        rfl
    | cons cursor rest =>
        cases branches with
        | nil => simp at aligned
        | cons branch siblings =>
            have first := (sourceReadings_cons cursor rest).mp readings |>.1
            cases cursor with
            | invoke frontier maps consumer =>
                exact invoke_step_preserves_rows construct callbackConstruct fallback attachment
                  frontier maps consumer rest branch siblings ordinal loan first
            | body authored reading frame consumer =>
                change reading = .observe .noAnswers at first
                subst reading
                exact body_step_preserves_rows construct callbackConstruct fallback attachment
                  authored frame consumer rest branch siblings ordinal loan

theorem step_aligned (state : Graded.Compact.State Item Value Weight)
    (aligned : state.branches.length = state.core.work.length) :
    let actual := Graded.Compact.stepWith construct callbackConstruct fallback (activationValue attachment) state
    actual.2.branches.length = actual.2.core.work.length := by
  cases selected : Graded.activation? state.core with
  | none =>
      obtain same | popped := Graded.quiet_work_length construct callbackConstruct fallback state.core selected
      · simp [Graded.Compact.stepWith, selected, same, aligned]
      · have different : (BodyCall.step construct callbackConstruct fallback state.core).next.work.length ≠ state.core.work.length := by omega
        simp only [Graded.Compact.stepWith, selected, different, ↓reduceIte, List.length_tail]
        omega
  | some activation =>
      obtain ⟨rest, work, pushed⟩ := Graded.activation_pushes construct callbackConstruct fallback state.core activation selected
      simp only [Graded.Compact.stepWith, selected, pushed, Move.next, withPhase, List.length_cons, List.length_tail]
      simp only [work, List.length_cons] at aligned
      omega

theorem open_rows (authored : List (Equation Value)) (items : List Item) (parameter : Nat) :
    workRows construct callbackConstruct attachment
        (BodyCall.openState authored items parameter (.observe .noAnswers)).work [[]] =
      source construct callbackConstruct attachment authored items parameter := by
  simp [BodyCall.openState, workRows, cursorRows, openFrontier, invokeRows, mapped, prepend,
    bindConsumer, applyMaps, ← source_eq_equations]

theorem bodyRows_erase (authored : List (Equation Value)) (items : List Item) (parameter : Nat) (code : Code Value) :
    (bodyRows construct callbackConstruct attachment authored items parameter code).map Prod.fst =
      BodyCall.bodyRows construct callbackConstruct authored items parameter code := by
  cases items <;> simp [bodyRows, BodyCall.bodyRows, body_erase, source_erase]

theorem mapped_erase (maps : List (Mapper Item Value)) (rows : List (Row Value Weight)) :
    (mapped construct callbackConstruct maps rows).map Prod.fst =
      mappedRows construct callbackConstruct maps (rows.map Prod.fst) := by
  simp [mapped, mappedRows, List.map_map, Function.comp_def]

theorem bindConsumer_erase (authored : List (Equation Value)) (consumer : Consumer Item Value)
    (row : Row Value Weight) :
    (bindConsumer construct callbackConstruct attachment authored consumer row).map Prod.fst =
      BodyCall.bindConsumer construct callbackConstruct authored consumer row.1 := by
  induction consumer generalizing row with
  | emit => rfl
  | concat first outer ih => exact ih _
  | times right items parameter maps outer ih =>
      simp only [bindConsumer, List.map_flatMap, ih, BodyCall.bindConsumer]
      rw [← bodyRows_erase construct callbackConstruct attachment authored items parameter right,
        ← mapped_erase construct callbackConstruct maps]
      simp only [List.flatMap_map]

theorem invokeRows_erase (frontier : RetainedFrontier Item Value) :
    (invokeRows construct callbackConstruct attachment frontier).map Prod.fst =
      BodyCall.invokeRows construct callbackConstruct frontier := by
  cases phase : frontier.phase <;> cases sealed : frontier.sealed <;>
    simp [invokeRows, BodyCall.invokeRows, phase, sealed, equations_erase, bodyRows_erase]

theorem cursorRows_erase (factors : List Weight) (cursor : Cursor Item Value) :
    (cursorRows construct callbackConstruct attachment factors cursor).map Prod.fst =
      BodyCall.cursorRows construct callbackConstruct cursor := by
  cases cursor <;>
    simp only [cursorRows, BodyCall.cursorRows, List.map_flatMap, bindConsumer_erase]
  all_goals first
    | rw [← bodyRows_erase construct callbackConstruct attachment]
    | rw [← invokeRows_erase construct callbackConstruct attachment]
  all_goals simp only [prepend, mapped, mappedRows, List.flatMap_map, List.map_map,
    Function.comp_def]

theorem workRows_erase (work : List (Cursor Item Value))
    (branches : List (Graded.Factors (Item := Item) (Value := Value) (Weight := Weight)))
    (aligned : branches.length = work.length) :
    (workRows construct callbackConstruct attachment work branches).map Prod.fst =
      BodyCall.workRows construct callbackConstruct work := by
  induction work generalizing branches with
  | nil => cases branches <;> rfl
  | cons cursor rest ih =>
      cases branches with
      | nil => simp at aligned
      | cons branch siblings =>
          simp only [workRows, List.map_append, cursorRows_erase, BodyCall.workRows_cons]
          rw [ih siblings (by simpa using aligned)]

#print axioms body_erase
#print axioms equations_erase
#print axioms source_erase
#print axioms bodyRows_erase
#print axioms mapped_erase
#print axioms bindConsumer_erase
#print axioms invokeRows_erase
#print axioms cursorRows_erase
#print axioms workRows_erase
#print axioms deliver_preserves_rows
#print axioms body_step_preserves_rows
#print axioms invoke_step_preserves_rows
#print axioms step_preserves_rows
#print axioms step_aligned
#print axioms open_rows

end WeightedSource

end BodyCall

/-! Shared worker admission retains absence, a selected body, and ambiguity
separately. Body checks share one structural traversal; no source answers are
evaluated during preparation. -/
namespace Preparation

open AnswerCardinality

private def tabulate {Branch : Type v} (f : Shape → Branch) : ShapeTree Branch :=
  ⟨f ⟨false, false⟩, f ⟨true, false⟩, f ⟨false, true⟩, f ⟨true, true⟩⟩

theorem branch_tabulate {Branch : Type v} (f : Shape → Branch) (input : Shape) :
    (tabulate f).branch input = f input := by
  rcases input with ⟨nonempty, positive⟩
  cases nonempty <;> cases positive <;> rfl

/-- Admission flags and conservative answer bounds for the existing body. -/
structure Checks where
  strict : ShapeTree Bool
  optional : Bool
  bounds : ShapeTree Grade

/-- One structural body traversal derives scalar admission and shape-local
bounds. A recursive call is unknown when its current guards permit it; its
future invocation is never analyzed here. -/
def analyze : Code Value → Checks
  | .empty | .singleton _ =>
      ⟨tabulate (fun _ => true), true, tabulate (fun _ => .one)⟩
  | .unsupported =>
      ⟨tabulate (fun _ => false), false, tabulate (fun _ => .any)⟩
  | .append left right =>
      let l := analyze left
      let r := analyze right
      ⟨tabulate (fun input => l.strict.branch input && r.strict.branch input),
        l.optional && r.optional,
        tabulate (fun input => seq (l.bounds.branch input) (r.bounds.branch input))⟩
  | .mapHead body =>
      let b := analyze body
      ⟨tabulate (fun input => input.nonempty && b.strict.branch input), b.optional,
        tabulate (fun input => if input.nonempty then b.bounds.branch input else .zero)⟩
  | .map _ body => analyze body
  | .ifZero yes no =>
      let y := analyze yes
      let n := analyze no
      ⟨tabulate (fun input => y.strict.branch ⟨input.nonempty, false⟩ &&
          n.strict.branch ⟨input.nonempty, true⟩), y.optional && n.optional,
        tabulate (fun input => if input.positive then n.bounds.branch input else y.bounds.branch input)⟩
  | .ifEmpty yes no =>
      let y := analyze yes
      let n := analyze no
      ⟨tabulate (fun input => y.strict.branch ⟨false, input.positive⟩ &&
          n.strict.branch ⟨true, input.positive⟩), y.optional && n.optional,
        tabulate (fun input => if input.nonempty then n.bounds.branch input else y.bounds.branch input)⟩
  | .callTail =>
      ⟨tabulate (fun input => input.nonempty), true,
        tabulate (fun input => if input.nonempty then .any else .zero)⟩
  | .callPredecessor =>
      ⟨tabulate (fun input => input.nonempty && input.positive), true,
        tabulate (fun input => if input.nonempty && input.positive then .any else .zero)⟩

theorem analyze_strict (body : Code Value) (input : Shape) :
    (analyze body).strict.branch input = check input.nonempty input.positive body := by
  induction body generalizing input <;>
    simp_all only [analyze, branch_tabulate, check]

theorem analyze_optional (body : Code Value) :
    (analyze body).optional = optionalSupported body := by
  induction body <;> simp_all only [analyze, optionalSupported]

/-- For this instruction grammar strict readiness entails optional support.
The converse need not hold, and whole-source support still checks discarded bodies. -/
theorem strict_entails_optional (body : Code Value) (input : Shape)
    (ready : (analyze body).strict.branch input = true) :
    (analyze body).optional = true := by
  rw [analyze_strict] at ready
  rw [analyze_optional]
  induction body generalizing input with
  | empty | singleton | callTail | callPredecessor => rfl
  | unsupported => simp [check] at ready
  | append left right leftIH rightIH =>
      obtain ⟨l, r⟩ := Bool.and_eq_true_iff.mp ready
      exact Bool.and_eq_true_iff.mpr ⟨leftIH input l, rightIH input r⟩
  | mapHead body ih => exact ih input (Bool.and_eq_true_iff.mp ready).2
  | map callback body ih => exact ih input ready
  | ifZero yes no yesIH noIH =>
      obtain ⟨y, n⟩ := Bool.and_eq_true_iff.mp ready
      exact Bool.and_eq_true_iff.mpr
        ⟨yesIH ⟨input.nonempty, false⟩ y, noIH ⟨input.nonempty, true⟩ n⟩
  | ifEmpty yes no yesIH noIH =>
      obtain ⟨y, n⟩ := Bool.and_eq_true_iff.mp ready
      exact Bool.and_eq_true_iff.mpr
        ⟨yesIH ⟨false, input.positive⟩ y, noIH ⟨true, input.positive⟩ n⟩

/-- `none` means ambiguous; `some none` means no matching equation. -/
abbrev Choice (Value : Type v) := Option (Option (Code Value × Checks))

structure Family (Value : Type v) where
  choices : ShapeTree (Choice Value)
  supported : Bool
  bounds : ShapeTree Grade

private def admitHead (input : Shape) (equation : Equation Value)
    (body : Code Value × Checks) (suffix : Choice Value) : Choice Value :=
  if equation.head.accepts input then
    if equation.commit then some (some body)
    else match suffix with
      | some none => some (some body)
      | _ => none
  else suffix

/-- One equation-family fold. Invocation-local commit discards only its
suffix; each equation's body checks are shared by all four head classes. -/
def prepare : List (Equation Value) → Family Value
  | [] => ⟨tabulate (fun _ => some none), true, tabulate (fun _ => .zero)⟩
  | equation :: rest =>
      let suffix := prepare rest
      let body := (equation.body, analyze equation.body)
      ⟨tabulate (fun input =>
          admitHead input equation body (suffix.choices.branch input)),
        body.2.optional && suffix.supported,
        tabulate (fun input =>
          if equation.head.accepts input then
            if equation.commit then body.2.bounds.branch input
            else choice (body.2.bounds.branch input) (suffix.bounds.branch input)
          else suffix.bounds.branch input)⟩

/-- The grade fold follows equation order and source commit, without calls. -/
theorem bounds_cons (equation : Equation Value) (rest : List (Equation Value)) (input : Shape) :
    (prepare (equation :: rest)).bounds.branch input =
      if equation.head.accepts input then
        if equation.commit then (analyze equation.body).bounds.branch input
        else choice ((analyze equation.body).bounds.branch input) ((prepare rest).bounds.branch input)
      else (prepare rest).bounds.branch input := by
  simp only [prepare, branch_tabulate]

theorem bounds_nil (input : Shape) :
    (prepare ([] : List (Equation Value))).bounds.branch input = .zero := by
  simp only [prepare, branch_tabulate]

private theorem select_noMatch (input : Shape) (program : List (Equation Value))
    (absent : noMatch input program = true) : select input program = none := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      simp only [noMatch, List.all_cons, Bool.and_eq_true] at absent
      have unmatched : equation.head.accepts input = false := by simpa using absent.1
      simp [select, unmatched, ih absent.2]

theorem prepare_choice (program : List (Equation Value)) (input : Shape) :
    (prepare program).choices.branch input =
      if noMatch input program then some none
      else (select input program).map (fun body => some (body, analyze body)) := by
  induction program with
  | nil => simp [prepare, branch_tabulate, noMatch]
  | cons equation rest ih =>
      have absentCons : noMatch input (equation :: rest) =
          (!equation.head.accepts input && noMatch input rest) := rfl
      simp only [prepare, branch_tabulate, ih]
      cases matched : equation.head.accepts input <;>
        cases committed : equation.commit <;>
        cases absent : noMatch input rest <;>
        simp [admitHead, matched, committed, select, absentCons, absent]

theorem prepare_supported (program : List (Equation Value)) :
    (prepare program).supported = BodyCall.supportedProgram program := by
  induction program with
  | nil => rfl
  | cons equation rest ih =>
      simp only [prepare, analyze_optional, ih, BodyCall.supportedProgram, List.all_cons]

def strictBranch (family : Family Value) (input : Shape) : Option (Code Value) := do
  let some (body, checks) ← family.choices.branch input | none
  if checks.strict.branch input then some body else none

def optionalBranch (family : Family Value) (input : Shape) : Option (Option (Code Value)) :=
  match family.choices.branch input with
  | none => none
  | some none => some none
  | some (some (body, checks)) => if checks.optional then some (some body) else none

theorem strictBranch_eq (program : List (Equation Value)) (input : Shape) :
    strictBranch (prepare program) input = compileBranch input program := by
  rw [strictBranch, prepare_choice]
  cases absent : noMatch input program with
  | true => simp [compileBranch, select_noMatch input program absent]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases selected : select input program <;>
        simp [compileBranch, selected, analyze_strict]

theorem optionalBranch_eq (program : List (Equation Value)) (input : Shape) :
    optionalBranch (prepare program) input = compileOptionalBranch input program := by
  rw [optionalBranch, prepare_choice]
  cases absent : noMatch input program with
  | true => simp [absent, compileOptionalBranch]
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases selected : select input program <;>
        simp [compileOptionalBranch, absent, selected, analyze_optional]

private def gather {Branch : Type v} (tree : ShapeTree (Option Branch)) :
    Option (ShapeTree Branch) := do
  let ze ← tree.zeroEmpty
  let zc ← tree.zeroCons
  let pe ← tree.positiveEmpty
  let pc ← tree.positiveCons
  pure ⟨ze, zc, pe, pc⟩

def strictTree (family : Family Value) : Option (DecisionTree Value) :=
  gather (tabulate (strictBranch family))

def optionalTree (family : Family Value) : Option (ShapeTree (Option (Code Value))) :=
  gather (tabulate (optionalBranch family))

def strictCode (family : Family Value) : Option (Code Value) :=
  (strictTree family).map DecisionTree.code

theorem strictTree_eq (program : List (Equation Value)) :
    strictTree (prepare program) = compileTree program := by
  simp only [strictTree, gather, tabulate, strictBranch_eq, compileTree]

theorem optionalTree_eq (program : List (Equation Value)) :
    optionalTree (prepare program) = compileOptionalTree program := by
  simp only [optionalTree, gather, tabulate, optionalBranch_eq, compileOptionalTree]

theorem strictCode_eq (program : List (Equation Value)) :
    strictCode (prepare program) = compile program := by
  rw [strictCode, strictTree_eq, compile]

#print axioms analyze_strict
#print axioms analyze_optional
#print axioms strict_entails_optional
#print axioms prepare_choice
#print axioms prepare_supported
#print axioms strictBranch_eq
#print axioms optionalBranch_eq
#print axioms strictTree_eq
#print axioms optionalTree_eq
#print axioms strictCode_eq

end Preparation

end Mettapedia.Machines.SourceProducerAdmission
