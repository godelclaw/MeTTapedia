import Mettapedia.Machines.RecursiveFiniteProducer
import Mettapedia.Machines.EquationCut
import Mettapedia.Machines.AnswerCardinality

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

`RetainedFrontier` publishes one matched equation at a time. It keeps every
authored equation and that invocation's captured items and parameter, then
calls the existing `bodyResults` helper on that equation alone. `tailResults`
is supplied already computed. The frontier is not an index into a precomputed
answer list, and it is not a body or call cursor: `append`, `map`, `mapHead`,
`ifZero`, `ifEmpty`, `callTail` and `callPredecessor` are not frames here.
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

end Mettapedia.Machines.SourceProducerAdmission
