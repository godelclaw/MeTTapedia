import Mettapedia.Languages.C11.Sequencing
import Mathlib.Data.List.OfFn

/-!
# Plain finite data for C occurrence sequencing

The represented order is a complete square Boolean matrix. Access labels
are an exact occurrence-indexed list. Decoding validates both dimensions;
its fallback lookup values cannot become admitted missing occurrences.
Both order and evaluation codecs have their two inverse laws, so they retain
the full sequencing relation and scalar identities rather than only one
chosen linear execution trace.

This data interface describes an already constructed evaluation. Native
Cesta syntax and source object identity must be connected separately. A
decoded graph does not authenticate its execution history or commit effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.SequencingData

open Sequencing

abbrev Matrix := List (List Bool)

def encodeOrder {count : Nat} (order : Order (Fin count)) : Matrix :=
  List.ofFn fun first => List.ofFn fun second => order.before first second

def shape (count : Nat) (matrix : Matrix) : Bool :=
  decide (matrix.length = count) && matrix.all (fun row => decide (row.length = count))

theorem shape_iff (count : Nat) (matrix : Matrix) : shape count matrix = true ↔
    matrix.length = count ∧ ∀ row ∈ matrix, row.length = count := by
  simp only [shape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

def decodeOrder (count : Nat) (matrix : Matrix) : Option (Order (Fin count)) :=
  if shape count matrix then
    some ⟨fun first second => (((matrix[first.val]?).getD [])[second.val]?).getD false⟩
  else none

theorem encodeOrder_shape {count : Nat} (order : Order (Fin count)) : shape count (encodeOrder order) = true := by
  apply (shape_iff count _).mpr
  constructor
  · simp [encodeOrder]
  · intro row present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    simp

theorem decodeOrder_encode {count : Nat} (order : Order (Fin count)) :
    decodeOrder count (encodeOrder order) = some order := by
  simp only [decodeOrder, encodeOrder_shape, ↓reduceIte]
  congr 1
  cases order
  congr 1
  funext first second
  simp [encodeOrder, first.isLt, second.isLt]

theorem encodeOrder_decode (count : Nat) (matrix : Matrix) (order : Order (Fin count))
    (decoded : decodeOrder count matrix = some order) : encodeOrder order = matrix := by
  by_cases valid : shape count matrix = true
  · have dimensions := (shape_iff count matrix).mp valid
    simp only [decodeOrder, valid, ↓reduceIte, Option.some.injEq] at decoded
    subst order
    apply List.ext_getElem
    · simpa [encodeOrder] using dimensions.1.symm
    · intro first leftBound rightBound
      have firstBound : first < count := by simpa [encodeOrder] using leftBound
      have rowLength : (matrix[first]).length = count := dimensions.2 _ (List.getElem_mem rightBound)
      simp only [encodeOrder, List.getElem_ofFn]
      apply List.ext_getElem
      · simpa using rowLength.symm
      · intro second smallLeft smallRight
        simp [List.getElem?_eq_getElem rightBound, List.getElem?_eq_getElem smallRight]
  · simp [decodeOrder, valid] at decoded

structure EvaluationData where
  matrix : Matrix
  accesses : List (Access Nat)
  deriving DecidableEq, Repr

def encodeEvaluation {count : Nat} (evaluation : Evaluation (Fin count) Nat) : EvaluationData :=
  ⟨encodeOrder evaluation.order, List.ofFn evaluation.access⟩

def decodeEvaluation (count : Nat) (data : EvaluationData) : Option (Evaluation (Fin count) Nat) := do
  let order ← decodeOrder count data.matrix
  if data.accesses.length = count then
    some ⟨order, fun index => (data.accesses[index.val]?).getD .other⟩
  else none

theorem decodeEvaluation_encode {count : Nat} (evaluation : Evaluation (Fin count) Nat) :
    decodeEvaluation count (encodeEvaluation evaluation) = some evaluation := by
  simp only [decodeEvaluation, encodeEvaluation, decodeOrder_encode, bind, Option.bind_some, List.length_ofFn, ↓reduceIte]
  congr 1
  cases evaluation
  congr 1
  funext index
  simp [index.isLt]

theorem encodeEvaluation_decode (count : Nat) (data : EvaluationData)
    (evaluation : Evaluation (Fin count) Nat) (decoded : decodeEvaluation count data = some evaluation) :
    encodeEvaluation evaluation = data := by
  cases orderDecoded : decodeOrder count data.matrix with
  | none => simp [decodeEvaluation, orderDecoded] at decoded
  | some order =>
      by_cases length : data.accesses.length = count
      · simp only [decodeEvaluation, orderDecoded, bind, Option.bind_some, length, ↓reduceIte, Option.some.injEq] at decoded
        subst evaluation
        have matrix := encodeOrder_decode count data.matrix order orderDecoded
        have accesses : List.ofFn (fun index : Fin count => (data.accesses[index.val]?).getD .other) = data.accesses := by
          apply List.ext_getElem
          · simpa using length.symm
          · intro index first second
            simp [List.getElem?_eq_getElem second]
        cases data
        simp only [encodeEvaluation, matrix, accesses]
      · simp [decodeEvaluation, orderDecoded, length] at decoded

def inspect (count : Nat) (data : EvaluationData) : Option (CheckResult (Fin count)) := do
  let evaluation ← decodeEvaluation count data
  some (checkFamily (.fin count) [evaluation])

theorem inspect_accepted (count : Nat) (data : EvaluationData) (accepted : inspect count data = some .safe) :
    ∃ evaluation, decodeEvaluation count data = some evaluation ∧
      encodeEvaluation evaluation = data ∧ evaluation.order.Valid ∧ ¬ evaluation.Undefined := by
  cases decoded : decodeEvaluation count data with
  | none => simp [inspect, decoded] at accepted
  | some evaluation =>
      have checked : checkFamily (.fin count) [evaluation] = .safe := by simpa [inspect, decoded] using accepted
      have sound := (checkFamily_safe_iff (.fin count) [evaluation]).mp checked
      exact ⟨evaluation, rfl, encodeEvaluation_decode count data evaluation decoded,
        sound.2 evaluation (by simp)⟩

theorem inspect_complete {count : Nat} (evaluation : Evaluation (Fin count) Nat)
    (valid : evaluation.order.Valid) (clean : ¬ evaluation.Undefined) :
    inspect count (encodeEvaluation evaluation) = some .safe := by
  have checked : checkFamily (.fin count) [evaluation] = .safe :=
    (checkFamily_safe_iff (.fin count) [evaluation]).mpr ⟨by simp, by simpa using And.intro valid clean⟩
  simp [inspect, decodeEvaluation_encode, checked]

end Mettapedia.Languages.C11.SequencingData
