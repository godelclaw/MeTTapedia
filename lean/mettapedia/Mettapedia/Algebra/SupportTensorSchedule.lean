import Mettapedia.Algebra.SupportTensor

/-!
# Independent-row interleaving without reassociation

A loop over columns can update a vector of independent row accumulators,
rather than finish one row at a time. The observation of each row is its
original left fold. The step is arbitrary, so the law needs neither
associativity nor commutativity and applies to a specified rounded step.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportTensorSchedule

variable {I C A B : Type*}

def interleaved (step : A → B → A) (initial : I → A)
    (columns : List C) (input : I → C → B) : I → A :=
  columns.foldl (fun state column => fun row => step (state row) (input row column)) initial

theorem observe_interleaved (step : A → B → A) (initial : I → A)
    (columns : List C) (input : I → C → B) (row : I) :
    interleaved step initial columns input row =
      columns.foldl (fun accumulator column => step accumulator (input row column)) (initial row) := by
  induction columns generalizing initial with
  | nil => rfl
  | cons column rest ih =>
      simpa only [interleaved, List.foldl_cons] using
        ih (fun row => step (initial row) (input row column))

theorem interleaved_eq_independent_rows (step : A → B → A) (initial : I → A)
    (columns : List C) (input : I → C → B) :
    interleaved step initial columns input =
      fun row => columns.foldl (fun accumulator column => step accumulator (input row column)) (initial row) := by
  funext row
  exact observe_interleaved step initial columns input row

/-- Splitting an execution into consecutive column blocks preserves the
original schedule; combining partial sums by another operation is not used. -/
theorem interleaved_append (step : A → B → A) (initial : I → A)
    (first second : List C) (input : I → C → B) :
    interleaved step initial (first++second) input =
      interleaved step (interleaved step initial first input) second input := by
  simp [interleaved, List.foldl_append]

example : interleaved (fun (xs : List Nat) v => xs++[v]) (fun (_ : Bool) => [])
    [0,1,2] (fun row col => if row then col else col+4) true = [0,1,2] := by decide
example : interleaved (fun (xs : List Nat) v => xs++[v]) (fun (_ : Bool) => [])
    [0,1,2] (fun row col => if row then col else col+4) false = [4,5,6] := by decide
example : ([0,1,2] : List Nat).foldl (fun xs v => xs++[v]) [] ≠
    ([2,1,0] : List Nat).foldl (fun xs v => xs++[v]) [] := by decide

#print axioms interleaved_eq_independent_rows

end Mettapedia.Algebra.SupportTensorSchedule
