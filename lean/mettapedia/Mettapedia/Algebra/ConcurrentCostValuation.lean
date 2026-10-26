import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Core.Composition

/-!
# Sequential and parallel event valuations

A concurrent cost algebra supplies two total partial monoids. Their construction
adds neither a scheduler nor independence evidence. WorkSpan's two unit jobs
separate the resulting accounts even though both are total and lawful.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.ConcurrentCostValuation

open Mettapedia.GSLT

universe u

/-- Any total associative operation with a two-sided unit gives a partial
monoid that accepts every pair. No scheduling policy is added. -/
def totalPartialMonoid {Cost : Type u} (unit : Cost) (op : Cost → Cost → Cost)
    (leftUnit : ∀ value, op unit value = value)
    (rightUnit : ∀ value, op value unit = value)
    (assoc : ∀ first second third, op (op first second) third = op first (op second third)) :
    PartialMonoid Cost where
  unit := unit
  op first second := some (op first second)
  unit_op value := congrArg some (leftUnit value)
  op_unit value := congrArg some (rightUnit value)
  op_assoc first second third := congrArg some (assoc first second third)

/-- The sequential operation as a total partial event valuation. -/
def sequentialPartialMonoid {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) : PartialMonoid Cost :=
  totalPartialMonoid algebra.zero algebra.sequential algebra.sequential_zero_left
    algebra.sequential_zero_right algebra.sequential_assoc

/-- The parallel operation as a total partial event valuation. Using this
account still requires evidence that the events may run independently. -/
def parallelPartialMonoid {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) : PartialMonoid Cost :=
  totalPartialMonoid algebra.zero algebra.parallel algebra.parallel_zero_left
    algebra.parallel_zero_right algebra.parallel_assoc

theorem sequential_op_isSome {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) (first second : Cost) :
    ((sequentialPartialMonoid algebra).op first second).isSome := rfl

theorem parallel_op_isSome {Cost : Type u} [Preorder Cost]
    (algebra : ConcurrentCostAlgebra Cost) (left right : Cost) :
    ((parallelPartialMonoid algebra).op left right).isSome := rfl

/-- The concrete WorkSpan sequential valuation algebra. -/
abbrev workSpanSequential : PartialMonoid WorkSpan :=
  sequentialPartialMonoid WorkSpan.algebra

/-- The concrete WorkSpan parallel valuation algebra. -/
abbrev workSpanParallel : PartialMonoid WorkSpan :=
  parallelPartialMonoid WorkSpan.algebra

/-- Positive control: two unit jobs accumulate exactly two units of work and
two units of sequential span. -/
theorem workSpanSequential_two_units :
    workSpanSequential.op ⟨1, 1⟩ ⟨1, 1⟩ = some ⟨2, 2⟩ := rfl

/-- Positive control: the same jobs have parallel span one. -/
theorem workSpanParallel_two_units :
    workSpanParallel.op ⟨1, 1⟩ ⟨1, 1⟩ = some ⟨2, 1⟩ := rfl

/-- Negative control: lawfulness and totality do not collapse the two
compositions. -/
theorem workSpan_valuation_compositions_distinct :
    workSpanSequential.op ⟨1, 1⟩ ⟨1, 1⟩ ≠
      workSpanParallel.op ⟨1, 1⟩ ⟨1, 1⟩ := by
  decide

end Mettapedia.Algebra.ConcurrentCostValuation
