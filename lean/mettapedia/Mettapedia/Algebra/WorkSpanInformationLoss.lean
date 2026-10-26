import Mettapedia.Algebra.WorkSpan
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Data.Set.Operations

/-!
# Recovering observations from supplied costs

A cost function forgets an observation precisely when it identifies executions
that the observation distinguishes. Recovery is unique on realized costs when
the observation is constant on cost fibres. No value is chosen for unrealized
costs; in particular, an empty execution type needs no inhabited attribute type.
Concrete operational collisions belong in the execution adapter.
-/

namespace Mettapedia.Algebra

open Mettapedia.GSLT.Core.NonFactorization

/-- Observe a chosen representative of each realized cost. Fibre constancy is
the condition under which this choice recovers the supplied observation. -/
noncomputable def recoverOnImage {Execution Cost Attribute : Type*}
    (cost : Execution → Cost) (observe : Execution → Attribute) : Set.range cost → Attribute :=
  observe ∘ Function.surjInv (Set.rangeFactorization_surjective (f := cost))

@[simp] theorem recoverOnImage_apply {Execution Cost Attribute : Type*}
    (cost : Execution → Cost) (observe : Execution → Attribute)
    (constant : observe.FactorsThrough cost) (execution : Execution) :
    recoverOnImage cost observe (Set.rangeFactorization cost execution) = observe execution :=
  constant (congrArg Subtype.val (Function.surjInv_eq Set.rangeFactorization_surjective _))

/-- Correct recovery determines the entire function on the realized image. -/
theorem recoverOnImage_unique {Execution Cost Attribute : Type*}
    (cost : Execution → Cost) (observe : Execution → Attribute)
    (constant : observe.FactorsThrough cost) (recover : Set.range cost → Attribute)
    (correct : ∀ execution, recover (Set.rangeFactorization cost execution) = observe execution) :
    recover = recoverOnImage cost observe := by
  funext value
  obtain ⟨execution, rfl⟩ := Set.rangeFactorization_surjective value
  exact (correct execution).trans (recoverOnImage_apply cost observe constant execution).symm

/-- The existing factorization criterion, without defaults outside the image. -/
theorem recovery_on_image_iff {Execution Cost Attribute : Type*}
    (cost : Execution → Cost) (observe : Execution → Attribute) :
    Factors (Set.rangeFactorization cost) observe ↔ observe.FactorsThrough cost := by
  rw [factors_iff_constantOnFibers Set.rangeFactorization_surjective]
  exact ⟨fun constant _ _ same => constant _ _ (Subtype.ext same),
    fun constant _ _ same => constant (congrArg Subtype.val same)⟩

namespace WorkSpan

/-- Two unit jobs have equal work but different sequential and parallel span. -/
theorem work_does_not_determine_span :
    ∃ left right : WorkSpan,
      left.work = right.work ∧ left.span ≠ right.span :=
  ⟨⟨2, 2⟩, ⟨2, 1⟩, rfl, by decide⟩

/-- Equal span does not determine work. -/
theorem span_does_not_determine_work :
    ∃ left right : WorkSpan,
      left.span = right.span ∧ left.work ≠ right.work :=
  ⟨⟨1, 1⟩, ⟨2, 1⟩, rfl, by decide⟩

/-- An empty branch makes the sequential and parallel cost combinators agree. -/
theorem sequential_eq_parallel_of_zero_right (value : WorkSpan) :
    sequential value 0 = parallel value 0 := by simp

/-- Equality at some inputs does not identify the two cost combinators. -/
theorem workSpan_forgets_schedule_shape :
    ∃ left right : WorkSpan,
      sequential left right = parallel left right ∧
        ¬ ∀ first second : WorkSpan,
          sequential first second = parallel first second := by
  refine ⟨⟨1, 1⟩, 0, sequential_eq_parallel_of_zero_right _, ?_⟩
  exact fun allEqual => by
    simpa [sequential, parallel] using congrArg span (allEqual ⟨0, 1⟩ ⟨0, 1⟩)

end WorkSpan

end Mettapedia.Algebra
