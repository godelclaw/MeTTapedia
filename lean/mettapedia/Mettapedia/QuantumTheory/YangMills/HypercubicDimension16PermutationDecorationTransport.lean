import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CycleBlockDecoration

/-!
# Transport of indexed decoration characters

The signed decoration character is invariant under a change of the finite
label type.  Both the exact derivative-degree fiber and the tensor-sign
product are transported explicitly.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PermutationDecorationTransport

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16CycleBlockDecoration

def transportIndexedDecoration
    {Source Target : Type*} (labelEquiv : Source ≃ Target)
    {derivativeBudget : ℕ}
    (letters : Source → LocalFieldLetter derivativeBudget) :
    Target → LocalFieldLetter derivativeBudget :=
  fun target => letters (labelEquiv.symm target)

def transportIndexedDecorationEquiv
    {Source Target : Type*} (labelEquiv : Source ≃ Target)
    (derivativeBudget : ℕ) :
    (Source → LocalFieldLetter derivativeBudget) ≃
      (Target → LocalFieldLetter derivativeBudget) :=
  Equiv.arrowCongr labelEquiv (Equiv.refl _)

@[simp] theorem transportIndexedDecorationEquiv_apply
    {Source Target : Type*} (labelEquiv : Source ≃ Target)
    (derivativeBudget : ℕ)
    (letters : Source → LocalFieldLetter derivativeBudget)
    (target : Target) :
    transportIndexedDecorationEquiv labelEquiv derivativeBudget letters target =
      transportIndexedDecoration labelEquiv letters target :=
  rfl

theorem transportIndexedDecoration_degree
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (labelEquiv : Source ≃ Target) (derivativeBudget : ℕ)
    (letters : Source → LocalFieldLetter derivativeBudget) :
    (∑ target,
        (transportIndexedDecoration labelEquiv letters target).derivativeCount.1) =
      ∑ source, (letters source).derivativeCount.1 := by
  exact Equiv.sum_comp labelEquiv.symm
    (fun source => (letters source).derivativeCount.1)

theorem transportIndexedDecoration_tensorSign
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (labelEquiv : Source ≃ Target) (h : Hypercubic4)
    (derivativeBudget : ℕ)
    (letters : Source → LocalFieldLetter derivativeBudget) :
    (∏ target,
        (transportIndexedDecoration labelEquiv letters target).tensorSign h) =
      ∏ source, (letters source).tensorSign h := by
  exact Equiv.prod_comp labelEquiv.symm
    (fun source => (letters source).tensorSign h)

theorem isTwistedIndexedDecoration_transport_iff
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    (labelEquiv : Source ≃ Target)
    (h : Hypercubic4) (rename : Equiv.Perm Source)
    (derivativeBudget targetDegree : ℕ)
    (letters : Source → LocalFieldLetter derivativeBudget) :
    IsTwistedIndexedDecoration h
        (labelEquiv.permCongr rename) derivativeBudget targetDegree
        (transportIndexedDecoration labelEquiv letters) ↔
      IsTwistedIndexedDecoration h rename derivativeBudget targetDegree
        letters := by
  constructor
  · intro transported
    refine ⟨?_, ?_⟩
    · rw [← transportIndexedDecoration_degree labelEquiv derivativeBudget
          letters]
      exact transported.1
    · intro source
      have pointwise := transported.2 (labelEquiv source)
      simpa [transportIndexedDecoration] using pointwise
  · intro original
    refine ⟨?_, ?_⟩
    · rw [transportIndexedDecoration_degree labelEquiv derivativeBudget
          letters]
      exact original.1
    · intro target
      simpa [transportIndexedDecoration] using
        original.2 (labelEquiv.symm target)

/-- Exact invariance of the signed decoration character under an arbitrary
finite change of labels. -/
theorem indexedDecorationCharacter_permCongr
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (labelEquiv : Source ≃ Target)
    (h : Hypercubic4) (rename : Equiv.Perm Source)
    (derivativeBudget targetDegree : ℕ) :
    indexedDecorationCharacter h rename derivativeBudget targetDegree =
      indexedDecorationCharacter h (labelEquiv.permCongr rename)
        derivativeBudget targetDegree := by
  classical
  unfold indexedDecorationCharacter
  apply Fintype.sum_equiv
    (transportIndexedDecorationEquiv labelEquiv derivativeBudget)
  intro letters
  unfold indexedDecorationWeight
  have transportedEq :
      transportIndexedDecorationEquiv labelEquiv derivativeBudget letters =
        transportIndexedDecoration labelEquiv letters := rfl
  rw [transportedEq]
  by_cases original :
      IsTwistedIndexedDecoration h rename derivativeBudget targetDegree letters
  · have transported :=
      (isTwistedIndexedDecoration_transport_iff labelEquiv h rename
        derivativeBudget targetDegree letters).mpr original
    rw [if_pos original, if_pos transported]
    exact (transportIndexedDecoration_tensorSign labelEquiv h
      derivativeBudget letters).symm
  · have notTransported :
        ¬IsTwistedIndexedDecoration h (labelEquiv.permCongr rename)
          derivativeBudget targetDegree
          (transportIndexedDecoration labelEquiv letters) :=
      fun transported =>
        original ((isTwistedIndexedDecoration_transport_iff labelEquiv h rename
          derivativeBudget targetDegree letters).mp transported)
    rw [if_neg original, if_neg notTransported]

end HypercubicDimension16PermutationDecorationTransport
end YangMills
end QuantumTheory
end Mettapedia
