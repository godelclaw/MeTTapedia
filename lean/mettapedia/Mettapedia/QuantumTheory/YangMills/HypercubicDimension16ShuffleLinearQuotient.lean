import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ShuffleQuotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Exact linear quotient by adjacent derivative shuffles

The set quotient of global owner--axis words by adjacent swaps is not by
itself a rank theorem.  This module linearizes owner-localization over the
rationals and proves that its kernel is exactly the span of the literal
two-term rows obtained by one adjacent interchange of different owners.

The proof lifts the previously established list-level generated equivalence
to fixed-length vectors.  It then follows an `EqvGen` chain linearly: a
relation step supplies one generator row, symmetry negates a row, and
transitivity adds rows.  Thus no fiber equality is inserted as a bespoke
relation generator.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ShuffleLinearQuotient

open HypercubicDimension16ShuffleQuotient

abbrev GlobalOwnedAxisWordSpace (fieldCount derivativeCount : ℕ) :=
  GlobalOwnedAxisWord fieldCount derivativeCount →₀ ℚ

abbrev LocalAxisWordFamilySpace (fieldCount derivativeCount : ℕ) :=
  LocalAxisWordFamily fieldCount derivativeCount →₀ ℚ

/-! ## The linear localization map and its right inverse -/

def linearLocalizeBasis {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    LocalAxisWordFamilySpace fieldCount derivativeCount :=
  Finsupp.single (localize word) 1

def linearLocalize (fieldCount derivativeCount : ℕ) :
    GlobalOwnedAxisWordSpace fieldCount derivativeCount →ₗ[ℚ]
      LocalAxisWordFamilySpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ linearLocalizeBasis

@[simp] theorem linearLocalize_single {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount)
    (coefficient : ℚ) :
    linearLocalize fieldCount derivativeCount
        (Finsupp.single word coefficient) =
      coefficient • linearLocalizeBasis word := by
  simp [linearLocalize]

def linearGlobalizeBasis {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount) :
    GlobalOwnedAxisWordSpace fieldCount derivativeCount :=
  Finsupp.single (globalize family) 1

def linearGlobalize (fieldCount derivativeCount : ℕ) :
    LocalAxisWordFamilySpace fieldCount derivativeCount →ₗ[ℚ]
      GlobalOwnedAxisWordSpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ linearGlobalizeBasis

@[simp] theorem linearGlobalize_single {fieldCount derivativeCount : ℕ}
    (family : LocalAxisWordFamily fieldCount derivativeCount)
    (coefficient : ℚ) :
    linearGlobalize fieldCount derivativeCount
        (Finsupp.single family coefficient) =
      coefficient • linearGlobalizeBasis family := by
  simp [linearGlobalize]

theorem linearLocalize_linearGlobalize (fieldCount derivativeCount : ℕ)
    (value : LocalAxisWordFamilySpace fieldCount derivativeCount) :
    linearLocalize fieldCount derivativeCount
        (linearGlobalize fieldCount derivativeCount value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single family coefficient =>
      simp [linearGlobalizeBasis, linearLocalizeBasis,
        localize_globalize]

/-! ## Literal fixed-length generators -/

structure LiteralShuffleSite (fieldCount derivativeCount : ℕ) where
  source : GlobalOwnedAxisWord fieldCount derivativeCount
  target : GlobalOwnedAxisWord fieldCount derivativeCount
  step : IsAdjacentDifferentOwnerSwap source target

def literalShuffleRow {fieldCount derivativeCount : ℕ}
    (site : LiteralShuffleSite fieldCount derivativeCount) :
    GlobalOwnedAxisWordSpace fieldCount derivativeCount :=
  Finsupp.single site.source 1 - Finsupp.single site.target 1

def literalShuffleSubmodule (fieldCount derivativeCount : ℕ) :
    Submodule ℚ (GlobalOwnedAxisWordSpace fieldCount derivativeCount) :=
  Submodule.span ℚ
    (Set.range (literalShuffleRow :
      LiteralShuffleSite fieldCount derivativeCount →
        GlobalOwnedAxisWordSpace fieldCount derivativeCount))

theorem linearLocalize_literalShuffleRow {fieldCount derivativeCount : ℕ}
    (site : LiteralShuffleSite fieldCount derivativeCount) :
    linearLocalize fieldCount derivativeCount (literalShuffleRow site) = 0 := by
  have hsemantic := adjacentDifferentOwnerSwap_semanticallyEquivalent site.step
  change localize site.source = localize site.target at hsemantic
  simp [literalShuffleRow, map_sub, linearLocalizeBasis, hsemantic]

/-! ## Lifting the list-generated theorem to fixed-length vectors -/

theorem listAdjacentDifferentOwnerSwap_length_eq {fieldCount : ℕ}
    {left right : List (OwnedAxis fieldCount)}
    (hstep : ListAdjacentDifferentOwnerSwap left right) :
    left.length = right.length := by
  rcases hstep with
    ⟨headEntries, tailEntries, first, second, _hdifferent, hleft, hright⟩
  rw [hleft, hright]
  simp

theorem listShuffleGeneratedEquivalent_length_eq {fieldCount : ℕ}
    {left right : List (OwnedAxis fieldCount)}
    (hgenerated : ListShuffleGeneratedEquivalent left right) :
    left.length = right.length := by
  induction hgenerated with
  | rel source target hstep =>
      exact listAdjacentDifferentOwnerSwap_length_eq hstep
  | refl source => rfl
  | symm source target _ ih => exact ih.symm
  | trans source middle target _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem listShuffleGeneratedEquivalent_liftVector
    {fieldCount derivativeCount : ℕ}
    (left right : List (OwnedAxis fieldCount))
    (hleft : left.length = derivativeCount)
    (hright : right.length = derivativeCount)
    (hgenerated : ListShuffleGeneratedEquivalent left right) :
    Relation.EqvGen IsAdjacentDifferentOwnerSwap
      (⟨left, hleft⟩ : GlobalOwnedAxisWord fieldCount derivativeCount)
      (⟨right, hright⟩ : GlobalOwnedAxisWord fieldCount derivativeCount) := by
  induction hgenerated with
  | rel source target hstep =>
      exact Relation.EqvGen.rel _ _ hstep
  | refl source =>
      have heq :
          (⟨source, hleft⟩ : GlobalOwnedAxisWord fieldCount derivativeCount) =
            ⟨source, hright⟩ := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact Relation.EqvGen.refl _
  | symm source target _ ih =>
      exact Relation.EqvGen.symm _ _ (ih hright hleft)
  | trans source middle target hsourceMiddle _hmiddleTarget ih₁ ih₂ =>
      have hmiddle : middle.length = derivativeCount :=
        (listShuffleGeneratedEquivalent_length_eq hsourceMiddle).symm.trans
          hleft
      exact Relation.EqvGen.trans _ _ _
        (ih₁ hleft hmiddle) (ih₂ hmiddle hright)

theorem semanticShuffleEquivalent_generatedVector
    {fieldCount derivativeCount : ℕ}
    (left right : GlobalOwnedAxisWord fieldCount derivativeCount)
    (hsemantic : SemanticShuffleEquivalent left right) :
    Relation.EqvGen IsAdjacentDifferentOwnerSwap left right := by
  have hlist := ownerAxisProjection_eq_listShuffleGeneratedEquivalent
    left.toList right.toList (by
      intro owner
      exact congrArg (fun family => family.1 owner) hsemantic)
  exact listShuffleGeneratedEquivalent_liftVector
    left.toList right.toList left.toList_length right.toList_length hlist

/-- Every list-splice presentation of one literal vector step is the swap of
two concrete adjacent `Fin` positions.  This is the bridge back to the sparse
position-indexed relation operator. -/
theorem isAdjacentDifferentOwnerSwap_exists_positions
    {fieldCount derivativeCount : ℕ}
    (left right : GlobalOwnedAxisWord fieldCount derivativeCount)
    (hstep : IsAdjacentDifferentOwnerSwap left right) :
    ∃ (firstPosition secondPosition : Fin derivativeCount),
      firstPosition.1 + 1 = secondPosition.1 ∧
      (left.get firstPosition).1 ≠ (left.get secondPosition).1 ∧
      right = List.Vector.ofFn
        (left.get ∘ Equiv.swap firstPosition secondPosition) := by
  rcases hstep with
    ⟨headEntries, tailEntries, first, second, hdifferent, hleft, hright⟩
  have hlength : headEntries.length + 2 + tailEntries.length =
      derivativeCount := by
    have := left.toList_length
    rw [hleft] at this
    simp at this
    omega
  have hnext : headEntries.length + 1 < derivativeCount := by omega
  let firstPosition : Fin derivativeCount :=
    ⟨headEntries.length, by omega⟩
  let secondPosition : Fin derivativeCount :=
    ⟨headEntries.length + 1, hnext⟩
  have hfirst : left.get firstPosition = first := by
    rw [List.Vector.get_eq_get_toList]
    simp [firstPosition, hleft]
  have hsecond : left.get secondPosition = second := by
    rw [List.Vector.get_eq_get_toList]
    simp [secondPosition, hleft]
  have hswap := list_ofFn_adjacent_swap left.get headEntries.length hnext
  have hofFn : List.ofFn left.get = left.toList := by
    have hvector := congrArg List.Vector.toList (List.Vector.ofFn_get left)
    simpa only [List.Vector.toList_ofFn] using hvector
  rw [hofFn, hleft, hfirst, hsecond] at hswap
  have htarget : List.Vector.ofFn
      (left.get ∘ Equiv.swap firstPosition secondPosition) = right := by
    apply List.Vector.eq
    rw [List.Vector.toList_ofFn, hswap, hright]
    simp
  exact ⟨firstPosition, secondPosition, rfl, by simpa [hfirst, hsecond],
    htarget.symm⟩

/-! ## Generated chains give exactly the linear kernel -/

theorem generatedVector_difference_mem
    {fieldCount derivativeCount : ℕ}
    {left right : GlobalOwnedAxisWord fieldCount derivativeCount}
    (hgenerated : Relation.EqvGen IsAdjacentDifferentOwnerSwap left right) :
    Finsupp.single left 1 - Finsupp.single right 1 ∈
      literalShuffleSubmodule fieldCount derivativeCount := by
  induction hgenerated with
  | rel source target hstep =>
      exact Submodule.subset_span
        ⟨({ source := source, target := target, step := hstep } :
          LiteralShuffleSite fieldCount derivativeCount), rfl⟩
  | refl source => simp
  | symm source target _ ih =>
      have hneg := (literalShuffleSubmodule fieldCount derivativeCount).neg_mem ih
      simpa only [neg_sub] using hneg
  | trans source middle target _ _ ih₁ ih₂ =>
      have hadd := (literalShuffleSubmodule fieldCount derivativeCount).add_mem
        ih₁ ih₂
      convert hadd using 1
      module

theorem globalOwnedAxisWord_basis_residual_mem
    {fieldCount derivativeCount : ℕ}
    (word : GlobalOwnedAxisWord fieldCount derivativeCount) :
    Finsupp.single word 1 -
        linearGlobalize fieldCount derivativeCount
          (linearLocalizeBasis word) ∈
      literalShuffleSubmodule fieldCount derivativeCount := by
  have hsemantic : SemanticShuffleEquivalent word
      (globalize (localize word)) :=
    (localize_globalize (localize word)).symm
  have hgenerated := semanticShuffleEquivalent_generatedVector word
    (globalize (localize word)) hsemantic
  simpa [linearLocalizeBasis, linearGlobalizeBasis] using
    generatedVector_difference_mem hgenerated

theorem globalOwnedAxisWord_residual_mem
    {fieldCount derivativeCount : ℕ}
    (value : GlobalOwnedAxisWordSpace fieldCount derivativeCount) :
    value - linearGlobalize fieldCount derivativeCount
        (linearLocalize fieldCount derivativeCount value) ∈
      literalShuffleSubmodule fieldCount derivativeCount := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      have hadd := (literalShuffleSubmodule fieldCount derivativeCount).add_mem
        hleft hright
      convert hadd using 1
      simp [map_add]
      module
  | single word coefficient =>
      have hscaled := (literalShuffleSubmodule fieldCount derivativeCount).smul_mem
        coefficient (globalOwnedAxisWord_basis_residual_mem word)
      simpa [smul_sub] using hscaled

theorem ker_linearLocalize_eq_literalShuffleSubmodule
    (fieldCount derivativeCount : ℕ) :
    LinearMap.ker (linearLocalize fieldCount derivativeCount) =
      literalShuffleSubmodule fieldCount derivativeCount := by
  apply le_antisymm
  · intro value hkernel
    have hresidual := globalOwnedAxisWord_residual_mem value
    rw [LinearMap.mem_ker.mp hkernel] at hresidual
    simpa using hresidual
  · unfold literalShuffleSubmodule
    rw [Submodule.span_le]
    rintro value ⟨site, rfl⟩
    exact LinearMap.mem_ker.mpr (linearLocalize_literalShuffleRow site)

theorem linearLocalize_surjective (fieldCount derivativeCount : ℕ) :
    Function.Surjective (linearLocalize fieldCount derivativeCount) := by
  intro value
  exact ⟨linearGlobalize fieldCount derivativeCount value,
    linearLocalize_linearGlobalize fieldCount derivativeCount value⟩

def literalShuffleQuotientEquivLocal (fieldCount derivativeCount : ℕ) :
    (GlobalOwnedAxisWordSpace fieldCount derivativeCount ⧸
        literalShuffleSubmodule fieldCount derivativeCount) ≃ₗ[ℚ]
      LocalAxisWordFamilySpace fieldCount derivativeCount :=
  (Submodule.quotEquivOfEq (literalShuffleSubmodule fieldCount derivativeCount)
      (LinearMap.ker (linearLocalize fieldCount derivativeCount))
      (ker_linearLocalize_eq_literalShuffleSubmodule
        fieldCount derivativeCount).symm).trans
    ((linearLocalize fieldCount derivativeCount).quotKerEquivOfSurjective
      (linearLocalize_surjective fieldCount derivativeCount))

end HypercubicDimension16ShuffleLinearQuotient
end YangMills
end QuantumTheory
end Mettapedia
