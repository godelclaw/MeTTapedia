import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PartitionRepresentatives

/-!
# Exact conjugacy compression of the dimension-sixteen carrier

The permutation-fixed Burnside numerator is regrouped by the standard
integer partition of each field permutation.  Each fiber is an ordinary
conjugacy class.  Its cardinality cancels the centralizer factor exactly,
leaving the cycle-block character sum with coefficient one.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16ConjugacyCompression

open HypercubicDimension16CompressionCensus
open HypercubicDimension16OrbitCharacter
open HypercubicDimension16CycleBlockDecoration
open HypercubicDimension16PermutationConjugacy
open HypercubicDimension16PermutationFixedSector
open HypercubicDimension16PartitionRepresentatives
open V14HypercubicFDCensus

/-! ## Standard partition fibers -/

/-- The ordinary cycle partition of a field permutation, transported from
the cardinality-indexed standard definition to the literal field count. -/
def permutationStandardPartition (fieldIndex : Fin 8)
    (rename : Equiv.Perm (Fin (fieldIndex.1 + 1))) :
    Nat.Partition (fieldIndex.1 + 1) where
  parts := rename.partition.parts
  parts_pos := rename.partition.parts_pos
  parts_sum := by simpa using rename.partition.parts_sum

theorem permutationStandardPartition_parts (fieldIndex : Fin 8)
    (rename : Equiv.Perm (Fin (fieldIndex.1 + 1))) :
    (permutationStandardPartition fieldIndex rename).parts =
      rename.partition.parts := by
  rfl

/-- The representative selected by the standard partition of a permutation
is conjugate to that permutation. -/
theorem listedRepresentative_isConj_permutation (fieldIndex : Fin 8)
    (rename : Equiv.Perm (Fin (fieldIndex.1 + 1))) :
    IsConj
      (listedCycleRepresentative fieldIndex
        (partitionTableEntry fieldIndex
          (permutationStandardPartition fieldIndex rename)))
      rename := by
  rw [Equiv.Perm.partition_eq_of_isConj]
  apply Nat.Partition.ext
  rw [listedCycleRepresentative_partition_parts_for_partition]
  exact permutationStandardPartition_parts fieldIndex rename

theorem permutationStandardPartition_eq_iff_isConj
    (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1))
    (rename : Equiv.Perm (Fin (fieldIndex.1 + 1))) :
    permutationStandardPartition fieldIndex rename = partition ↔
      IsConj
        (listedCycleRepresentative fieldIndex
          (partitionTableEntry fieldIndex partition))
        rename := by
  constructor
  · intro equality
    subst partition
    exact listedRepresentative_isConj_permutation fieldIndex rename
  · intro conjugate
    apply Nat.Partition.ext
    rw [permutationStandardPartition_parts]
    have partitionEquality :=
      Equiv.Perm.partition_eq_of_isConj.mp conjugate
    have partsEquality := congrArg Nat.Partition.parts partitionEquality
    rw [listedCycleRepresentative_partition_parts_for_partition] at partsEquality
    exact partsEquality.symm

/-- The fiber of the standard partition map is literally the corresponding
ordinary conjugacy class. -/
def partitionFiberEquivIsConj (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1)) :
    { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
        permutationStandardPartition fieldIndex rename = partition } ≃
      { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
        IsConj
          (listedCycleRepresentative fieldIndex
            (partitionTableEntry fieldIndex partition))
          rename } where
  toFun rename :=
    ⟨rename.1,
      (permutationStandardPartition_eq_iff_isConj
        fieldIndex partition rename.1).mp rename.2⟩
  invFun rename :=
    ⟨rename.1,
      (permutationStandardPartition_eq_iff_isConj
        fieldIndex partition rename.1).mpr rename.2⟩
  left_inv rename := by cases rename; rfl
  right_inv rename := by cases rename; rfl

theorem partitionFiber_card (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1)) :
    Fintype.card
        { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
          permutationStandardPartition fieldIndex rename = partition } =
      Nat.card
        { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
          IsConj
            (listedCycleRepresentative fieldIndex
              (partitionTableEntry fieldIndex partition))
            rename } := by
  letI := Fintype.ofFinite
    { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
      IsConj
        (listedCycleRepresentative fieldIndex
          (partitionTableEntry fieldIndex partition))
        rename }
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_congr (partitionFiberEquivIsConj fieldIndex partition)

/-! ## One conjugacy fiber -/

theorem conjugacyClassCard_mul_centralizerCard_eq_factorial
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (rename : Equiv.Perm Label) :
    Nat.card { other : Equiv.Perm Label // IsConj rename other } *
        Nat.card (Subgroup.centralizer
          ({rename} : Set (Equiv.Perm Label))) =
      Nat.factorial (Fintype.card Label) := by
  rw [Equiv.Perm.nat_card_centralizer]
  exact Equiv.Perm.card_isConj_mul_eq rename

theorem partitionFiber_decorationCharacter
    (h : Hypercubic4) (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1))
    (targetDegree : ℕ)
    (rename : Equiv.Perm (Fin (fieldIndex.1 + 1)))
    (fiberMembership :
      permutationStandardPartition fieldIndex rename = partition) :
    indexedDecorationCharacter h rename targetDegree targetDegree =
      partitionDerivativeCharacter h
        (partitionCanonicalList partition) targetDegree := by
  let representative :=
    listedCycleRepresentative fieldIndex
      (partitionTableEntry fieldIndex partition)
  have conjugate : IsConj representative rename :=
    (permutationStandardPartition_eq_iff_isConj
      fieldIndex partition rename).mp fiberMembership
  calc
    indexedDecorationCharacter h rename targetDegree targetDegree =
        indexedDecorationCharacter h representative targetDegree
          targetDegree :=
      (indexedDecorationCharacter_isConj h targetDegree targetDegree
        conjugate).symm
    _ = partitionDerivativeCharacter h
          (partitionTableEntry fieldIndex partition).1 targetDegree :=
      listedCycleRepresentative_decorationCharacter h fieldIndex
        (partitionTableEntry fieldIndex partition) targetDegree
    _ = partitionDerivativeCharacter h
          (partitionCanonicalList partition) targetDegree := rfl

theorem partitionFiber_centralizerCard
    (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1))
    (rename : Equiv.Perm (Fin (fieldIndex.1 + 1)))
    (fiberMembership :
      permutationStandardPartition fieldIndex rename = partition) :
    Nat.card (Subgroup.centralizer
        ({rename} : Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) =
      Nat.card (Subgroup.centralizer
        ({listedCycleRepresentative fieldIndex
            (partitionTableEntry fieldIndex partition)} :
          Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) := by
  exact natCardCentralizer_isConj
    ((permutationStandardPartition_eq_iff_isConj
      fieldIndex partition rename).mp fiberMembership).symm

theorem partitionFiber_sum_eq_factorial_mul_character
    (h : Hypercubic4) (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1))
    (targetDegree : ℕ) :
    (∑ rename :
        { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
          permutationStandardPartition fieldIndex rename = partition },
      (Nat.card (Subgroup.centralizer
        ({rename.1} : Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
        indexedDecorationCharacter h rename.1 targetDegree targetDegree) =
      (Nat.factorial (fieldIndex.1 + 1) : ℚ) *
        partitionDerivativeCharacter h
          (partitionCanonicalList partition) targetDegree := by
  let representative :=
    listedCycleRepresentative fieldIndex
      (partitionTableEntry fieldIndex partition)
  let character := partitionDerivativeCharacter h
    (partitionCanonicalList partition) targetDegree
  calc
    _ = ∑ _rename :
          { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
            permutationStandardPartition fieldIndex rename = partition },
          (Nat.card (Subgroup.centralizer
            ({representative} :
              Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
            character := by
        apply Finset.sum_congr rfl
        intro rename _
        rw [partitionFiber_centralizerCard fieldIndex partition rename.1
          rename.2]
        exact congrArg
          (fun value : ℚ =>
            (Nat.card (Subgroup.centralizer
              ({representative} :
                Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) * value)
          (partitionFiber_decorationCharacter h fieldIndex partition
            targetDegree rename.1 rename.2)
    _ = (Fintype.card
          { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
            permutationStandardPartition fieldIndex rename = partition } : ℚ) *
          ((Nat.card (Subgroup.centralizer
            ({representative} :
              Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
            character) := by simp
    _ = (Nat.card
          { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
            IsConj representative rename } : ℚ) *
          ((Nat.card (Subgroup.centralizer
            ({representative} :
              Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
            character) := by
        rw [partitionFiber_card fieldIndex partition]
    _ = (Nat.factorial (fieldIndex.1 + 1) : ℚ) * character := by
        rw [← mul_assoc, ← Nat.cast_mul,
          conjugacyClassCard_mul_centralizerCard_eq_factorial representative,
          Fintype.card_fin]
    _ = _ := rfl

/-! ## Full compression and cancellation -/

theorem standardPartitionSum_eq_listedPartitionSum
    (h : Hypercubic4) (fieldIndex : Fin 8) (targetDegree : ℕ) :
    (∑ partition : Nat.Partition (fieldIndex.1 + 1),
      partitionDerivativeCharacter h
        (partitionCanonicalList partition) targetDegree) =
      ∑ parts ∈ (fieldPartitions (fieldIndex.1 + 1)).toFinset,
        partitionDerivativeCharacter h parts targetDegree := by
  rw [fieldPartitions_eq_partitionImage]
  rw [Finset.sum_image]
  exact partitionCanonicalList_injective.injOn

theorem labeledBurnsideNumerator_eq_factorial_mul_listedPartitionSum
    (h : Hypercubic4) (fieldIndex : Fin 8) (targetDegree : ℕ) :
    labeledBurnsideNumerator h (fieldIndex.1 + 1) targetDegree =
      (Nat.factorial (fieldIndex.1 + 1) : ℚ) *
        (∑ parts ∈ (fieldPartitions (fieldIndex.1 + 1)).toFinset,
          partitionDerivativeCharacter h parts targetDegree) := by
  rw [labeledBurnsideNumerator_eq_sum_centralizer_mul_decoration]
  calc
    (∑ rename : Equiv.Perm (Fin (fieldIndex.1 + 1)),
        (Nat.card (Subgroup.centralizer
          ({rename} : Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
          indexedDecorationCharacter h rename targetDegree targetDegree) =
      ∑ partition : Nat.Partition (fieldIndex.1 + 1),
        ∑ rename :
            { rename : Equiv.Perm (Fin (fieldIndex.1 + 1)) //
              permutationStandardPartition fieldIndex rename = partition },
          (Nat.card (Subgroup.centralizer
            ({rename.1} : Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
            indexedDecorationCharacter h rename.1 targetDegree targetDegree := by
        exact (Fintype.sum_fiberwise
          (permutationStandardPartition fieldIndex)
          (fun rename =>
            (Nat.card (Subgroup.centralizer
              ({rename} : Set (Equiv.Perm (Fin (fieldIndex.1 + 1))))) : ℚ) *
              indexedDecorationCharacter h rename targetDegree
                targetDegree)).symm
    _ = ∑ partition : Nat.Partition (fieldIndex.1 + 1),
          (Nat.factorial (fieldIndex.1 + 1) : ℚ) *
            partitionDerivativeCharacter h
              (partitionCanonicalList partition) targetDegree := by
        apply Finset.sum_congr rfl
        intro partition _
        exact partitionFiber_sum_eq_factorial_mul_character
          h fieldIndex partition targetDegree
    _ = (Nat.factorial (fieldIndex.1 + 1) : ℚ) *
          (∑ partition : Nat.Partition (fieldIndex.1 + 1),
            partitionDerivativeCharacter h
              (partitionCanonicalList partition) targetDegree) := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [standardPartitionSum_eq_listedPartitionSum]

/-- The honest labeled numerator is exactly the factorial multiple of the
previously displayed dimension-sixteen compressed sector character. -/
theorem labeledBurnsideNumerator_eq_factorial_mul_compressedSectorCharacter
    (h : Hypercubic4) (fieldIndex : Fin 8) :
    labeledBurnsideNumerator h (fieldIndex.1 + 1)
        (derivativeCountForFields (fieldIndex.1 + 1)) =
      (Nat.factorial (fieldIndex.1 + 1) : ℚ) *
        compressedSectorCharacter h (fieldIndex.1 + 1) := by
  rw [labeledBurnsideNumerator_eq_factorial_mul_listedPartitionSum]
  rfl

/-- Exact character identity between the honest orbit carrier and the
cycle-partition compression, for every nonempty field sector through eight
fields at engineering dimension sixteen. -/
theorem actualOrbitCharacter_eq_compressedSectorCharacter
    (h : Hypercubic4) (fieldIndex : Fin 8) :
    actualOrbitCharacter h (fieldIndex.1 + 1)
        (derivativeCountForFields (fieldIndex.1 + 1)) =
      compressedSectorCharacter h (fieldIndex.1 + 1) := by
  have honestEquality :=
    labeledBurnsideNumerator_eq_factorial_mul_actualOrbitCharacter h
      (fieldIndex.1 + 1)
      (derivativeCountForFields (fieldIndex.1 + 1))
  have compressedEquality :=
    labeledBurnsideNumerator_eq_factorial_mul_compressedSectorCharacter
      h fieldIndex
  have factorialPositive :
      (0 : ℚ) < Nat.factorial (fieldIndex.1 + 1) := by positivity
  rw [compressedEquality] at honestEquality
  nlinarith

end HypercubicDimension16ConjugacyCompression
end YangMills
end QuantumTheory
end Mettapedia
