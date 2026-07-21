import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PermutationConjugacy
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Canonical cycle-block representatives of integer partitions

The explicit partition lists through eight fields are identified with the
standard finite type of integer partitions.  Every listed partition is
realized by a concrete block rotation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PartitionRepresentatives

open HypercubicDimension16CompressionCensus
open HypercubicDimension16CycleBlockDecoration
open HypercubicDimension16PermutationDecorationTransport
open V14HypercubicFDCensus

/-- Descending list attached canonically to a standard integer partition. -/
def partitionCanonicalList {n : ℕ} (partition : Nat.Partition n) : List ℕ :=
  partition.parts.sort (fun left right => right ≤ left)

theorem partitionCanonicalList_sum {n : ℕ}
    (partition : Nat.Partition n) :
    (partitionCanonicalList partition).sum = n := by
  rw [partitionCanonicalList, ← Multiset.sum_coe, Multiset.sort_eq]
  exact partition.parts_sum

theorem partitionCanonicalList_coe {n : ℕ}
    (partition : Nat.Partition n) :
    (partitionCanonicalList partition : Multiset ℕ) = partition.parts := by
  simp [partitionCanonicalList]

theorem partitionCanonicalList_positive {n : ℕ}
    (partition : Nat.Partition n) :
    ∀ part ∈ partitionCanonicalList partition, 0 < part := by
  intro part membership
  apply partition.parts_pos
  simpa [partitionCanonicalList] using membership

theorem partitionCanonicalList_injective {n : ℕ} :
    Function.Injective
      (partitionCanonicalList : Nat.Partition n → List ℕ) := by
  intro left right equality
  apply Nat.Partition.ext
  have multisetEquality := congrArg
    (fun parts : List ℕ => (parts : Multiset ℕ)) equality
  simpa [partitionCanonicalList] using multisetEquality

def compositionCanonicalList {n : ℕ}
    (composition : Composition n) : List ℕ :=
  composition.blocks.insertionSort (fun left right => right ≤ left)

theorem compositionCanonicalList_eq_partitionCanonicalList {n : ℕ}
    (composition : Composition n) :
    compositionCanonicalList composition =
      partitionCanonicalList (Nat.Partition.ofComposition n composition) := by
  simp [compositionCanonicalList, partitionCanonicalList,
    Nat.Partition.ofComposition, List.mergeSort_eq_insertionSort]

/-- The two extensions of a positive composition whose total is increased
by one: increase its first part, or insert a new leading one. -/
def compositionListSuccessors : List ℕ → List (List ℕ)
  | [] => [[1]]
  | first :: rest => [(first + 1) :: rest, 1 :: first :: rest]

/-- Transparent recursive enumeration of all positive ordered compositions.
Unlike the standard `Fintype` instance, this definition is intended for
small kernel-replayed certificates. -/
def positiveCompositionLists : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (positiveCompositionLists n).flatMap compositionListSuccessors

theorem mem_positiveCompositionLists_iff {n : ℕ} {parts : List ℕ} :
    parts ∈ positiveCompositionLists n ↔
      (∀ part ∈ parts, 0 < part) ∧ parts.sum = n := by
  induction n generalizing parts with
  | zero =>
      constructor
      · intro membership
        simp [positiveCompositionLists] at membership
        subst parts
        simp
      · rintro ⟨positivity, total⟩
        rcases parts with _ | ⟨first, rest⟩
        · simp [positiveCompositionLists]
        · have firstPositive := positivity first (by simp)
          simp at total
          omega
  | succ n inductionHypothesis =>
      constructor
      · intro membership
        rw [positiveCompositionLists, List.mem_flatMap] at membership
        obtain ⟨previous, previousMembership, successorMembership⟩ := membership
        have previousProperties := inductionHypothesis.mp previousMembership
        rcases previous with _ | ⟨first, rest⟩
        · simp [compositionListSuccessors] at successorMembership
          subst parts
          constructor
          · simp
          · simp at previousProperties ⊢
            omega
        · simp [compositionListSuccessors] at successorMembership
          rcases successorMembership with rfl | rfl
          ·
            constructor
            · intro part partMembership
              simp only [List.mem_cons] at partMembership
              rcases partMembership with rfl | partMembership
              · omega
              · exact previousProperties.1 part (by simp [partMembership])
            · simp only [List.sum_cons] at previousProperties ⊢
              omega
          ·
            constructor
            · intro part partMembership
              simp only [List.mem_cons] at partMembership
              rcases partMembership with rfl | partMembership
              · omega
              · exact previousProperties.1 part (by simp [partMembership])
            · simp only [List.sum_cons] at previousProperties ⊢
              omega
      · rintro ⟨positivity, total⟩
        rcases parts with _ | ⟨first, rest⟩
        · simp at total
        · have firstPositive : 0 < first := positivity first (by simp)
          rcases first with _ | first
          · omega
          · rcases first with _ | first
            · have restTotal : rest.sum = n := by
                simp only [List.sum_cons] at total
                omega
              have restPositive : ∀ part ∈ rest, 0 < part := by
                intro part partMembership
                exact positivity part (by simp [partMembership])
              have restMembership := inductionHypothesis.mpr
                ⟨restPositive, restTotal⟩
              rw [positiveCompositionLists, List.mem_flatMap]
              refine ⟨rest, restMembership, ?_⟩
              rcases rest with _ | ⟨next, tail⟩ <;>
                simp [compositionListSuccessors]
            · let previous := (first + 1) :: rest
              simp only [List.sum_cons] at total
              have previousTotal : previous.sum = n := by
                dsimp [previous]
                omega
              have previousPositive : ∀ part ∈ previous, 0 < part := by
                intro part partMembership
                simp only [previous, List.mem_cons] at partMembership
                rcases partMembership with rfl | partMembership
                · omega
                · exact positivity part (by simp [partMembership])
              have previousMembership := inductionHypothesis.mpr
                ⟨previousPositive, previousTotal⟩
              rw [positiveCompositionLists, List.mem_flatMap]
              refine ⟨previous, previousMembership, ?_⟩
              simp [previous, compositionListSuccessors]

def canonicalizeCompositionList (parts : List ℕ) : List ℕ :=
  parts.insertionSort (fun left right => right ≤ left)

theorem compositionCanonicalList_eq_canonicalize {n : ℕ}
    (composition : Composition n) :
    compositionCanonicalList composition =
      canonicalizeCompositionList composition.blocks := by
  rfl

/- Small kernel-replayed certificate on the transparent composition
enumeration. -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem fieldPartitions_eq_generatedImage (fieldIndex : Fin 8) :
    (fieldPartitions (fieldIndex.1 + 1)).toFinset =
      (positiveCompositionLists (fieldIndex.1 + 1)).toFinset.image
        canonicalizeCompositionList := by
  fin_cases fieldIndex <;>
    norm_num (config := { maxSteps := 1000000 })
      [fieldPartitions, positiveCompositionLists,
        compositionListSuccessors, canonicalizeCompositionList,
        List.insertionSort, List.orderedInsert] <;> decide

/-- Exact identification of the hand-written lists with the standard integer
partitions through eight fields. -/
theorem fieldPartitions_eq_partitionImage (fieldIndex : Fin 8) :
    (fieldPartitions (fieldIndex.1 + 1)).toFinset =
      (Finset.univ : Finset (Nat.Partition (fieldIndex.1 + 1))).image
        partitionCanonicalList := by
  rw [fieldPartitions_eq_generatedImage]
  ext parts
  constructor
  · intro membership
    rcases Finset.mem_image.mp membership with
      ⟨compositionParts, compositionMembership, rfl⟩
    have compositionProperties := mem_positiveCompositionLists_iff.mp
      (List.mem_toFinset.mp compositionMembership)
    let composition : Composition (fieldIndex.1 + 1) :=
      ⟨compositionParts, (fun {_} membership =>
        compositionProperties.1 _ membership), compositionProperties.2⟩
    apply Finset.mem_image.mpr
    refine ⟨Nat.Partition.ofComposition _ composition, Finset.mem_univ _, ?_⟩
    change partitionCanonicalList
      (Nat.Partition.ofComposition _ composition) =
        canonicalizeCompositionList composition.blocks
    rw [← compositionCanonicalList_eq_canonicalize,
      compositionCanonicalList_eq_partitionCanonicalList]
  · intro membership
    rcases Finset.mem_image.mp membership with
      ⟨partition, _, rfl⟩
    obtain ⟨composition, compositionEquality⟩ :=
      Nat.Partition.ofComposition_surj partition
    apply Finset.mem_image.mpr
    refine ⟨composition.blocks, List.mem_toFinset.mpr ?_, ?_⟩
    · apply mem_positiveCompositionLists_iff.mpr
      exact ⟨(fun part membership => composition.blocks_pos membership),
        composition.blocks_sum⟩
    · rw [← compositionCanonicalList_eq_canonicalize,
        compositionCanonicalList_eq_partitionCanonicalList,
        compositionEquality]

/-! ## Cycle structure under finite relabelling and disjoint sums -/

theorem isCycle_permCongr
    {Source Target : Type*}
    (labelEquiv : Source ≃ Target) {rename : Equiv.Perm Source}
    (cycle : rename.IsCycle) :
    (labelEquiv.permCongr rename).IsCycle := by
  let fullRangeEquiv : Source ≃ {target : Target // target ∈ Set.univ} :=
    labelEquiv.trans (Equiv.Set.univ Target).symm
  have extensionEquality :
      rename.extendDomain fullRangeEquiv =
        labelEquiv.permCongr rename := by
    ext target
    rw [Equiv.Perm.extendDomain_apply_subtype _ _ (Set.mem_univ target)]
    simp [fullRangeEquiv]
  rw [← extensionEquality]
  exact cycle.extendDomain fullRangeEquiv

theorem disjoint_permCongr
    {Source Target : Type*}
    (labelEquiv : Source ≃ Target)
    {left right : Equiv.Perm Source}
    (disjoint : left.Disjoint right) :
    (labelEquiv.permCongr left).Disjoint
      (labelEquiv.permCongr right) := by
  intro target
  rcases disjoint (labelEquiv.symm target) with fixed | fixed
  · left
    simpa using congrArg labelEquiv fixed
  · right
    simpa using congrArg labelEquiv fixed

theorem card_support_permCongr
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (labelEquiv : Source ≃ Target) (rename : Equiv.Perm Source) :
    (labelEquiv.permCongr rename).support.card = rename.support.card := by
  let fullRangeEquiv : Source ≃ {target : Target // target ∈ Set.univ} :=
    labelEquiv.trans (Equiv.Set.univ Target).symm
  have extensionEquality :
      rename.extendDomain fullRangeEquiv =
        labelEquiv.permCongr rename := by
    ext target
    rw [Equiv.Perm.extendDomain_apply_subtype _ _ (Set.mem_univ target)]
    simp [fullRangeEquiv]
  rw [← extensionEquality]
  exact Equiv.Perm.card_support_extend_domain fullRangeEquiv

theorem cycleType_permCongr
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (labelEquiv : Source ≃ Target) (rename : Equiv.Perm Source) :
    (labelEquiv.permCongr rename).cycleType = rename.cycleType := by
  classical
  letI : LinearOrder Source :=
    LinearOrder.lift' (Fintype.equivFin Source)
      (Fintype.equivFin Source).injective
  let factors := (Equiv.Perm.cycleFactors rename).1
  have factorsProduct : factors.prod = rename :=
    (Equiv.Perm.cycleFactors rename).2.1
  have factorsCycles :
      ∀ factor ∈ factors, factor.IsCycle :=
    (Equiv.Perm.cycleFactors rename).2.2.1
  have factorsDisjoint : factors.Pairwise Equiv.Perm.Disjoint :=
    (Equiv.Perm.cycleFactors rename).2.2.2
  have transportedProduct :
      (factors.map labelEquiv.permCongr).prod =
        labelEquiv.permCongr rename := by
    change (factors.map (fun factor =>
      labelEquiv.permCongrHom factor)).prod =
        labelEquiv.permCongrHom rename
    rw [← map_list_prod labelEquiv.permCongrHom, factorsProduct]
  have transportedCycles :
      ∀ factor ∈ factors.map labelEquiv.permCongr,
        factor.IsCycle := by
    intro factor membership
    rcases List.mem_map.mp membership with ⟨sourceFactor, sourceMembership, rfl⟩
    exact isCycle_permCongr labelEquiv
      (factorsCycles sourceFactor sourceMembership)
  have transportedDisjoint :
      (factors.map labelEquiv.permCongr).Pairwise
        Equiv.Perm.Disjoint := by
    rw [List.pairwise_map]
    exact factorsDisjoint.imp fun disjoint =>
      disjoint_permCongr labelEquiv disjoint
  rw [Equiv.Perm.cycleType_eq
      (factors.map labelEquiv.permCongr) transportedProduct
      transportedCycles transportedDisjoint,
    Equiv.Perm.cycleType_eq factors factorsProduct factorsCycles
      factorsDisjoint]
  simp [List.map_map, Function.comp_def, card_support_permCongr]

theorem partition_parts_permCongr
    {Source Target : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Target] [DecidableEq Target]
    (labelEquiv : Source ≃ Target) (rename : Equiv.Perm Source) :
    (labelEquiv.permCongr rename).partition.parts =
      rename.partition.parts := by
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition,
    cycleType_permCongr labelEquiv rename,
    card_support_permCongr labelEquiv rename,
    Fintype.card_congr labelEquiv]

theorem partition_parts_instance_irrel
    {Label : Type*}
    (firstFintype secondFintype : Fintype Label)
    (firstDecidable secondDecidable : DecidableEq Label)
    (rename : Equiv.Perm Label) :
    (@Equiv.Perm.partition Label firstFintype firstDecidable rename).parts =
      (@Equiv.Perm.partition Label secondFintype secondDecidable rename).parts := by
  have fintypeEquality : firstFintype = secondFintype :=
    Subsingleton.elim _ _
  subst secondFintype
  have decidableEquality : firstDecidable = secondDecidable :=
    Subsingleton.elim _ _
  subst secondDecidable
  rfl

set_option maxHeartbeats 1000000 in
theorem cycleType_sumCongr
    {Left Right : Type*}
    [Fintype Left] [DecidableEq Left]
    [Fintype Right] [DecidableEq Right]
    (left : Equiv.Perm Left) (right : Equiv.Perm Right) :
    (Equiv.Perm.sumCongr left right).cycleType =
      left.cycleType + right.cycleType := by
  let leftEquiv :
      Left ≃ {label : Left ⊕ Right //
        label ∈ Set.range (Sum.inl : Left → Left ⊕ Right)} :=
    Equiv.ofInjective Sum.inl Sum.inl_injective
  let rightEquiv :
      Right ≃ {label : Left ⊕ Right //
        label ∈ Set.range (Sum.inr : Right → Left ⊕ Right)} :=
    Equiv.ofInjective Sum.inr Sum.inr_injective
  have leftEquality :
      Equiv.Perm.sumCongr left 1 =
        left.extendDomain leftEquiv := by
    ext label
    rcases label with label | label
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _
        (show Sum.inl label ∈ Set.range
          (Sum.inl : Left → Left ⊕ Right) from ⟨label, rfl⟩)]
      simp [leftEquiv]
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _
        (show Sum.inr label ∉ Set.range
          (Sum.inl : Left → Left ⊕ Right) by simp)]
      rfl
  have rightEquality :
      Equiv.Perm.sumCongr 1 right =
        right.extendDomain rightEquiv := by
    ext label
    rcases label with label | label
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _
        (show Sum.inl label ∉ Set.range
          (Sum.inr : Right → Left ⊕ Right) by simp)]
      rfl
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _
        (show Sum.inr label ∈ Set.range
          (Sum.inr : Right → Left ⊕ Right) from ⟨label, rfl⟩)]
      simp [rightEquiv]
  have leftCycleType :
      (Equiv.Perm.sumCongr left (1 : Equiv.Perm Right)).cycleType =
        left.cycleType := by
    rw [leftEquality]
    exact Equiv.Perm.cycleType_extendDomain leftEquiv
  have rightCycleType :
      (Equiv.Perm.sumCongr (1 : Equiv.Perm Left) right).cycleType =
        right.cycleType := by
    rw [rightEquality]
    exact Equiv.Perm.cycleType_extendDomain rightEquiv
  have disjoint :
      (Equiv.Perm.sumCongr left (1 : Equiv.Perm Right)).Disjoint
        (Equiv.Perm.sumCongr (1 : Equiv.Perm Left) right) := by
    intro label
    rcases label with label | label
    · exact Or.inr rfl
    · exact Or.inl rfl
  rw [← leftCycleType, ← rightCycleType,
    ← disjoint.cycleType_mul, Equiv.Perm.sumCongr_mul]
  simp

set_option maxHeartbeats 1000000 in
theorem partition_parts_sumCongr
    {Left Right : Type*}
    [Fintype Left] [DecidableEq Left]
    [Fintype Right] [DecidableEq Right]
    (left : Equiv.Perm Left) (right : Equiv.Perm Right) :
    (Equiv.Perm.sumCongr left right).partition.parts =
      left.partition.parts + right.partition.parts := by
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition,
    Equiv.Perm.parts_partition, cycleType_sumCongr]
  rw [← Equiv.Perm.sum_cycleType, ← Equiv.Perm.sum_cycleType,
    ← Equiv.Perm.sum_cycleType]
  rw [cycleType_sumCongr, Multiset.sum_add]
  have leftBound := left.sum_cycleType_le
  have rightBound := right.sum_cycleType_le
  have subtraction :
      Fintype.card (Left ⊕ Right) -
          (left.cycleType.sum + right.cycleType.sum) =
        (Fintype.card Left - left.cycleType.sum) +
          (Fintype.card Right - right.cycleType.sum) := by
    simp only [Fintype.card_sum]
    omega
  rw [subtraction, Multiset.replicate_add]
  ac_rfl

/-! ## Concrete finite-label representatives -/

def cycleBlockFinEquiv :
    (parts : List ℕ) → CycleBlockLabel parts ≃ Fin parts.sum
  | [] => finZeroEquiv'.symm
  | _ :: rest =>
      (Equiv.sumCongr (Equiv.refl _) (cycleBlockFinEquiv rest)).trans
        finSumFinEquiv

/-- The displayed block rotation transported to the standard finite label
type of the same cardinality. -/
def cycleBlockFinRotation (parts : List ℕ) :
    Equiv.Perm (Fin parts.sum) :=
  (cycleBlockFinEquiv parts).permCongr (cycleBlockRotation parts)

theorem partition_parts_finRotate_of_pos {cycleLength : ℕ}
    (positive : 0 < cycleLength) :
    (finRotate cycleLength).partition.parts = {cycleLength} := by
  rcases cycleLength with _ | cyclePredecessor
  · omega
  rcases cyclePredecessor with _ | cyclePredecessor
  · simp [finRotate_one]
  · simp [Equiv.Perm.parts_partition,
      cycleType_finRotate, support_finRotate]

/-- The recursive disjoint rotation has exactly the displayed cycle
partition, including one-cycles as fixed points. -/
theorem cycleBlockRotation_partition_parts (parts : List ℕ)
    (positive : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    (cycleBlockRotation parts).partition.parts = (parts : Multiset ℕ) := by
  induction parts with
  | nil =>
      simp [cycleBlockRotation]
  | cons cycleLength rest inductionHypothesis =>
      have cyclePositive : 0 < cycleLength := positive _ (by simp)
      have restPositive : ∀ part ∈ rest, 0 < part := by
        intro part membership
        exact positive part (by simp [membership])
      have splitPartition :
          (cycleBlockRotation (cycleLength :: rest)).partition.parts =
            (finRotate cycleLength).partition.parts +
              (cycleBlockRotation rest).partition.parts := by
        let canonicalSumFintype :
            Fintype (Fin cycleLength ⊕ CycleBlockLabel rest) :=
          inferInstance
        let canonicalSumDecidable :
            DecidableEq (Fin cycleLength ⊕ CycleBlockLabel rest) :=
          inferInstance
        calc
          _ = (@Equiv.Perm.partition
                (Fin cycleLength ⊕ CycleBlockLabel rest)
                canonicalSumFintype canonicalSumDecidable
                (Equiv.Perm.sumCongr (finRotate cycleLength)
                  (cycleBlockRotation rest))).parts := by
              exact partition_parts_instance_irrel
                (cycleBlockLabelFintype (cycleLength :: rest))
                canonicalSumFintype
                (cycleBlockLabelDecidableEq (cycleLength :: rest))
                canonicalSumDecidable _
          _ = _ := by
              simpa only using
                partition_parts_sumCongr (finRotate cycleLength)
                  (cycleBlockRotation rest)
      rw [splitPartition,
        partition_parts_finRotate_of_pos cyclePositive,
        inductionHypothesis restPositive]
      rfl

theorem cycleBlockFinRotation_partition_parts (parts : List ℕ)
    (positive : ∀ cycleLength ∈ parts, 0 < cycleLength) :
    (cycleBlockFinRotation parts).partition.parts = (parts : Multiset ℕ) := by
  rw [cycleBlockFinRotation,
    partition_parts_permCongr,
    cycleBlockRotation_partition_parts parts positive]

abbrev ListedFieldPartition (fieldIndex : Fin 8) :=
  ↥(fieldPartitions (fieldIndex.1 + 1)).toFinset

/-- Every displayed list has the advertised total field count. -/
theorem listedFieldPartition_sum (fieldIndex : Fin 8) :
    ∀ entry : ListedFieldPartition fieldIndex,
      entry.1.sum = fieldIndex.1 + 1 := by
  fin_cases fieldIndex <;> decide

/-- Every displayed cycle length is positive. -/
theorem listedFieldPartition_positive (fieldIndex : Fin 8) :
    ∀ entry : ListedFieldPartition fieldIndex,
      ∀ part ∈ entry.1, 0 < part := by
  fin_cases fieldIndex <;> decide

theorem finCongr_permCongr_partition_parts
    {leftSize rightSize : ℕ} (sizeEquality : leftSize = rightSize)
    (rename : Equiv.Perm (Fin leftSize)) :
    ((finCongr sizeEquality).permCongr rename).partition.parts =
      rename.partition.parts := by
  subst rightSize
  rfl

/-- Concrete representative on the literal field-label type. -/
def listedCycleRepresentative (fieldIndex : Fin 8)
    (entry : ListedFieldPartition fieldIndex) :
    Equiv.Perm (Fin (fieldIndex.1 + 1)) :=
  (finCongr (listedFieldPartition_sum fieldIndex entry)).permCongr
    (cycleBlockFinRotation entry.1)

theorem listedCycleRepresentative_partition_parts (fieldIndex : Fin 8)
    (entry : ListedFieldPartition fieldIndex) :
    (listedCycleRepresentative fieldIndex entry).partition.parts =
      (entry.1 : Multiset ℕ) := by
  rw [listedCycleRepresentative, partition_parts_permCongr,
    cycleBlockFinRotation_partition_parts entry.1
      (listedFieldPartition_positive fieldIndex entry)]

/-- Canonical table entry selected by a standard integer partition. -/
def partitionTableEntry (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1)) :
    ListedFieldPartition fieldIndex :=
  ⟨partitionCanonicalList partition, by
    rw [fieldPartitions_eq_partitionImage]
    exact Finset.mem_image.mpr
      ⟨partition, Finset.mem_univ _, rfl⟩⟩

theorem listedCycleRepresentative_partition_parts_for_partition
    (fieldIndex : Fin 8)
    (partition : Nat.Partition (fieldIndex.1 + 1)) :
    (listedCycleRepresentative fieldIndex
      (partitionTableEntry fieldIndex partition)).partition.parts =
        partition.parts := by
  rw [listedCycleRepresentative_partition_parts]
  change (partitionCanonicalList partition : Multiset ℕ) = partition.parts
  exact partitionCanonicalList_coe partition

/-- The concrete listed representative carries the exact recursive
decoration character attached to its displayed partition. -/
theorem listedCycleRepresentative_decorationCharacter
    (h : Hypercubic4) (fieldIndex : Fin 8)
    (entry : ListedFieldPartition fieldIndex) (targetDegree : ℕ) :
    indexedDecorationCharacter h
        (listedCycleRepresentative fieldIndex entry)
        targetDegree targetDegree =
      partitionDerivativeCharacter h entry.1 targetDegree := by
  calc
    _ = indexedDecorationCharacter h (cycleBlockFinRotation entry.1)
          targetDegree targetDegree :=
      (indexedDecorationCharacter_permCongr
        (finCongr (listedFieldPartition_sum fieldIndex entry)) h
        (cycleBlockFinRotation entry.1) targetDegree targetDegree).symm
    _ = cycleBlockDecorationCharacter h entry.1
          targetDegree targetDegree :=
      (indexedDecorationCharacter_permCongr
        (cycleBlockFinEquiv entry.1) h (cycleBlockRotation entry.1)
        targetDegree targetDegree).symm
    _ = partitionDerivativeCharacter h entry.1 targetDegree :=
      cycleBlockDecorationCharacter_eq_partitionDerivativeCharacter
        h entry.1 targetDegree
        (listedFieldPartition_positive fieldIndex entry)

end HypercubicDimension16PartitionRepresentatives
end YangMills
end QuantumTheory
end Mettapedia
