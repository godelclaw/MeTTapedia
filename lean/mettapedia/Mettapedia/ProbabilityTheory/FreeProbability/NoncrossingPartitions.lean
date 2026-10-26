import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic

/-!
# Canonical noncrossing partitions of ordered positions

Blocks form a finite set, so their presentation order and repetitions carry no data.
Positions inside a block retain the order inherited from `Fin n`. The computable
catalogue below uses canonical labelings, so each partition appears once. Its completeness
is proved, rather than inferred from a small list's length.

The refinement order is Mathlib's partition order. Only the small Catalan counts below
are established here; no general counting theorem or noncrossing lattice is asserted.
See Nica and Speicher, *Lectures on the Combinatorics of Free Probability*, Chapter 9:
https://rolandspeicher.com/wp-content/uploads/2020/06/nica-speicher-book.pdf
-/

namespace Mettapedia.ProbabilityTheory.FreeProbability
open Finset

/-- Partitions with disjoint, nonempty blocks covering every argument position. -/
abbrev Partition (n : ℕ) := Finpartition (univ : Finset (Fin n))

/-- Interlaced pairs in blocks must belong to the same block. -/
def Partition.isNoncrossing {n : ℕ} (P : Partition n) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    P.part a = P.part c → P.part b = P.part d → P.part a = P.part b

instance {n : ℕ} (P : Partition n) : Decidable P.isNoncrossing :=
  inferInstanceAs (Decidable (∀ a b c d : Fin n, a < b → b < c → c < d →
    P.part a = P.part c → P.part b = P.part d → P.part a = P.part b))

/-- Noncrossing partitions; argument positions, rather than variable values, are partitioned. -/
abbrev NC (n : ℕ) := {P : Partition n // P.isNoncrossing}

@[ext] theorem Partition.ext_part {n : ℕ} {P Q : Partition n}
    (h : ∀ i, P.part i = Q.part i) : P = Q := by
  apply Finpartition.ext
  ext B
  constructor <;> intro hB
  · obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB hi, h i]
    exact Q.part_mem.mpr (mem_univ i)
  · obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hB
    rw [← Q.part_eq_of_mem hB hi, ← h i]
    exact P.part_mem.mpr (mem_univ i)

instance {n : ℕ} (f : Fin n → Fin n) : DecidableRel (Setoid.ker f).r :=
  fun i j => inferInstanceAs (Decidable (f i = f j))

/-- The labeling presentation identifies exactly positions with equal labels. -/
def partitionOfLabels {n : ℕ} (f : Fin n → Fin n) : Partition n :=
  Finpartition.ofSetoid (Setoid.ker f)

@[simp] theorem mem_part_labels {n : ℕ} (f : Fin n → Fin n) (i j : Fin n) :
    j ∈ (partitionOfLabels f).part i ↔ f i = f j :=
  Finpartition.mem_part_ofSetoid_iff_rel

/-- A canonical label: the least position of the containing block. -/
def Partition.label {n : ℕ} (P : Partition n) (i : Fin n) : Fin n :=
  (P.part i).min' (P.part_nonempty.mpr (mem_univ i))

theorem Partition.label_eq_iff {n : ℕ} (P : Partition n) (i j : Fin n) :
    P.label i = P.label j ↔ P.part i = P.part j := by
  constructor
  · intro h
    have hi : P.label i ∈ P.part i := min'_mem _ _
    have hj : P.label j ∈ P.part j := min'_mem _ _
    exact P.eq_of_mem_parts (P.part_mem.mpr (mem_univ i))
      (P.part_mem.mpr (mem_univ j)) (h ▸ hi) hj
  · intro h
    simp only [Partition.label, h]

@[simp] theorem partitionOfLabels_label {n : ℕ} (P : Partition n) :
    partitionOfLabels P.label = P := by
  apply Partition.ext_part
  intro i
  ext j
  rw [mem_part_labels, P.label_eq_iff,
    P.mem_part_iff_part_eq_part (mem_univ j) (mem_univ i), eq_comm]

/-- Least-block labels decrease positions and are idempotent. -/
theorem Partition.label_laws {n : ℕ} (P : Partition n) (i : Fin n) :
    P.label i ≤ i ∧ P.label (P.label i) = P.label i := by
  refine ⟨min'_le _ _ (P.mem_part (mem_univ i)), ?_⟩
  apply (P.label_eq_iff _ _).mpr
  exact P.part_eq_of_mem (P.part_mem.mpr (mem_univ i)) (min'_mem _ _)

/-- Canonical labels are chosen from initial intervals: only `n!` candidates. -/
def canonicalLabels (n : ℕ) : Finset (Fin n → Fin n) :=
  (Fintype.piFinset (fun i : Fin n => Iic i)).filter (fun f => ∀ i, f (f i) = f i)

@[simp] theorem Partition.label_mem {n : ℕ} (P : Partition n) :
    P.label ∈ canonicalLabels n :=
  mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => mem_Iic.mpr (P.label_laws i).1),
    fun i => (P.label_laws i).2⟩

theorem label_partitionOfLabels {n : ℕ} {f : Fin n → Fin n}
    (hf : f ∈ canonicalLabels n) (i : Fin n) : (partitionOfLabels f).label i = f i := by
  obtain ⟨hf, hid⟩ := mem_filter.mp hf
  have hle := fun j => mem_Iic.mp (Fintype.mem_piFinset.mp hf j)
  apply le_antisymm
  · exact min'_le _ _ ((mem_part_labels f i (f i)).mpr (hid i).symm)
  · apply le_trans ?_ (hle _)
    exact le_of_eq ((mem_part_labels f i _).mp (min'_mem _ _))

/-- Canonical labelings are injective, allowing enumeration without duplicate comparisons. -/
def labelEmbedding {n : ℕ} (s : Finset (Fin n → Fin n)) (hs : s ⊆ canonicalLabels n) :
    s ↪ Partition n where
  toFun f := partitionOfLabels f.val
  inj' f g h := by
    apply Subtype.ext
    funext i
    simpa only [label_partitionOfLabels (hs f.property),
      label_partitionOfLabels (hs g.property)] using congrArg (fun P : Partition n => P.label i) h

/-- Complete partition catalogue, with block presentation order removed. -/
def allPartitions (n : ℕ) : Finset (Partition n) :=
  (canonicalLabels n).attach.map (labelEmbedding _ Subset.rfl)

@[simp] theorem mem_allPartitions {n : ℕ} (P : Partition n) : P ∈ allPartitions n :=
  mem_map.mpr ⟨⟨P.label, P.label_mem⟩, mem_attach _ _, partitionOfLabels_label P⟩

/-- Noncrossing is checked on labels before constructing blocks. -/
def labelsNoncrossing {n : ℕ} (f : Fin n → Fin n) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    f a = f c → f b = f d → f a = f b

instance {n : ℕ} (f : Fin n → Fin n) : Decidable (labelsNoncrossing f) :=
  inferInstanceAs (Decidable (∀ a b c d : Fin n, a < b → b < c → c < d →
    f a = f c → f b = f d → f a = f b))

@[simp] theorem part_labels_eq {n : ℕ} (f : Fin n → Fin n) (i j : Fin n) :
    (partitionOfLabels f).part i = (partitionOfLabels f).part j ↔ f i = f j := by
  rw [← (partitionOfLabels f).mem_part_iff_part_eq_part (mem_univ i) (mem_univ j),
    mem_part_labels, eq_comm]

@[simp] theorem labelsNoncrossing_iff {n : ℕ} (f : Fin n → Fin n) :
    (partitionOfLabels f).isNoncrossing ↔ labelsNoncrossing f := by
  simp only [Partition.isNoncrossing, labelsNoncrossing, part_labels_eq]

/-- Complete, duplicate-free noncrossing catalogue. -/
def noncrossingPartitions (n : ℕ) : Finset (Partition n) :=
  ((canonicalLabels n).filter labelsNoncrossing).attach.map
    (labelEmbedding _ (filter_subset _ _))

@[simp] theorem mem_noncrossingPartitions {n : ℕ} (P : Partition n) :
    P ∈ noncrossingPartitions n ↔ P.isNoncrossing := by
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := mem_map.mp h
    exact (labelsNoncrossing_iff f.val).mpr (mem_filter.mp f.property).2
  · intro h
    have hf : P.label ∈ (canonicalLabels n).filter labelsNoncrossing := by
      refine mem_filter.mpr ⟨P.label_mem, ?_⟩
      simpa only [← labelsNoncrossing_iff, partitionOfLabels_label] using h
    exact mem_map.mpr ⟨⟨P.label, hf⟩, mem_attach _ _, partitionOfLabels_label P⟩

instance (n : ℕ) : Fintype (NC n) :=
  Fintype.subtype (noncrossingPartitions n) mem_noncrossingPartitions

theorem top_noncrossing (n : ℕ) : (⊤ : Partition n).isNoncrossing := by
  intro a b _ _ _ _ _ _ _
  exact (Finpartition.parts_top_subsingleton _)
    ((⊤ : Partition n).part_mem.mpr (mem_univ a))
    ((⊤ : Partition n).part_mem.mpr (mem_univ b))

@[simp] theorem top_parts {n : ℕ} (hn : 0 < n) :
    (⊤ : Partition n).parts = {univ} := by
  apply subset_antisymm (Finpartition.parts_top_subset _)
  intro B hB
  obtain rfl := mem_singleton.mp hB
  obtain ⟨C, hC, _⟩ := (⊤ : Partition n).exists_mem (mem_univ (⟨0, hn⟩ : Fin n))
  simpa [mem_singleton.mp (Finpartition.parts_top_subset _ hC)] using hC

/-- Diagrams other than the one-block partition. -/
def properNoncrossingPartitions (n : ℕ) : Finset (Partition n) :=
  (noncrossingPartitions n).erase ⊤

/-- All proper partitions use strictly smaller arities in every block. -/
theorem Partition.card_lt {n : ℕ} (P : Partition n) (hP : P ≠ ⊤)
    {B : Finset (Fin n)} (hB : B ∈ P.parts) : B.card < n := by
  have hle : B ⊆ univ := subset_univ _
  have hne : B ≠ univ := by
    intro h
    apply hP
    apply le_antisymm le_top
    intro C hC
    have hC' : C = univ := mem_singleton.mp (Finpartition.parts_top_subset _ hC)
    exact ⟨B, hB, hC' ▸ h ▸ Subset.rfl⟩
  simpa using card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hle, hne⟩)

/-- Structural enumeration of block positions, without invoking a sorting algorithm. -/
def blockList {n : ℕ} (B : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun i => i ∈ B)

theorem blockList_length {n : ℕ} (B : Finset (Fin n)) : (blockList B).length = B.card := by
  have h : (blockList B).toFinset = B := by ext i; simp [blockList]
  calc
    _ = (blockList B).toFinset.card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)).symm
    _ = _ := congrArg Finset.card h

/-- Increasing enumeration of one block; its implementation scans the ambient order. -/
def blockPosition {n : ℕ} (B : Finset (Fin n)) : Fin B.card ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i => (blockList B).get (Fin.cast (blockList_length B).symm i))
    ((((List.pairwise_lt_finRange n).filter _).sortedLT.strictMono_get).comp
      (Fin.cast_strictMono _))

@[simp] theorem blockPosition_mem {n : ℕ} (B : Finset (Fin n)) (i : Fin B.card) :
    blockPosition B i ∈ B := by
  change (blockList B).get (Fin.cast (blockList_length B).symm i) ∈ B
  have h := List.get_mem (blockList B) (Fin.cast (blockList_length B).symm i)
  simpa only [blockList, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    using h

/-- The structural enumeration agrees with Mathlib's independently defined order embedding. -/
theorem blockPosition_eq_orderEmb {n : ℕ} (B : Finset (Fin n)) :
    blockPosition B = B.orderEmbOfFin rfl :=
  Finset.orderEmbOfFin_unique' rfl (fun i => blockPosition_mem B i)

@[simp] theorem blockPosition_univ {n : ℕ} (i : Fin (univ : Finset (Fin n)).card) :
    blockPosition univ i = Fin.cast (by simp) i := by
  rw [blockPosition_eq_orderEmb]
  have h := Finset.orderEmbOfFin_unique (s := (univ : Finset (Fin n))) (by simp)
    (f := fun j : Fin n => j) (fun _ => mem_univ _) (fun _ _ h => h)
  have hi := (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff
    (s := (univ : Finset (Fin n))) (h := rfl) (h' := by simp)
    (i := i) (j := Fin.cast (by simp) i)).mpr rfl
  exact hi.trans (congrFun h (Fin.cast (by simp) i)).symm

/-- Every original position occurs in exactly one block, at its ordered local index. -/
def Partition.coordinates {n : ℕ} (P : Partition n) :
    (Σ B : P.parts, Fin B.val.card) ≃ Fin n :=
  (Equiv.sigmaCongrRight (fun B : P.parts => (B.val.orderIsoOfFin rfl).toEquiv)).trans
    (P.equivSigmaParts.symm.trans (Equiv.subtypeUnivEquiv (fun _ => mem_univ _)))

@[simp] theorem Partition.coordinates_apply {n : ℕ} (P : Partition n)
    (B : P.parts) (i : Fin B.val.card) :
    P.coordinates ⟨B, i⟩ = blockPosition B.val i := by
  rw [blockPosition_eq_orderEmb]
  rfl

/-- Block sizes retain multiplicity; a shape forgets positions and is for diagonal queries only. -/
def properShapes (n : ℕ) : Multiset (Multiset ℕ) :=
  (properNoncrossingPartitions n).val.map (fun P => P.parts.val.map Finset.card)

/-- Complete shape histograms, not a list of selected example diagrams. -/
theorem properShapes_small :
    properShapes 1 = 0 ∧
    properShapes 2 = {{1, 1}} ∧
    properShapes 3 = {{1, 1, 1}} + Multiset.replicate 3 {2, 1} ∧
    properShapes 4 = {{1, 1, 1, 1}} + Multiset.replicate 6 {2, 1, 1} +
      Multiset.replicate 2 {2, 2} + Multiset.replicate 4 {3, 1} ∧
    properShapes 5 = {{1, 1, 1, 1, 1}} + Multiset.replicate 10 {2, 1, 1, 1} +
      Multiset.replicate 10 {2, 2, 1} + Multiset.replicate 10 {3, 1, 1} +
      Multiset.replicate 5 {3, 2} + Multiset.replicate 5 {4, 1} ∧
    properShapes 6 = {{1, 1, 1, 1, 1, 1}} + Multiset.replicate 15 {2, 1, 1, 1, 1} +
      Multiset.replicate 30 {2, 2, 1, 1} + Multiset.replicate 5 {2, 2, 2} +
      Multiset.replicate 20 {3, 1, 1, 1} + Multiset.replicate 30 {3, 2, 1} +
      Multiset.replicate 3 {3, 3} + Multiset.replicate 15 {4, 1, 1} +
      Multiset.replicate 6 {4, 2} + Multiset.replicate 6 {5, 1} := by
  decide +kernel

/-- Catalan numbers reuse Mathlib's recurrence. -/
abbrev catalanNumber := catalan

/-- These count a proved complete catalogue, including the empty partition. -/
theorem noncrossing_card_small :
    (noncrossingPartitions 0).card = 1 ∧
    (noncrossingPartitions 1).card = 1 ∧
    (noncrossingPartitions 2).card = 2 ∧
    (noncrossingPartitions 3).card = 5 ∧
    (noncrossingPartitions 4).card = 14 := by
  decide +kernel

end Mettapedia.ProbabilityTheory.FreeProbability
