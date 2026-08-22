import Mathlib.Order.Partition.Finpartition
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixSeamConnectivityFactor

/-!
# Lossless semantic compression of a literal hexagonal Cell profile

The finite one-Cell decoder stores a six-edge `CorridorCutProfile`.  Its raw
carrier treats each tracked-connectivity matrix as arbitrary Boolean data.
For a graph-derived Cell this is a large presentation redundancy: on the
positions carrying either color of a tracked pair, connectivity is an
equivalence relation, and all other entries are false.

This module replaces each such matrix by its finite partition of the tracked
positions.  It retains the complete proper six-color word and proves that the
code is lossless on the graph-semantic subset.  Every literal source Cell
supplies such a code.

This is a semantic compression of the local Cell letter, not a claim that the
three coarse slab orientations determine the transfer relation.  It does not
compose the separate boundary-rebase letter, measure a reachable closure,
derive `V0`, or verify the bounded base.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteHexCellProfileCompression

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24WindingClassification

/-- Canonical component labels are bounded by their position because each
label is the least member of its component. -/
abbrev CanonicalComponentLabels :=
  (position : Fin 6) → Fin (position.val + 1)

/-- A proper six-edge color word together with the canonical component label
of every position for each tracked color pair. -/
abbrev FiniteHexCellProfileCode :=
  {word : Fin 6 → StrandColor // IsProperCyclicColorWord word} ×
    (TrackedColorPair → CanonicalComponentLabels)

noncomputable instance : Fintype FiniteHexCellProfileCode := inferInstance
noncomputable instance : DecidableEq FiniteHexCellProfileCode :=
  Classical.decEq _

/-- The exact graph laws used by the partition code.  They are conclusions
for literal graph profiles, not extra assumptions on the source route. -/
structure IsGraphSemantic (profile : CorridorCutProfile 6 0 0) : Prop where
  proper : IsProperCyclicColorWord profile.edgeColor
  support : ∀ (pair : TrackedColorPair) (left right : Fin 6),
    profile.strandConnected pair (.inl left) (.inl right) = true →
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (profile.edgeColor left).toColor ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2 (profile.edgeColor right).toColor
  diagonal : ∀ (pair : TrackedColorPair) (position : Fin 6),
    profile.strandConnected pair (.inl position) (.inl position) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (profile.edgeColor position).toColor
  symmetric : ∀ (pair : TrackedColorPair) (left right : Fin 6),
    profile.strandConnected pair (.inl left) (.inl right) =
      profile.strandConnected pair (.inl right) (.inl left)
  transitive : ∀ (pair : TrackedColorPair) (left middle right : Fin 6),
    profile.strandConnected pair (.inl left) (.inl middle) = true →
    profile.strandConnected pair (.inl middle) (.inl right) = true →
    profile.strandConnected pair (.inl left) (.inl right) = true

/-- Complete the partial tracked relation to a setoid by making every
untracked position a singleton class. -/
def trackedSetoid (profile : CorridorCutProfile 6 0 0)
    (semantic : IsGraphSemantic profile) (pair : TrackedColorPair) :
    Setoid (Fin 6) where
  r left right := left = right ∨
    profile.strandConnected pair (.inl left) (.inl right) = true
  iseqv := {
    refl := fun position => Or.inl rfl
    symm := by
      intro left right hrelated
      rcases hrelated with hsame | hconnected
      · exact Or.inl hsame.symm
      · exact Or.inr (by
          rw [semantic.symmetric pair right left]
          exact hconnected)
    trans := by
      intro left middle right hleft hright
      rcases hleft with rfl | hleft
      · exact hright
      rcases hright with rfl | hright
      · exact Or.inr hleft
      · exact Or.inr (semantic.transitive pair left middle right hleft hright) }

/-- The finite partition induced by one semantic tracked relation. -/
noncomputable def trackedPartition (profile : CorridorCutProfile 6 0 0)
    (semantic : IsGraphSemantic profile) (pair : TrackedColorPair) :
    Finpartition (Finset.univ : Finset (Fin 6)) := by
  letI : DecidableRel (trackedSetoid profile semantic pair).r :=
    Classical.decRel _
  exact Finpartition.ofSetoid (trackedSetoid profile semantic pair)

@[simp]
theorem mem_trackedPartition_part_iff
    (profile : CorridorCutProfile 6 0 0)
    (semantic : IsGraphSemantic profile) (pair : TrackedColorPair)
    (left right : Fin 6) :
    right ∈ (trackedPartition profile semantic pair).part left ↔
      left = right ∨
        profile.strandConnected pair (.inl left) (.inl right) = true := by
  classical
  change right ∈
      (Finpartition.ofSetoid (trackedSetoid profile semantic pair)).part left ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- A canonical label for the part containing one position. -/
noncomputable def partitionRepresentative
    (partition : Finpartition (Finset.univ : Finset (Fin 6)))
    (position : Fin 6) : Fin 6 :=
  (partition.part position).min'
    ⟨position, partition.mem_part (Finset.mem_univ position)⟩

theorem partitionRepresentative_mem_part
    (partition : Finpartition (Finset.univ : Finset (Fin 6)))
    (position : Fin 6) :
    partitionRepresentative partition position ∈ partition.part position :=
  Finset.min'_mem _ _

/-- The minimum representative fits in the position-indexed finite type. -/
noncomputable def boundedPartitionRepresentative
    (partition : Finpartition (Finset.univ : Finset (Fin 6)))
    (position : Fin 6) : Fin (position.val + 1) :=
  ⟨(partitionRepresentative partition position).val,
    Nat.lt_succ_of_le (Finset.min'_le _ position
      (partition.mem_part (Finset.mem_univ position)))⟩

@[simp]
theorem boundedPartitionRepresentative_val
    (partition : Finpartition (Finset.univ : Finset (Fin 6)))
    (position : Fin 6) :
    (boundedPartitionRepresentative partition position).val =
      (partitionRepresentative partition position).val :=
  rfl

theorem mem_part_iff_partitionRepresentative_eq
    (partition : Finpartition (Finset.univ : Finset (Fin 6)))
    (left right : Fin 6) :
    right ∈ partition.part left ↔
      partitionRepresentative partition right =
        partitionRepresentative partition left := by
  constructor
  · intro hmem
    have hparts : partition.part right = partition.part left :=
      (partition.mem_part_iff_part_eq_part
        (Finset.mem_univ right) (Finset.mem_univ left)).1 hmem
    simp only [partitionRepresentative, hparts]
  · intro hrepresentative
    apply (partition.mem_part_iff_part_eq_part
      (Finset.mem_univ right) (Finset.mem_univ left)).2
    apply partition.eq_of_mem_parts
      (partition.part_mem.2 (Finset.mem_univ right))
      (partition.part_mem.2 (Finset.mem_univ left))
    · exact partitionRepresentative_mem_part partition right
    · rw [hrepresentative]
      exact partitionRepresentative_mem_part partition left

/-- Kernel-checked finite ceiling for the semantic Cell-letter code.  The raw
profile has three arbitrary `6 × 6` Boolean matrices; the partition code is
over eighteen orders of magnitude smaller even before source reachability is
used. -/
theorem card_finiteHexCellProfileCode_le :
    Fintype.card FiniteHexCellProfileCode ≤ 272097792000 := by
  rw [Fintype.card_prod, Fintype.card_fun]
  have hword :
      Fintype.card
          {word : Fin 6 → StrandColor // IsProperCyclicColorWord word} ≤
        3 ^ 6 := by
    calc
      Fintype.card
          {word : Fin 6 → StrandColor // IsProperCyclicColorWord word} ≤
          Fintype.card (Fin 6 → StrandColor) :=
        Fintype.card_subtype_le _
      _ = 3 ^ 6 := by
        rw [Fintype.card_fun]
        have hcolor : Fintype.card StrandColor = 3 := by decide
        rw [hcolor, Fintype.card_fin]
  have hpair : Fintype.card TrackedColorPair = 3 := by decide
  have hlabels : Fintype.card CanonicalComponentLabels = 720 := by
    rw [Fintype.card_pi]
    decide
  rw [hpair, hlabels]
  calc
    Fintype.card
          {word : Fin 6 → StrandColor // IsProperCyclicColorWord word} *
        720 ^ 3 ≤
        3 ^ 6 * 720 ^ 3 := by
      exact Nat.mul_le_mul_right (720 ^ 3) hword
    _ = 272097792000 := by norm_num

/-- Replace the three semantic connectivity matrices by their component
partitions. -/
noncomputable def encode (profile : CorridorCutProfile 6 0 0)
    (semantic : IsGraphSemantic profile) : FiniteHexCellProfileCode :=
  ⟨⟨profile.edgeColor, semantic.proper⟩,
    fun pair => boundedPartitionRepresentative
      (trackedPartition profile semantic pair)⟩

/-- Boolean membership in one of the three tracked two-color pairs, stated on
the finite source alphabet so decoding performs no proof-level search. -/
def isTrackedStrandColor : TrackedColorPair → StrandColor → Bool
  | .ab, .a | .ab, .b => true
  | .ac, .a | .ac, .c => true
  | .bc, .b | .bc, .c => true
  | _, _ => false

@[simp]
theorem isTrackedStrandColor_eq_true_iff
    (pair : TrackedColorPair) (color : StrandColor) :
    isTrackedStrandColor pair color = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 color.toColor := by
  cases pair <;> cases color <;> decide

/-- Decode a flat Cell code back to the raw six-edge profile.  Arbitrary codes
need not satisfy all graph laws; the round-trip theorem below is deliberately
restricted to the semantic image. -/
def decode (code : FiniteHexCellProfileCode) :
    CorridorCutProfile 6 0 0 where
  edgeColor := code.1.1
  strandConnected := fun pair left right =>
    match left, right with
    | .inl leftPosition, .inl rightPosition =>
        isTrackedStrandColor pair (code.1.1 leftPosition) &&
          isTrackedStrandColor pair (code.1.1 rightPosition) &&
          decide ((code.2 pair leftPosition).val =
            (code.2 pair rightPosition).val)
    | .inl _, .inr impossible => Fin.elim0 impossible
    | .inr impossible, _ => Fin.elim0 impossible
  faceContinues := fun impossible => Fin.elim0 impossible
  fragmentContainsPort := fun impossible => Fin.elim0 impossible
  faceLengthCap := fun impossible => Fin.elim0 impossible

private theorem bool_eq_of_true_iff_true {left right : Bool}
    (h : left = true ↔ right = true) : left = right := by
  cases left <;> cases right <;> simp_all

/-- Encoding followed by decoding is exactly the original semantic Cell
profile, including every tracked-connectivity entry. -/
theorem decode_encode (profile : CorridorCutProfile 6 0 0)
    (semantic : IsGraphSemantic profile) :
    decode (encode profile semantic) = profile := by
  cases profile with
  | mk edgeColor strandConnected faceContinues fragmentContainsPort faceLengthCap =>
    rw [CorridorCutProfile.mk.injEq]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · funext pair leftPort rightPort
      rcases leftPort with leftPosition | leftImpossible
      · rcases rightPort with rightPosition | rightImpossible
        · apply bool_eq_of_true_iff_true
          simp only [decode, encode, Bool.and_eq_true,
            isTrackedStrandColor_eq_true_iff, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨hleftTracked, hrightTracked⟩, hrepresentative⟩
            have hrepresentativeRaw :
                partitionRepresentative
                    (trackedPartition
                      ⟨edgeColor, strandConnected, faceContinues,
                        fragmentContainsPort, faceLengthCap⟩ semantic pair)
                    rightPosition =
                  partitionRepresentative
                    (trackedPartition
                      ⟨edgeColor, strandConnected, faceContinues,
                        fragmentContainsPort, faceLengthCap⟩ semantic pair)
                    leftPosition := by
              apply Fin.ext
              simpa using hrepresentative.symm
            have hmem :=
              (mem_part_iff_partitionRepresentative_eq
                (trackedPartition
                  ⟨edgeColor, strandConnected, faceContinues,
                    fragmentContainsPort, faceLengthCap⟩ semantic pair)
                leftPosition rightPosition).2 hrepresentativeRaw
            rcases (mem_trackedPartition_part_iff _ _ _ _ _).1 hmem with
              hsame | hconnected
            · subst rightPosition
              exact (semantic.diagonal pair leftPosition).2 hleftTracked
            · exact hconnected
          · intro hconnected
            rcases semantic.support pair leftPosition rightPosition hconnected with
              ⟨hleftTracked, hrightTracked⟩
            refine ⟨⟨hleftTracked, hrightTracked⟩, ?_⟩
            have hmem : rightPosition ∈
                (trackedPartition
                  ⟨edgeColor, strandConnected, faceContinues,
                    fragmentContainsPort, faceLengthCap⟩ semantic pair).part
                  leftPosition :=
              (mem_trackedPartition_part_iff _ _ _ _ _).2 (Or.inr hconnected)
            have hrepresentativeRaw :=
              (mem_part_iff_partitionRepresentative_eq _ _ _).1 hmem
            simpa using congrArg Fin.val hrepresentativeRaw.symm
        · exact Fin.elim0 rightImpossible
      · exact Fin.elim0 leftImpossible
    · funext impossible
      exact Fin.elim0 impossible
    · funext impossible
      exact Fin.elim0 impossible
    · funext impossible
      exact Fin.elim0 impossible

/-- The partition code loses no entry of a graph-semantic Cell profile. -/
theorem encode_injective
    {left right : CorridorCutProfile 6 0 0}
    (leftSemantic : IsGraphSemantic left)
    (rightSemantic : IsGraphSemantic right)
    (heq : encode left leftSemantic = encode right rightSemantic) :
    left = right := by
  have hedge : left.edgeColor = right.edgeColor :=
    congrArg (fun code : FiniteHexCellProfileCode => code.1.1) heq
  cases left with
  | mk leftEdge leftStrand leftFace leftContains leftLength =>
    cases right with
    | mk rightEdge rightStrand rightFace rightContains rightLength =>
      simp only at hedge ⊢
      subst rightEdge
      have hpart : ∀ pair,
          boundedPartitionRepresentative (trackedPartition
              ⟨leftEdge, leftStrand, leftFace, leftContains, leftLength⟩
              leftSemantic pair) =
            boundedPartitionRepresentative (trackedPartition
              ⟨leftEdge, rightStrand, rightFace, rightContains, rightLength⟩
              rightSemantic pair) := by
        intro pair
        exact congrFun (congrArg Prod.snd heq) pair
      have hpartValue : ∀ pair position,
          partitionRepresentative (trackedPartition
              ⟨leftEdge, leftStrand, leftFace, leftContains, leftLength⟩
              leftSemantic pair) position =
            partitionRepresentative (trackedPartition
              ⟨leftEdge, rightStrand, rightFace, rightContains, rightLength⟩
              rightSemantic pair) position := by
        intro pair position
        apply Fin.ext
        exact congrArg (fun label : Fin (position.val + 1) => label.val)
          (congrFun (hpart pair) position)
      have hstrand : leftStrand = rightStrand := by
        funext pair leftPort rightPort
        rcases leftPort with leftPosition | leftImpossible
        · rcases rightPort with rightPosition | rightImpossible
          · apply bool_eq_of_true_iff_true
            by_cases hsame : leftPosition = rightPosition
            · subst rightPosition
              rw [leftSemantic.diagonal, rightSemantic.diagonal]
            · constructor
              · intro hleft
                have hmem : rightPosition ∈
                    (trackedPartition
                      ⟨leftEdge, leftStrand, leftFace, leftContains, leftLength⟩
                      leftSemantic pair).part leftPosition :=
                  (mem_trackedPartition_part_iff _ _ _ _ _).2 (Or.inr hleft)
                have hrepresentative :=
                  (mem_part_iff_partitionRepresentative_eq _ _ _).1 hmem
                rw [hpartValue pair rightPosition,
                  hpartValue pair leftPosition] at hrepresentative
                have hmemRight :=
                  (mem_part_iff_partitionRepresentative_eq _ _ _).2
                    hrepresentative
                exact ((mem_trackedPartition_part_iff _ _ _ _ _).1
                  hmemRight).resolve_left hsame
              · intro hright
                have hmem : rightPosition ∈
                    (trackedPartition
                      ⟨leftEdge, rightStrand, rightFace, rightContains, rightLength⟩
                      rightSemantic pair).part leftPosition :=
                  (mem_trackedPartition_part_iff _ _ _ _ _).2 (Or.inr hright)
                have hrepresentative :=
                  (mem_part_iff_partitionRepresentative_eq _ _ _).1 hmem
                rw [← hpartValue pair rightPosition,
                  ← hpartValue pair leftPosition] at hrepresentative
                have hmemLeft :=
                  (mem_part_iff_partitionRepresentative_eq _ _ _).2
                    hrepresentative
                exact ((mem_trackedPartition_part_iff _ _ _ _ _).1
                  hmemLeft).resolve_left hsame
          · exact Fin.elim0 rightImpossible
        · exact Fin.elim0 leftImpossible
      subst rightStrand
      have hface : leftFace = rightFace := by
        funext impossible
        exact Fin.elim0 impossible
      have hcontains : leftContains = rightContains := by
        funext impossible
        exact Fin.elim0 impossible
      have hlength : leftLength = rightLength := by
        funext impossible
        exact Fin.elim0 impossible
      subst rightFace
      subst rightContains
      subst rightLength
      rfl

end GoertzelV24FiniteHexCellProfileCompression

namespace GoertzelV24FramedTrail

open GoertzelV24FiniteHexCellProfileCompression
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance finiteHexCellProfileCompressionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- Every graph-derived literal Cell profile lies in the partition-compressed
semantic carrier. -/
theorem localLayerCellBoundaryProfile_isGraphSemantic
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) :
    IsGraphSemantic (aligned.localLayerCellBoundaryProfile color hcolor) := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let profile := aligned.localLayerCellBoundaryProfile color hcolor
  refine {
    proper := by
      exact placedHexColorWord_isProper aligned.localLayerCellPlacement
        hcubic hrotation color hcolor
    support := ?_
    diagonal := ?_
    symmetric := ?_
    transitive := ?_ }
  · intro pair left right hconnected
    rw [aligned.localLayerCellBoundaryProfile_strandConnected] at hconnected
    rw [localLayerCellConnectivityProfile,
      placedHexRegionalConnectivityProfile_eq_true_iff] at hconnected
    simpa only [aligned.localLayerCellBoundaryProfile_edgeColor_toColor] using
      ⟨hconnected.2.2.1, hconnected.2.2.2.1⟩
  · intro pair position
    rw [aligned.localLayerCellBoundaryProfile_strandConnected]
    change regionalTrackedConnectivity RS
        aligned.toInterface.localLayerCellBoundaryRegion color pair
        (aligned.localLayerCellBoundaryEdge position)
        (aligned.localLayerCellBoundaryEdge position) = true ↔ _
    rw [regionalTrackedConnectivity_self_eq_true_iff]
    simp only [aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion,
      true_and, aligned.localLayerCellBoundaryProfile_edgeColor_toColor]
  · intro pair left right
    rw [aligned.localLayerCellBoundaryProfile_strandConnected,
      aligned.localLayerCellBoundaryProfile_strandConnected]
    exact placedHexRegionalConnectivityProfile_comm
      aligned.localLayerCellPlacement
      aligned.toInterface.localLayerCellBoundaryRegion color pair left right
  · intro pair left middle right hleft hright
    rw [aligned.localLayerCellBoundaryProfile_strandConnected] at hleft hright ⊢
    exact regionalTrackedConnectivity_trans RS
      aligned.toInterface.localLayerCellBoundaryRegion color pair
      (aligned.localLayerCellBoundaryEdge left)
      (aligned.localLayerCellBoundaryEdge middle)
      (aligned.localLayerCellBoundaryEdge right) hleft hright

/-- The finite partition code carried by one actual source Cell. -/
noncomputable def localLayerFiniteHexCellProfileCode
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) : FiniteHexCellProfileCode :=
  encode (aligned.localLayerCellBoundaryProfile color hcolor)
    (aligned.localLayerCellBoundaryProfile_isGraphSemantic
      hcubic hrotation color hcolor)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
