import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialFaceFactorReceipt

/-!
# The uncaptured old-face residue of one literal serial update

The displayed two-edge input profile records only face fragments meeting that
displayed cut.  Until the cumulative Cell frontier is proved to cancel to its
two ends, it is not sound to assert that those fragments cover every old-prefix
piece of an outgoing face.

This module makes the remaining dependency exact.  It unions precisely the
incoming fragments on the same facial side that embed into a named outgoing
fragment, defines the old-prefix residue left uncovered by that union, and
proves a disjoint capped-length partition.  Thus all unexplained old-prefix
face-length dependence is localized to one finite residue cap.  No claim that
the residue vanishes is made here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialFaceInputResidueEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The union of exactly those displayed-input fragments that occur on the
same facial side inside one outgoing fragment. -/
noncomputable def sourceCorridorSerialSelectedInputFaceUnionAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) : Finset G.edgeSet := by
  classical
  let inputData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  exact (Finset.univ.filter fun input =>
    sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic
      hrotation htwoSided hunique offset output input).biUnion
      inputData.regionalFragmentEdges

/-- The part of the old-prefix slice not represented by any displayed-input
fragment on the correct facial side. -/
noncomputable def sourceCorridorSerialOldFaceInputResidueAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) : Finset G.edgeSet :=
  sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation htwoSided
      hunique offset output \
    sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic hrotation
      htwoSided hunique offset output

/-- The only observation of the uncaptured residue needed by the manuscript's
face-progress coordinate. -/
noncomputable def sourceCorridorSerialOldFaceInputResidueCapAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) : Fin 6 :=
  ⟨min (sourceCorridorSerialOldFaceInputResidueAt realization hcubic hrotation
      htwoSided hunique offset output).card 5, by omega⟩

/-- The selected input fragments really lie in the old-prefix slice. -/
theorem sourceCorridorSerialSelectedInputFaceUnionAt_subset_oldFaceSlice
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic hrotation
        htwoSided hunique offset output ⊆
      sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
        htwoSided hunique offset output := by
  classical
  let inputData := sourceCorridorSerialInputCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  let outputData := sourceCorridorSerialPrefixCutDataAt realization hcubic
    hrotation htwoSided hunique offset
  intro edge hedge
  simp only [sourceCorridorSerialSelectedInputFaceUnionAt] at hedge
  rcases Finset.mem_biUnion.1 hedge with
    ⟨input, hinputSelected, hedgeInput⟩
  have hused : sourceCorridorSerialInputFaceUsedByOutputAt realization hcubic
      hrotation htwoSided hunique offset output input :=
    (Finset.mem_filter.1 hinputSelected).2
  have hedgeOutput : edge ∈ outputData.regionalFragmentEdges output :=
    hused.2 hedgeInput
  have hedgeOldRegion : edge ∈
      sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
        hunique offset := by
    have : edge ∈ inputData.regionEdges := (Finset.mem_inter.1 hedgeInput).2
    simpa [inputData, sourceCorridorSerialInputCutDataAt,
      regionalBoundaryGraphCutData] using this
  exact Finset.mem_inter.2 ⟨hedgeOutput, hedgeOldRegion⟩

/-- The selected input union and the uncaptured residue partition the entire
old-prefix slice. -/
theorem sourceCorridorSerialSelectedInputFaceUnionAt_union_residue
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic hrotation
          htwoSided hunique offset output ∪
        sourceCorridorSerialOldFaceInputResidueAt realization hcubic hrotation
          htwoSided hunique offset output =
      sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
        htwoSided hunique offset output := by
  classical
  let selected := sourceCorridorSerialSelectedInputFaceUnionAt realization
    hcubic hrotation htwoSided hunique offset output
  let oldSlice := sourceCorridorSerialOldFaceSliceAt realization hcubic
    hrotation htwoSided hunique offset output
  have hsubset : selected ⊆ oldSlice :=
    sourceCorridorSerialSelectedInputFaceUnionAt_subset_oldFaceSlice
      realization hcubic hrotation htwoSided hunique offset output
  ext edge
  simp only [sourceCorridorSerialOldFaceInputResidueAt,
    Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hselected | ⟨hold, _⟩)
    · exact hsubset hselected
    · exact hold
  · intro hold
    by_cases hselected : edge ∈ selected
    · exact Or.inl hselected
    · exact Or.inr ⟨hold, hselected⟩

/-- The residue is disjoint from the selected input union by construction. -/
theorem sourceCorridorSerialSelectedInputFaceUnionAt_disjoint_residue
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    Disjoint
      (sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic
        hrotation htwoSided hunique offset output)
      (sourceCorridorSerialOldFaceInputResidueAt realization hcubic hrotation
        htwoSided hunique offset output) := by
  classical
  rw [Finset.disjoint_left]
  intro edge hselected hresidue
  exact (Finset.mem_sdiff.1 hresidue).2 hselected

/-- The cap-at-five size of the old slice splits exactly into the selected
input contribution and one residue cap.  This is the fail-closed form of the
remaining facial locality obligation. -/
theorem sourceCorridorSerialOldFaceSliceAt_cap_eq_selected_add_residue
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    min (sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
          htwoSided hunique offset output).card 5 =
      min
        (min (sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic
              hrotation htwoSided hunique offset output).card 5 +
          min (sourceCorridorSerialOldFaceInputResidueAt realization hcubic
              hrotation htwoSided hunique offset output).card 5)
        5 := by
  let selected := sourceCorridorSerialSelectedInputFaceUnionAt realization
    hcubic hrotation htwoSided hunique offset output
  let oldSlice := sourceCorridorSerialOldFaceSliceAt realization hcubic
    hrotation htwoSided hunique offset output
  have hsubset : selected ⊆ oldSlice :=
    sourceCorridorSerialSelectedInputFaceUnionAt_subset_oldFaceSlice
      realization hcubic hrotation htwoSided hunique offset output
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  change min oldSlice.card 5 =
    min (min selected.card 5 + min (oldSlice \ selected).card 5) 5
  omega

/-- The exact missing locality statement: every old-prefix piece of every
outgoing face is represented by a same-face displayed-input fragment. -/
def SourceCorridorSerialFaceInputCompleteAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3)) : Prop :=
  ∀ output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset),
    sourceCorridorSerialOldFaceInputResidueAt realization hcubic hrotation
      htwoSided hunique offset output = ∅

/-- Under the exact input-completeness obligation, the selected incoming
fragments cover the old slice with no hidden prefix contribution. -/
theorem sourceCorridorSerialSelectedInputFaceUnionAt_eq_oldFaceSlice_of_complete
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hcomplete : SourceCorridorSerialFaceInputCompleteAt realization hcubic
      hrotation htwoSided hunique offset)
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    sourceCorridorSerialSelectedInputFaceUnionAt realization hcubic hrotation
        htwoSided hunique offset output =
      sourceCorridorSerialOldFaceSliceAt realization hcubic hrotation
        htwoSided hunique offset output := by
  have hpartition :=
    sourceCorridorSerialSelectedInputFaceUnionAt_union_residue realization
      hcubic hrotation htwoSided hunique offset output
  rw [hcomplete output, Finset.union_empty] at hpartition
  exact hpartition

/-- Equivalently, input completeness makes the finite residue cap zero. -/
theorem sourceCorridorSerialOldFaceInputResidueCapAt_eq_zero_of_complete
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hcomplete : SourceCorridorSerialFaceInputCompleteAt realization hcubic
      hrotation htwoSided hunique offset)
    (output : SerialCutFragmentIndex
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset)) :
    sourceCorridorSerialOldFaceInputResidueCapAt realization hcubic hrotation
      htwoSided hunique offset output = 0 := by
  apply Fin.ext
  simp [sourceCorridorSerialOldFaceInputResidueCapAt, hcomplete output]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
