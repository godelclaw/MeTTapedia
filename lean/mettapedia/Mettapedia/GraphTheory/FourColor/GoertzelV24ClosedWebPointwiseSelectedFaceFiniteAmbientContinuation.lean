import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOldEdgeAdequacy
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation

/-!
# Pointwise-selected finite ambient-face continuation

Every outgoing regional fragment meets one selected crossing of the second
literal local layer.  Since an edge is incident with at most two orbit faces,
the fragment's ambient face is one of the three vertices of that two-step
dual walk.  This yields the same three-valued continuation code as the rooted
Cell ABI, using only the selected interior receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation
open GoertzelV24ClosedWebPointwiseSelectedFaceFiniteOutputFragment
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedFaceFiniteAmbientContinuationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Formation

/-- Position of a face role on the literal two-edge outgoing dual walk. -/
def pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex :
    SourceLocalLayerSerialOutputFaceRole → Nat
  | .first => 0
  | .center => 1
  | .second => 2

/-- Interpret a finite outgoing role as the corresponding face of the
selected literal two-step layer. -/
def pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialOutputFaceRole → OrbitFace formation.annular.RS
  | role =>
      ((pointwiseSelectedSourceLocalLayerPairAt formation corridor hinterior
        offset).secondWalk.getVert
          (pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex role)).1

/-- The three selected outgoing roles name distinct ambient faces. -/
theorem pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_injective
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Function.Injective
      (pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole formation
        corridor hinterior offset) := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  intro left right heq
  have hleft :
      pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex left ∈
        {index | index ≤ layers.secondWalk.length} := by
    cases left <;>
      simp [pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex,
        Formation.LocalLayerPair.secondWalk]
  have hright :
      pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex right ∈
        {index | index ≤ layers.secondWalk.length} := by
    cases right <;>
      simp [pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex,
        Formation.LocalLayerPair.secondWalk]
  have hvertices :
      layers.secondWalk.getVert
          (pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex left) =
        layers.secondWalk.getVert
          (pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex right) :=
    Subtype.ext heq
  have hindices := layers.secondWalk_isPath.getVert_injOn hleft hright hvertices
  cases left <;> cases right <;>
    simp_all [pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleIndex]

/-- Every selected outgoing fragment lies on one of the three literal faces
of the second local-layer walk. -/
theorem exists_pointwiseSelectedSourceLocalLayerSerialOutputFaceRole
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    ∃ role : SourceLocalLayerSerialOutputFaceRole,
      pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole formation corridor
        hinterior offset role = fragment.1.1 := by
  let layers := pointwiseSelectedSourceLocalLayerPairAt formation corridor
    hinterior offset
  let pair := layers.pointwiseSelectedLocalLayerPair hinterior
  let cut := indexedCrossingEdgeSet
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset)
  let region :=
    pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
      corridor hinterior offset
  let edge := boundaryRegionalFragmentCutEdge formation.annular.RS cut region
    fragment
  have hedgeCut : edge ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut formation.annular.RS cut region
      fragment
  rcases (mem_indexedCrossingEdgeSet_iff
    (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
      hinterior offset) edge).1 hedgeCut with ⟨step, hstep⟩
  let secondStep : Fin pair.right.crosscut.walk.length :=
    ⟨step.val, by
      simpa [pair, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
        Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
        Formation.LocalLayerPair.secondLayer,
        Formation.LocalLayerPair.secondWalk] using step.isLt⟩
  have hedgeCrossing : pair.right.crossingEdge secondStep = edge := by
    simpa [pointwiseSelectedSourceLocalLayerRightCrossingAt, layers, pair,
      secondStep, Formation.LocalLayerPair.pointwiseSelectedLocalLayerPair,
      Formation.LocalLayerPair.pointwiseSelectedSecondLayer,
      Formation.LocalLayerPair.secondLayer,
      Formation.LocalLayerPair.secondWalk] using hstep
  have hedgeFragment : edge ∈
      boundaryRegionalFragmentEdges formation.annular.RS cut region fragment :=
    boundaryRegionalFragmentCutEdge_mem_fragment formation.annular.RS cut region
      fragment
  have hedgeFace : edge ∈ orbitFaceBoundary formation.annular.RS fragment.1.1 :=
    (Finset.mem_inter.mp
      (boundaryRegionalFragmentEdges_subset_boundary_inter_region
        formation.annular.RS cut region fragment hedgeFragment)).1
  let leftFace := pair.right.crosscut.walk.getVert secondStep.val
  let rightFace := pair.right.crosscut.walk.getVert (secondStep.val + 1)
  have hleftFace : edge ∈ orbitFaceBoundary formation.annular.RS leftFace.1 := by
    rw [← hedgeCrossing]
    exact pair.right.crossingEdge_mem_leftFace secondStep
  have hrightFace : edge ∈ orbitFaceBoundary formation.annular.RS rightFace.1 := by
    rw [← hedgeCrossing]
    exact pair.right.crossingEdge_mem_rightFace secondStep
  have hfacesNe : leftFace.1 ≠ rightFace.1 := by
    intro hfaces
    exact (pair.right.crosscut.walk.adj_getVert_succ secondStep.isLt).ne
      (Subtype.ext hfaces)
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary formation.annular.RS)
      (Finset.univ : Finset (OrbitFace formation.annular.RS))
      (orbitFace_incidence_le_two formation.annular.RS) leftFace.2 rightFace.2
      (Finset.mem_univ fragment.1.1) hfacesNe hleftFace hrightFace hedgeFace
  fin_cases step <;> rcases hcases with hleft | hright
  · refine ⟨.first, ?_⟩
    change layers.firstFace.1 = fragment.1.1
    exact hleft.symm
  · refine ⟨.center, ?_⟩
    change
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (pointwiseSelectedSourceLocalLayerInteriorAt offset).outgoing.right).1 =
          fragment.1.1
    exact hright.symm
  · refine ⟨.center, ?_⟩
    change
      (corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton.faceAt
        (pointwiseSelectedSourceLocalLayerInteriorAt offset).outgoing.right).1 =
          fragment.1.1
    exact hleft.symm
  · refine ⟨.second, ?_⟩
    change layers.secondFace.1 = fragment.1.1
    exact hright.symm

/-- Canonical three-valued ambient-face role of a selected output fragment. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    SourceLocalLayerSerialOutputFaceRole :=
  Classical.choose
    (exists_pointwiseSelectedSourceLocalLayerSerialOutputFaceRole formation
      corridor hinterior offset fragment)

@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_roleAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (fragment : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole formation corridor
        hinterior offset
        (pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt formation
          corridor hinterior offset fragment) = fragment.1.1 :=
  Classical.choose_spec
    (exists_pointwiseSelectedSourceLocalLayerSerialOutputFaceRole formation
      corridor hinterior offset fragment)

/-- Equality of selected finite roles is exactly ambient-face continuation. -/
theorem pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt_eq_iff
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (left right : PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt
      formation corridor hinterior offset) :
    pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt formation corridor
        hinterior offset left =
      pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt formation corridor
        hinterior offset right ↔
      left.1.1 = right.1.1 := by
  constructor
  · intro hrole
    rw [← pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_roleAt
      formation corridor hinterior offset left,
      ← pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_roleAt
      formation corridor hinterior offset right]
    exact congrArg
      (pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole formation corridor
        hinterior offset) hrole
  · intro hface
    apply pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_injective
      formation corridor hinterior offset
    rw [pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_roleAt formation
      corridor hinterior offset left,
      pointwiseSelectedSourceLocalLayerSerialOutputFaceOfRole_roleAt formation
      corridor hinterior offset right]
    exact hface

/-- Role code on the finite enumeration of the selected output fragments. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleCodeAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :
    Fin (Fintype.card
      (PointwiseSelectedSourceLocalLayerSerialFaceOutputFragmentAt formation
        corridor hinterior offset)) → SourceLocalLayerSerialOutputFaceRole :=
  fun index =>
    pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt formation corridor
      hinterior offset
      (boundaryRegionalFragmentAt formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset) index)

/-- The output profile's continuation bit is exactly equality of the selected
three-valued role code, for every supplied output colour function. -/
theorem pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputBoundedProfileAt_faceContinues_iff_roleCode
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
        hinterior offset step) ≠ 0)
    (left right : Fin
      (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputBoundedProfileAt
        formation corridor hinterior offset color hcolor).faceFragmentCount.val) :
    ((pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputBoundedProfileAt
        formation corridor hinterior offset color hcolor).profile.faceContinues
        left right = true) ↔
      pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleCodeAt formation
          corridor hinterior offset left =
        pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleCodeAt formation
          corridor hinterior offset right := by
  change decide
      ((boundaryRegionalFragmentAt formation.annular.RS
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
              hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            formation corridor hinterior offset) left).1.1 =
        (boundaryRegionalFragmentAt formation.annular.RS
          (indexedCrossingEdgeSet
            (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
              hinterior offset))
          (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            formation corridor hinterior offset) right).1.1) = true ↔ _
  rw [decide_eq_true_eq]
  exact
    (pointwiseSelectedSourceLocalLayerSerialOutputFaceRoleAt_eq_iff formation
      corridor hinterior offset
      (boundaryRegionalFragmentAt formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset) left)
      (boundaryRegionalFragmentAt formation.annular.RS
        (indexedCrossingEdgeSet
          (pointwiseSelectedSourceLocalLayerRightCrossingAt formation corridor
            hinterior offset))
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt formation
          corridor hinterior offset) right)).symm

end Formation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
