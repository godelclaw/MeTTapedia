import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOldEdgeAdequacy

/-!
# Finite ambient-face roles after one literal source Cell

Every outgoing regional fragment meets one of the two crossings of the
second literal local layer.  The ambient face of that fragment is therefore
one of the three facial vertices of the two-step layer walk.  This gives a
three-valued finite code for ambient face continuation on the opened annulus.

The code deliberately classifies ambient orbit faces, not regional
components.  Distinct regional fragments may lie on one ambient face on a
one-sided carrier; the occurrence-sensitive component decoder remains
separate.  No global face-two-sidedness hypothesis is used here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFiniteAmbientContinuationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The three literal facial roles on the outgoing two-step layer. -/
inductive SourceLocalLayerSerialOutputFaceRole
  | first
  | center
  | second
  deriving DecidableEq, Fintype

/-- Interpret a finite outgoing role as its literal ambient orbit face. -/
def sourceLocalLayerSerialOutputFaceOfRole
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerSerialOutputFaceRole → OrbitFace web.annular.RS
  | .first => (sourceLocalLayerPairAt corridor hunique offset).firstFace.1
  | .center => (sourceLocalLayerPairAt corridor hunique offset).nextCenterFace.1
  | .second => (sourceLocalLayerPairAt corridor hunique offset).secondFace.1

/-- The three literal outgoing roles name three distinct faces. -/
theorem sourceLocalLayerSerialOutputFaceOfRole_injective
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Function.Injective
      (sourceLocalLayerSerialOutputFaceOfRole corridor hunique offset) := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  intro left right heq
  cases left <;> cases right
  · rfl
  · exact False.elim (layers.first_adjacent_nextCenter.ne (Subtype.ext heq))
  · exact False.elim (layers.first_ne_second (Subtype.ext heq))
  · exact False.elim (layers.first_adjacent_nextCenter.ne
      (Subtype.ext heq.symm))
  · rfl
  · exact False.elim (layers.nextCenter_adjacent_second.ne (Subtype.ext heq))
  · exact False.elim (layers.first_ne_second (Subtype.ext heq.symm))
  · exact False.elim (layers.nextCenter_adjacent_second.ne
      (Subtype.ext heq.symm))
  · rfl

/-- The ambient face of every actual outgoing fragment is one of the three
faces of the literal two-step outgoing layer. -/
theorem exists_sourceLocalLayerSerialOutputFaceRole
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    ∃ role : SourceLocalLayerSerialOutputFaceRole,
      sourceLocalLayerSerialOutputFaceOfRole corridor hunique offset role =
        fragment.1.1 := by
  let layers := sourceLocalLayerPairAt corridor hunique offset
  let cut := indexedCrossingEdgeSet
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let edge := boundaryRegionalFragmentCutEdge web.annular.RS cut region fragment
  have hedgeCut : edge ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut web.annular.RS cut region fragment
  rcases (mem_indexedCrossingEdgeSet_iff
    (sourceLocalLayerRightCrossingAt corridor hunique offset) edge).1 hedgeCut with
    ⟨step, hstep⟩
  let secondStep : Fin layers.secondLayer.walk.length :=
    ⟨step.val, by
      simpa [LocalLayerPair.secondLayer, LocalLayerPair.secondWalk] using
        step.isLt⟩
  have hedgeCrossing : edge ∈ layers.secondLayer.crossingEdges hunique := by
    apply (layers.secondLayer.mem_crossingEdges_iff hunique edge).2
    refine ⟨secondStep, ?_⟩
    simpa [sourceLocalLayerRightCrossingAt, layers, secondStep] using hstep
  have hedgeFragment : edge ∈
      boundaryRegionalFragmentEdges web.annular.RS cut region fragment :=
    boundaryRegionalFragmentCutEdge_mem_fragment web.annular.RS cut region
      fragment
  have hedgeFace : edge ∈ orbitFaceBoundary web.annular.RS fragment.1.1 :=
    (Finset.mem_inter.mp
      (boundaryRegionalFragmentEdges_subset_boundary_inter_region
        web.annular.RS cut region fragment hedgeFragment)).1
  have hsupport :
      (⟨fragment.1.1, Finset.mem_univ fragment.1.1⟩ :
        AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))) ∈
        layers.secondWalk.support := by
    exact layers.secondLayer.face_mem_walk_support_of_mem_crossingEdge_of_mem_boundary
      hunique hedgeCrossing hedgeFace
  simp only [LocalLayerPair.secondWalk, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, List.mem_cons] at hsupport
  rcases hsupport with hfirst | hcenter | hsecond
  · exact ⟨.first, congrArg Subtype.val hfirst.symm⟩
  · exact ⟨.center, congrArg Subtype.val hcenter.symm⟩
  · rcases hsecond with hsecond | hnone
    · exact ⟨.second, congrArg Subtype.val hsecond.symm⟩
    · simp at hnone

/-- The canonical three-valued ambient-face role of an outgoing fragment. -/
noncomputable def sourceLocalLayerSerialOutputFaceRoleAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) : SourceLocalLayerSerialOutputFaceRole :=
  Classical.choose
    (exists_sourceLocalLayerSerialOutputFaceRole corridor hunique offset
      fragment)

@[simp]
theorem sourceLocalLayerSerialOutputFaceOfRole_roleAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    sourceLocalLayerSerialOutputFaceOfRole corridor hunique offset
        (sourceLocalLayerSerialOutputFaceRoleAt corridor hunique offset
          fragment) = fragment.1.1 :=
  Classical.choose_spec
    (exists_sourceLocalLayerSerialOutputFaceRole corridor hunique offset
      fragment)

/-- Equality of the finite roles is exactly ambient-face continuation. -/
theorem sourceLocalLayerSerialOutputFaceRoleAt_eq_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (left right : SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique
      offset) :
    sourceLocalLayerSerialOutputFaceRoleAt corridor hunique offset left =
        sourceLocalLayerSerialOutputFaceRoleAt corridor hunique offset right ↔
      left.1.1 = right.1.1 := by
  constructor
  · intro hrole
    rw [← sourceLocalLayerSerialOutputFaceOfRole_roleAt corridor hunique
      offset left, ← sourceLocalLayerSerialOutputFaceOfRole_roleAt corridor
      hunique offset right]
    exact congrArg
      (sourceLocalLayerSerialOutputFaceOfRole corridor hunique offset) hrole
  · intro hface
    apply sourceLocalLayerSerialOutputFaceOfRole_injective corridor hunique offset
    rw [sourceLocalLayerSerialOutputFaceOfRole_roleAt corridor hunique offset
      left, sourceLocalLayerSerialOutputFaceOfRole_roleAt corridor hunique offset
      right]
    exact hface

/-- The dependent fragment enumeration of the actual outgoing profile, read
through the canonical three-valued ambient-face role. -/
noncomputable def sourceLocalLayerSerialOutputFaceRoleCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Fin (Fintype.card
      (SourceLocalLayerSerialFaceOutputFragmentAt corridor hunique offset)) →
      SourceLocalLayerSerialOutputFaceRole :=
  fun index =>
    sourceLocalLayerSerialOutputFaceRoleAt corridor hunique offset
      (boundaryRegionalFragmentAt web.annular.RS
        (indexedCrossingEdgeSet
          (sourceLocalLayerRightCrossingAt corridor hunique offset))
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        index)

/-- The graph-derived outgoing profile's ambient continuation bit is exactly
equality of the three-valued role code.  This closes the fifth finite facial
observation without identifying distinct regional components. -/
theorem sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt_faceContinues_iff_roleCode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (left right : Fin
      (sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
        offset).faceFragmentCount.val) :
    ((sourceLocalLayerSerialPreRebaseOutputBoundedProfileAt corridor hunique
        offset).profile.faceContinues left right = true) ↔
      sourceLocalLayerSerialOutputFaceRoleCodeAt corridor hunique offset left =
        sourceLocalLayerSerialOutputFaceRoleCodeAt corridor hunique offset
          right := by
  change decide
      ((boundaryRegionalFragmentAt web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          left).1.1 =
        (boundaryRegionalFragmentAt web.annular.RS
          (indexedCrossingEdgeSet
            (sourceLocalLayerRightCrossingAt corridor hunique offset))
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          right).1.1) = true ↔ _
  rw [decide_eq_true_eq]
  exact (sourceLocalLayerSerialOutputFaceRoleAt_eq_iff corridor hunique offset
    (boundaryRegionalFragmentAt web.annular.RS
      (indexedCrossingEdgeSet
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      left)
    (boundaryRegionalFragmentAt web.annular.RS
      (indexedCrossingEdgeSet
        (sourceLocalLayerRightCrossingAt corridor hunique offset))
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      right)).symm

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteAmbientContinuation

end Mettapedia.GraphTheory.FourColor
