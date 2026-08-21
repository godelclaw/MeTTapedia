import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixFiniteConnectivityUpdate

/-!
# Canonical coordinates for the finite source-Cell connectivity carrier

The one-Cell connectivity contraction uses exactly eight actual edges: the
two incoming cut edges and the six edges of the newly exposed hexagonal face.
This file replaces that graph-dependent subtype by the stable finite
coordinate carrier `Fin 2 ⊕ Fin 6`.

The equivalence preserves the two blocks definitionally.  It is therefore a
coordinate bridge for the `L7` transition, not an arbitrary enumeration of
eight edges and not a complete five-coordinate profile update.  The remaining
face-factor witness is intentionally outside this module.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixFiniteConnectivityCoordinatesEdgeSetDecidableEq :
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

/-- Stable coordinates for the one-Cell connectivity carrier: two old cut
edges followed by the six cyclic positions of the new Cell boundary. -/
abbrev LocalLayerFiniteConnectivityCoordinate := Fin 2 ⊕ Fin 6

/-- Interpret a stable coordinate as its literal edge in the selected
eight-edge interface. -/
def localLayerFiniteConnectivityEdgeAt
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    LocalLayerFiniteConnectivityCoordinate →
      { edge // edge ∈ aligned.localLayerFiniteConnectivityInterface }
  | .inl step =>
      ⟨aligned.toInterface.localLayerPrefixCrossing step,
        aligned.localLayerPrefixCrossing_mem_finiteConnectivityInterface step⟩
  | .inr position =>
      ⟨aligned.localLayerCellBoundaryEdge position,
        aligned.localLayerCellBoundaryRegion_subset_finiteConnectivityInterface
          (aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion position)⟩

@[simp]
theorem localLayerFiniteConnectivityEdgeAt_inl
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    (aligned.localLayerFiniteConnectivityEdgeAt (.inl step)).1 =
      aligned.toInterface.localLayerPrefixCrossing step :=
  rfl

@[simp]
theorem localLayerFiniteConnectivityEdgeAt_inr
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (position : Fin 6) :
    (aligned.localLayerFiniteConnectivityEdgeAt (.inr position)).1 =
      aligned.localLayerCellBoundaryEdge position :=
  rfl

/-- The two coordinate blocks are individually injective and disjoint, so the
stable interpretation loses no edge identity. -/
theorem localLayerFiniteConnectivityEdgeAt_injective
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Injective aligned.localLayerFiniteConnectivityEdgeAt := by
  intro left right heq
  have hval := congrArg Subtype.val heq
  rcases left with left | left <;> rcases right with right | right
  · exact congrArg Sum.inl
      (aligned.toInterface.localLayerPrefixCrossing_injective hval)
  · exfalso
    change aligned.toInterface.localLayerPrefixCrossing left =
      aligned.localLayerCellBoundaryEdge right at hval
    exact aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion left
      (by
        rw [hval]
        exact aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion right)
  · exfalso
    change aligned.localLayerCellBoundaryEdge left =
      aligned.toInterface.localLayerPrefixCrossing right at hval
    exact aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion right
      (by
        rw [← hval]
        exact aligned.localLayerCellBoundaryEdge_mem_cellBoundaryRegion left)
  · exact congrArg Sum.inr
      (aligned.localLayerCellBoundaryEdge_injective hval)

/-- Every selected interface edge has either its old-cut coordinate or its
cyclic Cell-boundary coordinate. -/
theorem localLayerFiniteConnectivityEdgeAt_surjective
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    Function.Surjective aligned.localLayerFiniteConnectivityEdgeAt := by
  rintro ⟨edge, hedge⟩
  rcases Finset.mem_union.1 hedge with hprefix | hcell
  · rcases (mem_indexedCrossingEdgeSet_iff
      aligned.toInterface.localLayerPrefixCrossing edge).1 hprefix with
      ⟨step, hstep⟩
    refine ⟨.inl step, Subtype.ext ?_⟩
    exact hstep
  · have hindexed : edge ∈
        indexedCrossingEdgeSet aligned.localLayerCellBoundaryEdge := by
      rw [aligned.indexedLocalLayerCellBoundaryEdges_eq_cellBoundaryRegion]
      exact hcell
    rcases (mem_indexedCrossingEdgeSet_iff
      aligned.localLayerCellBoundaryEdge edge).1 hindexed with
      ⟨position, hposition⟩
    refine ⟨.inr position, Subtype.ext ?_⟩
    exact hposition

/-- Canonical finite coordinates for the graph-dependent eight-edge subtype.
The inverse is supplied by the proved exact union decomposition. -/
noncomputable def localLayerFiniteConnectivityEquiv
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    LocalLayerFiniteConnectivityCoordinate ≃
      { edge // edge ∈ aligned.localLayerFiniteConnectivityInterface } :=
  Equiv.ofBijective aligned.localLayerFiniteConnectivityEdgeAt
    ⟨aligned.localLayerFiniteConnectivityEdgeAt_injective,
      aligned.localLayerFiniteConnectivityEdgeAt_surjective⟩

@[simp]
theorem localLayerFiniteConnectivityEquiv_apply_inl
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    (aligned.localLayerFiniteConnectivityEquiv (.inl step)).1 =
      aligned.toInterface.localLayerPrefixCrossing step :=
  rfl

@[simp]
theorem localLayerFiniteConnectivityEquiv_apply_inr
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (position : Fin 6) :
    (aligned.localLayerFiniteConnectivityEquiv (.inr position)).1 =
      aligned.localLayerCellBoundaryEdge position :=
  rfl

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
