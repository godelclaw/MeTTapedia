import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorCoverage

/-!
# Finite coordinates for source prefix factors

This file packages the dependent carriers used by one source Cell update and
converts precisely the open branch of factor coverage into an incoming finite
profile coordinate.  The short local names are intentional: these carriers
occur in every update theorem, and expanding them repeatedly is expensive for
the elaborator.

The shared-rung residue remains a separate alternative.  It is not promoted
to a boundary coordinate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFactorCoordinatesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A boundary fragment paired with explicit equations for its ambient face
and edge support.  Keeping both observations stored prevents downstream
profile-coordinate proofs from unfolding a large source-specific constructor. -/
structure BoundaryFragmentSupportWitness
    (RS : RotationSystem V G.edgeSet) (cut region support : Finset G.edgeSet)
    (face : OrbitFace RS)
    where
  boundaryFragment : BoundaryRegionalFragment RS cut region
  face_eq : boundaryFragment.1.1 = face
  edges_eq : boundaryRegionalFragmentEdges RS cut region boundaryFragment =
    support

/-- A raw fragment that already carries a cut-incidence witness packages into
the generic support witness by reflexivity. -/
def boundaryFragmentSupportWitnessOf
    (RS : RotationSystem V G.edgeSet) (cut region : Finset G.edgeSet)
    (face : CutIncidentFace RS cut)
    (fragment : FaceRegionalFragment RS (orbitFaceRoot RS face.1) region)
    (htouch : FaceFragmentTouchesCut RS cut region face fragment) :
    BoundaryFragmentSupportWitness RS cut region
      (faceRegionalFragmentEdges RS (orbitFaceRoot RS face.1) region
        fragment) face.1 :=
  ⟨⟨face, ⟨fragment, htouch⟩⟩, rfl, rfl⟩

/-- Every packaged support witness has a canonical coordinate in the finite
boundary-fragment enumeration. -/
theorem BoundaryFragmentSupportWitness.exists_index
    {RS : RotationSystem V G.edgeSet} {cut region support : Finset G.edgeSet}
    {face : OrbitFace RS}
    (witness : BoundaryFragmentSupportWitness RS cut region support face) :
    ∃ index : Fin (Fintype.card (BoundaryRegionalFragment RS cut region)),
      boundaryRegionalFragmentEdges RS cut region
          (boundaryRegionalFragmentAt RS cut region index) = support := by
  rcases exists_boundaryRegionalFragmentAt_eq RS cut region
      witness.boundaryFragment with ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  rw [hindex]
  exact witness.edges_eq

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

/-- The incoming boundary-fragment carrier for one source Cell update. -/
abbrev LocalLayerLeftBoundaryFragment
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing)
    aligned.toInterface.localLayerLeftPrefixRegion

/-- Canonical finite indices of incoming boundary fragments. -/
abbrev LocalLayerLeftBoundaryIndex
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  Fin (Fintype.card aligned.LocalLayerLeftBoundaryFragment)

/-- The old-prefix factor carrier on the ambient face named by an outgoing
fragment. -/
abbrev LocalLayerLeftFactor
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :=
  FaceRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
      fragment.1.1)
    aligned.toInterface.localLayerLeftPrefixRegion

/-- Edge support of an old-prefix factor. -/
def localLayerLeftFactorEdges
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) : Finset G.edgeSet :=
  faceRegionalFragmentEdges
    embedded.cellulation.rotation.toRotationSystem
    (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
      fragment.1.1)
    aligned.toInterface.localLayerLeftPrefixRegion factor

/-- The canonical incoming boundary fragment at a finite coordinate. -/
noncomputable def localLayerLeftBoundaryFragmentAt
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (index : aligned.LocalLayerLeftBoundaryIndex) :
    aligned.LocalLayerLeftBoundaryFragment :=
  boundaryRegionalFragmentAt
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing)
    aligned.toInterface.localLayerLeftPrefixRegion index

/-- Edge support of a packaged incoming boundary fragment. -/
def localLayerLeftBoundaryFragmentEdges
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.LocalLayerLeftBoundaryFragment) : Finset G.edgeSet :=
  boundaryRegionalFragmentEdges
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing)
    aligned.toInterface.localLayerLeftPrefixRegion fragment

/-- Edge support stored at an incoming finite-profile coordinate. -/
def localLayerLeftBoundaryFragmentEdgesAt
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (index : aligned.LocalLayerLeftBoundaryIndex) : Finset G.edgeSet :=
  aligned.localLayerLeftBoundaryFragmentEdges
    (aligned.localLayerLeftBoundaryFragmentAt index)

/-- An old-prefix factor meets the displayed incoming cut. -/
def LocalLayerLeftFactorTouchesPrefixCut
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) : Prop :=
  ∃ step : Fin 2,
    aligned.toInterface.localLayerPrefixCrossing step ∈
      aligned.localLayerLeftFactorEdges fragment factor

/-- The unique bounded alternative to incoming cut incidence. -/
def LocalLayerLeftFactorContainsSharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) : Prop :=
  aligned.toInterface.localLayerSharedRungEdge ∈
    aligned.localLayerLeftFactorEdges fragment factor

/-- The factor's exact edge support occurs at an incoming profile
coordinate. -/
def LocalLayerLeftFactorHasProfileCoordinate
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) : Prop :=
  ∃ index : aligned.LocalLayerLeftBoundaryIndex,
    aligned.localLayerLeftBoundaryFragmentEdgesAt index =
      aligned.localLayerLeftFactorEdges fragment factor

/-- Specialized support witness for one old-prefix factor. -/
abbrev LocalLayerLeftFactorBoundaryWitness
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment) :=
  BoundaryFragmentSupportWitness
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing)
    aligned.toInterface.localLayerLeftPrefixRegion
    (aligned.localLayerLeftFactorEdges fragment factor) fragment.1.1

/-- Package an old-prefix factor as an incoming boundary fragment from one
literal incoming crossing in its support. -/
noncomputable def localLayerLeftFactorBoundaryWitnessOfTouch
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (step : Fin 2)
    (htouch : aligned.toInterface.localLayerPrefixCrossing step ∈
      aligned.localLayerLeftFactorEdges fragment factor) :
    aligned.LocalLayerLeftFactorBoundaryWitness fragment factor := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let cut := indexedCrossingEdgeSet interface.localLayerPrefixCrossing
  let region := interface.localLayerLeftPrefixRegion
  have hedgeCut : interface.localLayerPrefixCrossing step ∈ cut :=
    (mem_indexedCrossingEdgeSet_iff interface.localLayerPrefixCrossing
      (interface.localLayerPrefixCrossing step)).2 ⟨step, rfl⟩
  have hedgeFace : interface.localLayerPrefixCrossing step ∈
      orbitFaceBoundary RS fragment.1.1 := by
    have hboundary :=
      faceRegionalFragmentEdges_subset_boundary_inter_region RS root region
        factor htouch
    simpa [root] using (Finset.mem_inter.1 hboundary).1
  let face : CutIncidentFace RS cut :=
    ⟨fragment.1.1,
      (mem_cutIncidentFaces_iff RS cut fragment.1.1).2
        ⟨interface.localLayerPrefixCrossing step, hedgeCut, hedgeFace⟩⟩
  exact boundaryFragmentSupportWitnessOf RS cut region face factor
    ⟨interface.localLayerPrefixCrossing step, htouch, hedgeCut⟩

/-- A touched factor therefore occurs at a genuine incoming finite-profile
coordinate. -/
theorem localLayerLeftFactorHasProfileCoordinate_of_touchesPrefixCut
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (htouches : aligned.LocalLayerLeftFactorTouchesPrefixCut fragment factor) :
    aligned.LocalLayerLeftFactorHasProfileCoordinate fragment factor := by
  rcases htouches with ⟨step, htouch⟩
  let witness := aligned.localLayerLeftFactorBoundaryWitnessOfTouch
    fragment factor step htouch
  exact witness.exists_index

/-- Every contributing old-prefix factor is represented by an incoming
finite-profile coordinate or is the explicit shared-rung residue. -/
theorem localLayerLeftFactorHasProfileCoordinate_or_containsSharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (factor : aligned.LocalLayerLeftFactor fragment)
    (hfactor : factor ∈ aligned.localLayerLeftFactorFragments fragment) :
    aligned.LocalLayerLeftFactorHasProfileCoordinate fragment factor ∨
      aligned.LocalLayerLeftFactorContainsSharedRung fragment factor := by
  rcases aligned
      |>.localLayerLeftFactorFragment_touches_prefixCut_or_contains_sharedRung
        hcubic hrotation fragment factor hfactor with
    hcut | hshared
  · exact Or.inl
      (aligned.localLayerLeftFactorHasProfileCoordinate_of_touchesPrefixCut
        fragment factor hcut)
  · exact Or.inr hshared

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
