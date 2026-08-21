import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSupportResolution
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixThreeFaceBound

/-!
# A source Cell has at most one old-prefix factor per outgoing face

The coherent face-cap relation previously chose a coordinate for every
graph-dependent old-prefix factor.  For a literal source Cell, that apparent
multiplicity is spurious: the factors contributing to one outgoing boundary
fragment form a subsingleton.

Two cut-touching factors have incoming boundary fragments on the same ambient
face, hence the same support.  Two shared-rung residues both have the singleton
rung support.  The mixed case is impossible because a residue identifies the
ambient face with the new central hexagon, while an incoming cut edge is
disjoint from that hexagon's boundary.

This is the geometric compression needed before replacing the dependent
factor assignment by a fixed finite face-attachment code.  It does not yet
construct that code or a complete five-coordinate transition.
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

local instance framedCorridorPrefixFactorSubsingletonEdgeSetDecidableEq :
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

/-- Two old-prefix factors with equal literal edge support are the same
regional connected component. -/
theorem localLayerLeftFactor_eq_of_edges_eq
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (left right : aligned.LocalLayerLeftFactor fragment)
    (hedges : aligned.localLayerLeftFactorEdges fragment left =
      aligned.localLayerLeftFactorEdges fragment right) :
    left = right := by
  by_contra hne
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  let region := aligned.toInterface.localLayerLeftPrefixRegion
  have hdisjoint := disjoint_faceRegionalFragmentEdges_of_ne
    RS htwoSided root region hne
  change faceRegionalFragmentEdges RS root region left =
    faceRegionalFragmentEdges RS root region right at hedges
  rcases faceRegionalFragmentEdges_nonempty RS root region left with
    ⟨edge, hedge⟩
  have hedgeRight : edge ∈ faceRegionalFragmentEdges RS root region right := by
    rw [← hedges]
    exact hedge
  exact (Finset.disjoint_left.1 hdisjoint) hedge hedgeRight

/-- Once one contributing factor is the shared-rung residue, no contributing
factor on the same outgoing face can carry an incoming profile coordinate. -/
theorem not_localLayerLeftFactorHasProfileFragmentCoordinate_of_sharedRung
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (profileFactor residueFactor : aligned.LocalLayerLeftFactor fragment)
    (hcoordinate :
      aligned.LocalLayerLeftFactorHasProfileFragmentCoordinate
        fragment profileFactor)
    (hshared :
      aligned.LocalLayerLeftFactorContainsSharedRung fragment residueFactor) :
    False := by
  let interface := aligned.toInterface
  let RS := embedded.cellulation.rotation.toRotationSystem
  let cut := indexedCrossingEdgeSet interface.localLayerPrefixCrossing
  let region := interface.localLayerLeftPrefixRegion
  rcases hcoordinate with ⟨index, hface, _⟩
  let inputFragment := aligned.localLayerLeftBoundaryFragmentAt index
  let edge := boundaryRegionalFragmentCutEdge RS cut region inputFragment
  have hedgeCut : edge ∈ cut :=
    boundaryRegionalFragmentCutEdge_mem_cut RS cut region inputFragment
  rcases (mem_indexedCrossingEdgeSet_iff
      interface.localLayerPrefixCrossing edge).1 hedgeCut with
    ⟨step, hstep⟩
  have hedgeInputFace : edge ∈ orbitFaceBoundary RS inputFragment.1.1 := by
    exact (Finset.mem_inter.1
      (boundaryRegionalFragmentEdges_subset_boundary_inter_region
        RS cut region inputFragment
        (boundaryRegionalFragmentCutEdge_mem_fragment
          RS cut region inputFragment))).1
  have hresidueFace :
      fragment.1.1 = interface.nextCenterLayerFace.1 :=
    aligned.localLayerLeftFactor_face_eq_nextCenter_of_containsSharedRung
      fragment residueFactor hshared
  have hedgeNextCenter :
      edge ∈ orbitFaceBoundary RS interface.nextCenterLayerFace.1 := by
    simpa [inputFragment, hface, hresidueFace] using hedgeInputFace
  have hedgeCell : edge ∈ interface.localLayerCellBoundaryRegion := by
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion, RS]
      using hedgeNextCenter
  rw [← hstep] at hedgeCell
  exact aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion step
    hedgeCell

/-- The contributing old-prefix factors of one literal outgoing fragment are
subsingleton.  This is the load-bearing removal of the ambient factor carrier
from the future finite transition alphabet. -/
theorem localLayerLeftFactorFragments_card_le_one
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    (aligned.localLayerLeftFactorFragments fragment).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro left right hleft hright
  rcases aligned
      |>.localLayerLeftFactorHasProfileFragmentCoordinate_or_containsSharedRung
        hcubic hrotation fragment left hleft with
    hleftCoordinate | hleftShared
  · rcases aligned
        |>.localLayerLeftFactorHasProfileFragmentCoordinate_or_containsSharedRung
          hcubic hrotation fragment right hright with
      hrightCoordinate | hrightShared
    · rcases hleftCoordinate with
        ⟨leftIndex, hleftFace, hleftEdges⟩
      rcases hrightCoordinate with
        ⟨rightIndex, hrightFace, hrightEdges⟩
      have hfragments :
          aligned.localLayerLeftBoundaryFragmentAt leftIndex =
            aligned.localLayerLeftBoundaryFragmentAt rightIndex := by
        apply aligned.toInterface.localLayerPrefixBoundaryFragment_face_injective
        apply Subtype.ext
        exact hleftFace.trans hrightFace.symm
      have hinputEdges :
          aligned.localLayerLeftBoundaryFragmentEdgesAt leftIndex =
            aligned.localLayerLeftBoundaryFragmentEdgesAt rightIndex := by
        unfold localLayerLeftBoundaryFragmentEdgesAt
        rw [hfragments]
      exact aligned.localLayerLeftFactor_eq_of_edges_eq fragment left right
        (hleftEdges.symm.trans (hinputEdges.trans hrightEdges))
    · exact False.elim
        (aligned
          |>.not_localLayerLeftFactorHasProfileFragmentCoordinate_of_sharedRung
            fragment left right hleftCoordinate hrightShared)
  · rcases aligned
        |>.localLayerLeftFactorHasProfileFragmentCoordinate_or_containsSharedRung
          hcubic hrotation fragment right hright with
      hrightCoordinate | hrightShared
    · exact False.elim
        (aligned
          |>.not_localLayerLeftFactorHasProfileFragmentCoordinate_of_sharedRung
            fragment right left hrightCoordinate hleftShared)
    · exact aligned.localLayerLeftFactor_eq_of_edges_eq fragment left right
        ((aligned.localLayerLeftFactorEdges_eq_singleton_of_containsSharedRung
            fragment left hleftShared).trans
          (aligned.localLayerLeftFactorEdges_eq_singleton_of_containsSharedRung
            fragment right hrightShared).symm)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
