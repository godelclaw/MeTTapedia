import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutFactorBoundaryFragments
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutTerminalProfileCoverage

/-!
# Canonical source factor-profile cap coordinates

The retained and removed vertex sides see the same geometric edge cut.  This
file transports cut-incidence across that equality and assigns every
cut-incident factor fragment a canonical finite-profile coordinate on its own
side.  The coordinate is the existing `Fintype.equivFin` enumeration of the
proved boundary-fragment equivalence; no new profile data is introduced.

These canonical coordinates are the form needed to rewrite the finite sums in
the relational face-cap update through the actual input profiles.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceSliceFragments
open GoertzelV24VertexSideBoundaryFragmentCoverage
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

section SourceCrosscut

variable (data : Data G)
  {start finish : AmbientFace
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
  (pair : SeparatedAlignedSimpleDualCrosscuts
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))
    start finish hunique)
  (boundary : SourceCrosscutBoundaryData data pair)

/-! ## The same incident face seen from either vertex side -/

/-- A face incident to the retained vertex cut is incident to the removed
vertex cut as well, because complementing a vertex side does not change its
crossing-edge set. -/
def sourceCrosscutComplementCutIncidentFace
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))) :
    CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) :=
  ⟨face.1, by
    simpa only [vertexSetCrossingEdges_compl] using face.2⟩

@[simp]
theorem sourceCrosscutComplementCutIncidentFace_val
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))) :
    (sourceCrosscutComplementCutIncidentFace data pair boundary face).1 =
      face.1 :=
  rfl

/-- Package a removed-side regional fragment on the same named face as a
retained cut-incidence witness. -/
def sourceCrosscutRemovedFactorFragmentOfRetainedFace
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (fragment : FaceRegionalFragment data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)) :
    SourceCrosscutRemovedFactorFragment data pair boundary :=
  ⟨sourceCrosscutComplementCutIncidentFace data pair boundary face,
    fragment⟩

/-! ## Canonical retained coordinate -/

/-- Canonical finite-profile index of a retained factor fragment. -/
noncomputable def sourceCrosscutRetainedFactorProfileIndex
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRetainedFactorFragment data pair boundary) :
    Fin (pair.sourceCrosscutFaceFragmentCount data boundary) :=
  Fintype.equivFin _
    (cutIncidentFaceRegionalFragmentEquivBoundary data.toRotationSystem
      hcubic hrotation htwoSided (pair.componentSide boundary.component) item)

/-- The retained cut data at the canonical index is the original factor
fragment's literal edge support. -/
theorem sourceCrosscutRetainedFactorProfileIndex_fragmentEdges
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRetainedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    (pair.sourceCrosscutCutData data boundary crossingEdge).fragmentEdges
        (sourceCrosscutRetainedFactorProfileIndex data pair boundary
          hcubic hrotation htwoSided item) =
      sourceCrosscutRetainedFactorFragmentEdges data pair boundary item := by
  have hindex :
      boundaryRegionalFragmentAt data.toRotationSystem
          (vertexSetCrossingEdges data.toRotationSystem
            (pair.componentSide boundary.component))
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component))
          (sourceCrosscutRetainedFactorProfileIndex data pair boundary
            hcubic hrotation htwoSided item) =
        cutIncidentFaceRegionalFragmentEquivBoundary data.toRotationSystem
          hcubic hrotation htwoSided
          (pair.componentSide boundary.component) item := by
    exact (Fintype.equivFin (BoundaryRegionalFragment data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)))).symm_apply_apply _
  change boundaryRegionalFragmentEdges data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (boundaryRegionalFragmentAt data.toRotationSystem
        (vertexSetCrossingEdges data.toRotationSystem
          (pair.componentSide boundary.component))
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component))
        (sourceCrosscutRetainedFactorProfileIndex data pair boundary
          hcubic hrotation htwoSided item)) = _
  rw [hindex]
  rfl

/-- The canonical retained profile coordinate stores exactly the factor's
occurrence-sensitive cap-at-five value. -/
theorem sourceCrosscutRetainedFactorProfileIndex_faceLengthCap
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRetainedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    (((pair.sourceCrosscutCutData data boundary crossingEdge).profile
        coloring hcoloring).faceLengthCap
      (sourceCrosscutRetainedFactorProfileIndex data pair boundary
        hcubic hrotation htwoSided item)).val =
      sourceCrosscutRetainedFactorFragmentPositionCap
        data pair boundary item := by
  rw [GraphCorridorCutData.profile_faceLengthCap_val]
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    _ (pair.sourceCrosscutCutData_fragmentsOnFaceInRegion data boundary
      crossingEdge)]
  rw [pair.sourceCrosscutRetainedFactorProfileIndex_fragmentEdges
    data boundary hcubic hrotation htwoSided item crossingEdge]
  simpa [sourceCrosscutRetainedFactorFragmentEdges,
    sourceCrosscutRetainedFactorFragmentPositionCap] using
    (min_card_faceRegionalFragmentEdges_eq_positions
      data.toRotationSystem htwoSided
      (orbitFaceRoot data.toRotationSystem item.1.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)) item.2 5)

/-! ## Canonical removed coordinate -/

/-- Canonical finite-profile index of a removed factor fragment. -/
noncomputable def sourceCrosscutRemovedFactorProfileIndex
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRemovedFactorFragment data pair boundary) :
    Fin (pair.sourceCrosscutComplementFaceFragmentCount data boundary) :=
  Fintype.equivFin _
    (cutIncidentFaceRegionalFragmentEquivBoundary data.toRotationSystem
      hcubic hrotation htwoSided
      (pair.componentSide boundary.component)ᶜ item)

/-- The removed cut data at the canonical index is the original factor
fragment's literal edge support. -/
theorem sourceCrosscutRemovedFactorProfileIndex_fragmentEdges
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRemovedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    (pair.sourceCrosscutComplementCutData data boundary crossingEdge).fragmentEdges
        (sourceCrosscutRemovedFactorProfileIndex data pair boundary
          hcubic hrotation htwoSided item) =
      sourceCrosscutRemovedFactorFragmentEdges data pair boundary item := by
  have hindex :
      boundaryRegionalFragmentAt data.toRotationSystem
          (vertexSetCrossingEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ)
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ)
          (sourceCrosscutRemovedFactorProfileIndex data pair boundary
            hcubic hrotation htwoSided item) =
        cutIncidentFaceRegionalFragmentEquivBoundary data.toRotationSystem
          hcubic hrotation htwoSided
          (pair.componentSide boundary.component)ᶜ item := by
    exact (Fintype.equivFin (BoundaryRegionalFragment data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ))).symm_apply_apply _
  change boundaryRegionalFragmentEdges data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (boundaryRegionalFragmentAt data.toRotationSystem
        (vertexSetCrossingEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
        (sourceCrosscutRemovedFactorProfileIndex data pair boundary
          hcubic hrotation htwoSided item)) = _
  rw [hindex]
  rfl

/-- The canonical removed profile coordinate stores exactly the factor's
occurrence-sensitive cap-at-five value. -/
theorem sourceCrosscutRemovedFactorProfileIndex_faceLengthCap
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRemovedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    (((pair.sourceCrosscutComplementCutData data boundary crossingEdge).profile
        coloring hcoloring).faceLengthCap
      (sourceCrosscutRemovedFactorProfileIndex data pair boundary
        hcubic hrotation htwoSided item)).val =
      sourceCrosscutRemovedFactorFragmentPositionCap
        data pair boundary item := by
  rw [GraphCorridorCutData.profile_faceLengthCap_val]
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    _ (pair.sourceCrosscutComplementCutData_fragmentsOnFaceInRegion
      data boundary crossingEdge)]
  rw [pair.sourceCrosscutRemovedFactorProfileIndex_fragmentEdges
    data boundary hcubic hrotation htwoSided item crossingEdge]
  simpa [sourceCrosscutRemovedFactorFragmentEdges,
    sourceCrosscutRemovedFactorFragmentPositionCap] using
    (min_card_faceRegionalFragmentEdges_eq_positions
      data.toRotationSystem htwoSided
      (orbitFaceRoot data.toRotationSystem item.1.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) item.2 5)

/-! ## Finite factor sums in profile coordinates -/

/-- The retained input profile's cap value at the canonical coordinate of a
factor fragment. -/
noncomputable def sourceCrosscutRetainedProfileFactorCap
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (item : SourceCrosscutRetainedFactorFragment data pair boundary) : Nat :=
  (((pair.sourceCrosscutCutData data boundary crossingEdge).profile
      coloring hcoloring).faceLengthCap
    (sourceCrosscutRetainedFactorProfileIndex data pair boundary
      hcubic hrotation htwoSided item)).val

/-- The removed input profile's cap value at the canonical coordinate of a
factor fragment. -/
noncomputable def sourceCrosscutRemovedProfileFactorCap
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring)
    (item : SourceCrosscutRemovedFactorFragment data pair boundary) : Nat :=
  (((pair.sourceCrosscutComplementCutData data boundary crossingEdge).profile
      coloring hcoloring).faceLengthCap
    (sourceCrosscutRemovedFactorProfileIndex data pair boundary
      hcubic hrotation htwoSided item)).val

/-- The whole retained factor-fragment sum is a sum of literal cap
coordinates of the retained input profile. -/
theorem sum_sourceCrosscutRetainedProfileFactorCaps_eq
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (largeRegion : Finset G.edgeSet)
    (fragment : FaceRegionalFragment data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1) largeRegion)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    (∑ factorFragment ∈ faceRegionalFactorFragments data.toRotationSystem
          (orbitFaceRoot data.toRotationSystem face.1) largeRegion
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)) fragment,
        sourceCrosscutRetainedProfileFactorCap data pair boundary hcubic
          hrotation htwoSided crossingEdge coloring hcoloring
          ⟨face, factorFragment⟩) =
      ∑ factorFragment ∈ faceRegionalFactorFragments data.toRotationSystem
          (orbitFaceRoot data.toRotationSystem face.1) largeRegion
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)) fragment,
        min (faceRegionalFragmentPositions data.toRotationSystem
          (orbitFaceRoot data.toRotationSystem face.1)
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)) factorFragment).card 5 := by
  apply Finset.sum_congr rfl
  intro factorFragment _hfactor
  simpa [sourceCrosscutRetainedProfileFactorCap,
    sourceCrosscutRetainedFactorFragmentPositionCap] using
    (pair.sourceCrosscutRetainedFactorProfileIndex_faceLengthCap
      data boundary hcubic hrotation htwoSided
      (⟨face, factorFragment⟩ :
        SourceCrosscutRetainedFactorFragment data pair boundary)
      crossingEdge coloring hcoloring)

/-- The whole removed factor-fragment sum is a sum of literal cap coordinates
of the complementary input profile, using the same ambient face witness. -/
theorem sum_sourceCrosscutRemovedProfileFactorCaps_eq
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (largeRegion : Finset G.edgeSet)
    (fragment : FaceRegionalFragment data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1) largeRegion)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    (∑ factorFragment ∈ faceRegionalFactorFragments data.toRotationSystem
          (orbitFaceRoot data.toRotationSystem face.1) largeRegion
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ) fragment,
        sourceCrosscutRemovedProfileFactorCap data pair boundary hcubic
          hrotation htwoSided crossingEdge coloring hcoloring
          (sourceCrosscutRemovedFactorFragmentOfRetainedFace
            data pair boundary face factorFragment)) =
      ∑ factorFragment ∈ faceRegionalFactorFragments data.toRotationSystem
          (orbitFaceRoot data.toRotationSystem face.1) largeRegion
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ) fragment,
        min (faceRegionalFragmentPositions data.toRotationSystem
          (orbitFaceRoot data.toRotationSystem face.1)
          (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ) factorFragment).card 5 := by
  apply Finset.sum_congr rfl
  intro factorFragment _hfactor
  simpa [sourceCrosscutRemovedProfileFactorCap,
    sourceCrosscutRemovedFactorFragmentOfRetainedFace,
    sourceCrosscutRemovedFactorFragmentPositionCap] using
    (pair.sourceCrosscutRemovedFactorProfileIndex_faceLengthCap
      data boundary hcubic hrotation htwoSided
      (sourceCrosscutRemovedFactorFragmentOfRetainedFace
        data pair boundary face factorFragment)
      crossingEdge coloring hcoloring)

/-! ## The source cap update written only in input-profile coordinates -/

/-- A composed face fragment on a source face that meets the paired
transversal cut. -/
abbrev SourceCrosscutComposedFaceFragment
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))) :=
  FaceRegionalFragment data.toRotationSystem
    (orbitFaceRoot data.toRotationSystem face.1)
    (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) ∪
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)

/-- Sum of the retained input-profile cap coordinates that contribute to one
composed source face fragment. -/
noncomputable def sourceCrosscutRetainedProfileFactorCapSum
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (fragment : SourceCrosscutComposedFaceFragment data pair boundary face)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) : Nat :=
  ∑ factorFragment ∈ faceRegionalFactorFragments data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1)
      (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∪
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)) fragment,
    sourceCrosscutRetainedProfileFactorCap data pair boundary hcubic
      hrotation htwoSided (pair.left.crossingEdge hunique) coloring hcoloring
      ⟨face, factorFragment⟩

/-- Sum of the complementary input-profile cap coordinates that contribute
to the same composed source face fragment. -/
noncomputable def sourceCrosscutRemovedProfileFactorCapSum
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (fragment : SourceCrosscutComposedFaceFragment data pair boundary face)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) : Nat :=
  ∑ factorFragment ∈ faceRegionalFactorFragments data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1)
      (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component) ∪
        vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) fragment,
    sourceCrosscutRemovedProfileFactorCap data pair boundary hcubic
      hrotation htwoSided (pair.left.crossingEdge hunique) coloring hcoloring
      (sourceCrosscutRemovedFactorFragmentOfRetainedFace
        data pair boundary face factorFragment)

/-- Number of literal shared face occurrences that inclusion-exclusion must
subtract when the two factor slices are recomposed. -/
def sourceCrosscutFactorFragmentOverlapCard
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (fragment : SourceCrosscutComposedFaceFragment data pair boundary face) : Nat :=
  (faceRegionalFragmentPositionSlice data.toRotationSystem
        (orbitFaceRoot data.toRotationSystem face.1)
        (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component) ∪
          vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ)
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)) fragment ∩
    faceRegionalFragmentPositionSlice data.toRotationSystem
        (orbitFaceRoot data.toRotationSystem face.1)
        (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component) ∪
          vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ)
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ) fragment).card

/-- The occurrence-sensitive source face-cap update, expressed entirely via
the actual retained and complementary input profiles plus the genuine shared
occurrence count.  This is the face-progress coordinate of the relational
one-cell update; it does not choose a deterministic successor profile. -/
theorem sourceCrosscutRetainedRemoved_faceFragmentEdgeCap_eq_profileFactorCaps
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)))
    (fragment : SourceCrosscutComposedFaceFragment data pair boundary face)
    (hwidth : pair.left.walk.length = 2)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    min (faceRegionalFragmentEdges data.toRotationSystem
        (orbitFaceRoot data.toRotationSystem face.1)
        (vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component) ∪
          vertexSetRegionEdges data.toRotationSystem
            (pair.componentSide boundary.component)ᶜ) fragment).card 5 =
      min
        (min (sourceCrosscutRetainedProfileFactorCapSum data pair boundary
              hcubic hrotation htwoSided face fragment coloring hcoloring) 5 +
          min (sourceCrosscutRemovedProfileFactorCapSum data pair boundary
              hcubic hrotation htwoSided face fragment coloring hcoloring) 5 -
          sourceCrosscutFactorFragmentOverlapCard data pair boundary
            face fragment)
        5 := by
  unfold sourceCrosscutRetainedProfileFactorCapSum
    sourceCrosscutRemovedProfileFactorCapSum
    sourceCrosscutFactorFragmentOverlapCard
  rw [pair.sum_sourceCrosscutRetainedProfileFactorCaps_eq data boundary
    hcubic hrotation htwoSided face
    (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) ∪
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
    fragment (pair.left.crossingEdge hunique) coloring hcoloring]
  rw [pair.sum_sourceCrosscutRemovedProfileFactorCaps_eq data boundary
    hcubic hrotation htwoSided face
    (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) ∪
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
    fragment (pair.left.crossingEdge hunique) coloring hcoloring]
  exact pair.sourceCrosscutRetainedRemoved_faceFragmentEdgeCap_eq_factorFragmentCaps
    data boundary htwoSided (orbitFaceRoot data.toRotationSystem face.1)
    fragment hwidth

end SourceCrosscut

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
