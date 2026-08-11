import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceCapUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideBoundaryFragmentCoverage

/-!
# Source factor fragments as finite-profile coordinates

The relational face-update law decomposes one composed face fragment into
connected fragments on the retained and removed vertex sides.  A finite
corridor profile, however, indexes only boundary fragments: fragments of a
cut-incident face whose support meets the corresponding vertex cut.

For the literal source crosscut these two descriptions agree.  On either
vertex side, every fragment of a cut-incident face has a canonical coordinate
in that side's graph-derived cut data.  Consequently its cap-at-five value is
an actual `CorridorCutProfile.faceLengthCap` coordinate, not an auxiliary raw
cardinality.

This file deliberately keeps the retained and removed carriers separate.
It does not identify arbitrary internal face fragments with boundary-profile
coordinates; cut incidence is an explicit input to every conversion below.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TerminalProfileFaceCapUpdate
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

/-! ## Removed-side cut-data validity -/

/-- The complementary source-interface data uses exactly the computed open
fragments of the removed vertex side. -/
theorem sourceCrosscutComplementCutData_fragmentsOnFaceInRegion
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    (pair.sourceCrosscutComplementCutData data boundary
      crossingEdge).FragmentsOnFaceInRegion := by
  intro fragment
  exact boundaryRegionalFragmentEdges_subset_boundary_inter_region
    data.toRotationSystem
    (vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ)
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ)
    (boundaryRegionalFragmentAt data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) fragment)

/-! ## Retained factor fragments -/

/-- A retained-side factor fragment together with its cut-incident ambient
face.  Packaging the dependent pair keeps later source-specialized theorem
signatures small while retaining the occurrence-sensitive face identity. -/
abbrev SourceCrosscutRetainedFactorFragment :=
  Σ face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)),
    FaceRegionalFragment data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))

/-- Actual edge support of a retained source factor fragment. -/
def sourceCrosscutRetainedFactorFragmentEdges
    (item : SourceCrosscutRetainedFactorFragment data pair boundary) :
    Finset G.edgeSet :=
  faceRegionalFragmentEdges data.toRotationSystem
    (orbitFaceRoot data.toRotationSystem item.1.1)
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)) item.2

/-- The occurrence-sensitive cap recorded for a retained factor fragment. -/
def sourceCrosscutRetainedFactorFragmentPositionCap
    (item : SourceCrosscutRetainedFactorFragment data pair boundary) : Nat :=
  min (faceRegionalFragmentPositions data.toRotationSystem
    (orbitFaceRoot data.toRotationSystem item.1.1)
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)) item.2).card 5

/-- A raw retained-side fragment of a cut-incident face occurs at a genuine
fragment coordinate of the source cut data. -/
theorem exists_sourceCrosscutRetainedFactorFragmentIndex
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRetainedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    ∃ index : Fin (pair.sourceCrosscutFaceFragmentCount data boundary),
      (pair.sourceCrosscutCutData data boundary crossingEdge).fragmentEdges
          index = sourceCrosscutRetainedFactorFragmentEdges
            data pair boundary item := by
  rcases exists_boundaryRegionalFragmentAt_eq_cutIncidentFaceFragment
      data.toRotationSystem hcubic hrotation htwoSided
      (pair.componentSide boundary.component) item.1 item.2 with
    ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  change boundaryRegionalFragmentEdges data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (boundaryRegionalFragmentAt data.toRotationSystem
        (vertexSetCrossingEdges data.toRotationSystem
          (pair.componentSide boundary.component))
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)) index) = _
  rw [hindex]
  rfl

/-- The cap of a retained factor fragment is therefore literally available
as one coordinate of every graph-derived source profile on that interface. -/
theorem exists_sourceCrosscutRetainedProfileFaceLengthCap
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRetainedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    ∃ index : Fin (pair.sourceCrosscutFaceFragmentCount data boundary),
      (((pair.sourceCrosscutCutData data boundary crossingEdge).profile
          coloring hcoloring).faceLengthCap index).val =
        sourceCrosscutRetainedFactorFragmentPositionCap
          data pair boundary item := by
  rcases pair.exists_sourceCrosscutRetainedFactorFragmentIndex data boundary
      hcubic hrotation htwoSided item crossingEdge with
    ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  rw [GraphCorridorCutData.profile_faceLengthCap_val]
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    _ (pair.sourceCrosscutCutData_fragmentsOnFaceInRegion data boundary
      crossingEdge)]
  rw [hindex]
  simpa [sourceCrosscutRetainedFactorFragmentEdges,
    sourceCrosscutRetainedFactorFragmentPositionCap] using
    (min_card_faceRegionalFragmentEdges_eq_positions
      data.toRotationSystem htwoSided
      (orbitFaceRoot data.toRotationSystem item.1.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)) item.2 5)

/-! ## Removed factor fragments -/

/-- A removed-side factor fragment together with its cut-incident ambient
face.  Its carrier remains distinct from the retained-side carrier. -/
abbrev SourceCrosscutRemovedFactorFragment :=
  Σ face : CutIncidentFace data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ),
    FaceRegionalFragment data.toRotationSystem
      (orbitFaceRoot data.toRotationSystem face.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)

/-- Actual edge support of a removed source factor fragment. -/
def sourceCrosscutRemovedFactorFragmentEdges
    (item : SourceCrosscutRemovedFactorFragment data pair boundary) :
    Finset G.edgeSet :=
  faceRegionalFragmentEdges data.toRotationSystem
    (orbitFaceRoot data.toRotationSystem item.1.1)
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) item.2

/-- The occurrence-sensitive cap recorded for a removed factor fragment. -/
def sourceCrosscutRemovedFactorFragmentPositionCap
    (item : SourceCrosscutRemovedFactorFragment data pair boundary) : Nat :=
  min (faceRegionalFragmentPositions data.toRotationSystem
    (orbitFaceRoot data.toRotationSystem item.1.1)
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) item.2).card 5

/-- A raw removed-side fragment of a cut-incident face occurs at a genuine
fragment coordinate of the complementary source cut data. -/
theorem exists_sourceCrosscutRemovedFactorFragmentIndex
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRemovedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    ∃ index : Fin
        (pair.sourceCrosscutComplementFaceFragmentCount data boundary),
      (pair.sourceCrosscutComplementCutData data boundary crossingEdge).fragmentEdges
          index = sourceCrosscutRemovedFactorFragmentEdges
            data pair boundary item := by
  rcases exists_boundaryRegionalFragmentAt_eq_cutIncidentFaceFragment
      data.toRotationSystem hcubic hrotation htwoSided
      (pair.componentSide boundary.component)ᶜ item.1 item.2 with
    ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  change boundaryRegionalFragmentEdges data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (boundaryRegionalFragmentAt data.toRotationSystem
        (vertexSetCrossingEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ) index) = _
  rw [hindex]
  rfl

/-- The cap of a removed factor fragment is one coordinate of the actual
complementary source profile, on its own (not retained-side) carrier. -/
theorem exists_sourceCrosscutRemovedProfileFaceLengthCap
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (item : SourceCrosscutRemovedFactorFragment data pair boundary)
    {width : Nat} (crossingEdge : Fin width → G.edgeSet)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    ∃ index : Fin
        (pair.sourceCrosscutComplementFaceFragmentCount data boundary),
      (((pair.sourceCrosscutComplementCutData data boundary crossingEdge).profile
          coloring hcoloring).faceLengthCap index).val =
        sourceCrosscutRemovedFactorFragmentPositionCap
          data pair boundary item := by
  rcases pair.exists_sourceCrosscutRemovedFactorFragmentIndex data boundary
      hcubic hrotation htwoSided item crossingEdge with
    ⟨index, hindex⟩
  refine ⟨index, ?_⟩
  rw [GraphCorridorCutData.profile_faceLengthCap_val]
  rw [GraphCorridorCutData.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
    _ (pair.sourceCrosscutComplementCutData_fragmentsOnFaceInRegion
      data boundary crossingEdge)]
  rw [hindex]
  simpa [sourceCrosscutRemovedFactorFragmentEdges,
    sourceCrosscutRemovedFactorFragmentPositionCap] using
    (min_card_faceRegionalFragmentEdges_eq_positions
      data.toRotationSystem htwoSided
      (orbitFaceRoot data.toRotationSystem item.1.1)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) item.2 5)

end SourceCrosscut

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
