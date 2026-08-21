import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialOrderDichotomy
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat

/-!
# Profile-calibrated radial-order threshold

The curvature-free L6 entrance can now be calibrated directly against the
proved L7 carrier.  We use the exact separated source-profile block length
`764740`, after the proved three-face bound, and use
`closedWebCutProfileCount widthBound` as the requested laminar depth.  Thus a
closed web with more than `1529480` interior vertices
constructs an actual radial witness having one of the two source coordinates:

* a block of `764740` consecutive radial cuts, each with actual chord load at
  most twice the selected L7 carrier count; or
* one rotation sector containing more than that L7 carrier count of
  pairwise-laminar chords.

This is the numerical **L6/L7** connector, not `V₀`, `BaseVerified`, or a
strict-reduction supplier.  The shallow cuts still need source-local simple
layer boundaries, and the laminar chords still need source layer-boundary or
deletion-transversal realizations before the profile equality can be spliced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebProfileCalibratedRadialOrder

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebRadialOrderDichotomy
open GoertzelV24ClosedWebSectorAlternation
open GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The exact gap-at-least-four source-profile block length, expressed only
through the lossless L7 carrier rather than the heavier corridor tower. -/
def profileCalibratedBlockLength : Nat :=
  4 * boundedWidthTwoPortIncidenceProfileCount 3 + 4

/-- The source-profile block length is a checked numeral. -/
theorem profileCalibratedBlockLength_eq :
    profileCalibratedBlockLength = 764740 := by
  rw [profileCalibratedBlockLength,
    boundedWidthTwoPortIncidenceProfileCount_three]

/-- The first explicit curvature-free interior-vertex threshold calibrated to
the lossless separated source-profile carrier. -/
def separatedProfileRadialVertexThreshold : Nat :=
  radialOrderLengthDepthVertexThreshold profileCalibratedBlockLength

/-- The threshold is a checked numeral, not an opaque profile expression. -/
theorem separatedProfileRadialVertexThreshold_eq :
    separatedProfileRadialVertexThreshold = 1529480 := by
  rw [separatedProfileRadialVertexThreshold,
    radialOrderLengthDepthVertexThreshold,
    profileCalibratedBlockLength_eq]

/-- Total-vertex threshold for a five-by-five closed web.  The annular
carrier has exactly ten boundary stubs, so this is the interior threshold
plus ten rather than a new geometric estimate. -/
def separatedProfileClosedWebVertexThreshold : Nat :=
  separatedProfileRadialVertexThreshold + 10

/-- The total closed-web threshold is a checked numeral. -/
theorem separatedProfileClosedWebVertexThreshold_eq :
    separatedProfileClosedWebVertexThreshold = 1529490 := by
  rw [separatedProfileClosedWebVertexThreshold,
    separatedProfileRadialVertexThreshold_eq]

/-- Above the total five-by-five closed-web threshold, the interior exceeds
the radial L6/L7 threshold.  This is the exact accounting bridge from the
finite carrier to the source's `interiorVertices`; it is not yet the final
whole-route `V₀`. -/
theorem interiorVertices_large_of_closedWebVertices_large
    {data : AnnularBoundaryData G 5}
    (hdata : data.WellFormed)
    (hlarge : separatedProfileClosedWebVertexThreshold < Fintype.card V) :
    separatedProfileRadialVertexThreshold < data.interiorVertices.card := by
  have hpartition :
      data.interiorVertices.card + data.boundaryStubVertices.card =
        Fintype.card V := by
    simpa [AnnularBoundaryData.interiorVertices] using
      (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ data.boundaryStubVertices))
  have hboundary : data.boundaryStubVertices.card = 10 := by
    simpa using data.boundaryStubVertices_card hdata
  rw [hboundary] at hpartition
  unfold separatedProfileClosedWebVertexThreshold at hlarge
  omega

/-- **L6/L7 arithmetic connector.** Above the checked radial-order threshold,
the actual L8 witness satisfies the length/depth alternative with its depth
request set to the exact finite L7 profile count at `widthBound`.

No side assignment or splice is assumed here: the conclusion is the literal
source geometry constructed by L6. -/
theorem Instance.exists_radialWitness_with_profileCalibratedOutcome
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (widthBound : Nat)
    (hlarge : separatedProfileRadialVertexThreshold <
      data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            (profileCalibratedBlockLength - 1),
          RadialOrderLengthDepthOutcome web.annular
                web.boundary_wellFormed witness.pair htriple
                (closedWebCutProfileCount widthBound)
                profileCalibratedBlockLength ∨
            RadialOrderLengthDepthOutcome web.annular
              web.boundary_wellFormed (swapRadialPathPair witness.pair)
                htriple (closedWebCutProfileCount widthBound)
                profileCalibratedBlockLength := by
  apply Instance.exists_radialWitness_with_orderLengthDepthOutcome_of_threshold
    web (closedWebCutProfileCount widthBound)
      profileCalibratedBlockLength
      (by rw [profileCalibratedBlockLength_eq]; omega)
  exact hlarge

/-- Total-size form of the L6/L7 entrance for a five-by-five closed web.
The ten boundary stubs are discharged by the exact partition above. -/
theorem Instance.exists_radialWitness_with_profileCalibratedOutcome_of_card
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (widthBound : Nat)
    (hlarge : separatedProfileClosedWebVertexThreshold < Fintype.card V) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            (profileCalibratedBlockLength - 1),
          RadialOrderLengthDepthOutcome web.annular
                web.boundary_wellFormed witness.pair htriple
                (closedWebCutProfileCount widthBound)
                profileCalibratedBlockLength ∨
            RadialOrderLengthDepthOutcome web.annular
              web.boundary_wellFormed (swapRadialPathPair witness.pair)
                htriple (closedWebCutProfileCount widthBound)
                profileCalibratedBlockLength := by
  exact Instance.exists_radialWitness_with_profileCalibratedOutcome
    web widthBound
    (interiorVertices_large_of_closedWebVertices_large
      web.boundary_wellFormed hlarge)

end

end GoertzelV24ClosedWebProfileCalibratedRadialOrder

end Mettapedia.GraphTheory.FourColor
