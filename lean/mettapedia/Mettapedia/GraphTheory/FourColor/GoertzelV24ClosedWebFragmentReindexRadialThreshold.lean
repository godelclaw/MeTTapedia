import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialOrderDichotomy
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebProfileFiniteness
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedSerialBaseThreshold

/-!
# Fragment-reindexed radial-order threshold

The literal heterogeneous serial word has a lossless width-two profile
quotient with `105744` states: it forgets only the arbitrary enumeration of
face fragments, and equality in the quotient returns the explicit fragment
permutation accepted by the splice interface.  Its separated-repeat block
length is therefore the checked numeral `422980`.

This module substitutes that route-correct block length into the uniform
curvature-free radial-order theorem.  A five-by-five closed web above the
checked total-vertex threshold `845970` consequently constructs the source's
length/depth alternative, with the depth request calibrated to the existing
finite depth-profile carrier.

This is an arithmetic L6/L7 connector, not `V0`, `BaseVerified`, or a strict
reduction supplier.  The shallow radial cuts still need realization as the
literal serial layer boundaries, and the selected laminar sector still needs
genuine deletion transversals before either branch supplies a splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebFragmentReindexRadialThreshold

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebRadialOrderDichotomy
open GoertzelV24ClosedWebSectorAlternation
open GoertzelV24FramedSerialBaseThreshold
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The route-correct fragment-reindexed serial repeat length, reused as the
length coordinate in the curvature-free radial-order dichotomy. -/
def fragmentReindexRadialBlockLength : Nat :=
  separatedFragmentReindexSerialProfileBlockLength

theorem fragmentReindexRadialBlockLength_eq :
    fragmentReindexRadialBlockLength = 422980 := by
  exact separatedFragmentReindexSerialProfileBlockLength_eq

theorem fragmentReindexRadialBlockLength_pos :
    0 < fragmentReindexRadialBlockLength := by
  exact separatedFragmentReindexSerialProfileBlockLength_pos

/-- Uniform interior-vertex threshold calibrated to the lossless serial
fragment quotient. -/
def fragmentReindexRadialVertexThreshold : Nat :=
  radialOrderLengthDepthVertexThreshold fragmentReindexRadialBlockLength

theorem fragmentReindexRadialVertexThreshold_eq :
    fragmentReindexRadialVertexThreshold = 845960 := by
  rw [fragmentReindexRadialVertexThreshold,
    radialOrderLengthDepthVertexThreshold,
    fragmentReindexRadialBlockLength_eq]

/-- Total-vertex threshold for a five-by-five closed web.  The ten boundary
stubs are added by exact partition accounting, not by an estimate. -/
def fragmentReindexClosedWebVertexThreshold : Nat :=
  fragmentReindexRadialVertexThreshold + 10

theorem fragmentReindexClosedWebVertexThreshold_eq :
    fragmentReindexClosedWebVertexThreshold = 845970 := by
  rw [fragmentReindexClosedWebVertexThreshold,
    fragmentReindexRadialVertexThreshold_eq]

/-- Above the total threshold, the exact ten-stub partition puts the interior
above the radial-order threshold. -/
theorem interiorVertices_large_of_fragmentReindexClosedWebVertices_large
    {data : AnnularBoundaryData G 5}
    (hdata : data.WellFormed)
    (hlarge : fragmentReindexClosedWebVertexThreshold < Fintype.card V) :
    fragmentReindexRadialVertexThreshold < data.interiorVertices.card := by
  have hpartition :
      data.interiorVertices.card + data.boundaryStubVertices.card =
        Fintype.card V := by
    simpa [AnnularBoundaryData.interiorVertices] using
      (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ data.boundaryStubVertices))
  have hboundary : data.boundaryStubVertices.card = 10 := by
    simpa using data.boundaryStubVertices_card hdata
  rw [hboundary] at hpartition
  unfold fragmentReindexClosedWebVertexThreshold at hlarge
  omega

/-- **L6/L7 arithmetic connector.**  Above the quotient-calibrated interior
threshold, the actual L8 witness satisfies the source length/depth alternative.
The length branch has exactly the clean span required by the proved separated
fragment-reindex repeat, while the depth branch requests the existing finite
depth-profile count at `widthBound`.

No layer-boundary or deletion-transversal realization is asserted here. -/
theorem Instance.exists_radialWitness_with_fragmentReindexOutcome
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (widthBound : Nat)
    (hlarge : fragmentReindexRadialVertexThreshold <
      data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            (fragmentReindexRadialBlockLength - 1),
          RadialOrderLengthDepthOutcome web.annular
                web.boundary_wellFormed witness.pair htriple
                (closedWebCutProfileCount widthBound)
                fragmentReindexRadialBlockLength ∨
            RadialOrderLengthDepthOutcome web.annular
              web.boundary_wellFormed (swapRadialPathPair witness.pair)
                htriple (closedWebCutProfileCount widthBound)
                fragmentReindexRadialBlockLength := by
  apply Instance.exists_radialWitness_with_orderLengthDepthOutcome_of_threshold
    web (closedWebCutProfileCount widthBound)
      fragmentReindexRadialBlockLength
      fragmentReindexRadialBlockLength_pos
  exact hlarge

/-- Total-size form of the same quotient-calibrated entrance. -/
theorem Instance.exists_radialWitness_with_fragmentReindexOutcome_of_card
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (widthBound : Nat)
    (hlarge : fragmentReindexClosedWebVertexThreshold < Fintype.card V) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            (fragmentReindexRadialBlockLength - 1),
          RadialOrderLengthDepthOutcome web.annular
                web.boundary_wellFormed witness.pair htriple
                (closedWebCutProfileCount widthBound)
                fragmentReindexRadialBlockLength ∨
            RadialOrderLengthDepthOutcome web.annular
              web.boundary_wellFormed (swapRadialPathPair witness.pair)
                htriple (closedWebCutProfileCount widthBound)
                fragmentReindexRadialBlockLength := by
  exact Instance.exists_radialWitness_with_fragmentReindexOutcome
    web widthBound
    (interiorVertices_large_of_fragmentReindexClosedWebVertices_large
      web.boundary_wellFormed hlarge)

end

end GoertzelV24ClosedWebFragmentReindexRadialThreshold

end Mettapedia.GraphTheory.FourColor
