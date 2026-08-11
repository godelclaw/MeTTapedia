import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementSerialOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionSerialTangleColoring

/-!
# Coloring semantics of the complementary source Cell

The complementary source Cell has two literal presentations: an open-region
rotation system with fresh degree-one stubs, and a serial open tangle with
unpaired left and right ports.  This file identifies their Tait colorings and
proves that the displayed port colors are exactly the manuscript's ordered
left and right boundary words.

The identification follows physical ambient edges.  It does not replace the
full profile by its color coordinate, assert equality of successive profiles,
or assemble a global corridor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionColorGluing
open GoertzelV24OpenRegionSerialTangleColoring
open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The complementary boundary dart selected by the source coordinate is
literally the opposite ambient dart of the retained-side source port. -/
theorem sourceCrosscutComplementBoundaryDartAt_eq_alpha_source
    (data : Data G)
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
    (index : pair.SourceCrosscutBoundaryIndex) :
    (pair.sourceCrosscutComplementBoundaryDartAt data boundary index).1.1 =
      data.toRotationSystem.alpha
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1 := by
  let source := pair.sourceCrosscutBoundaryDartAt data boundary index
  let opposite : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
    ⟨⟨data.toRotationSystem.alpha source.1.1, source.2⟩, by
      intro houtside
      apply houtside
      simpa only [data.toRotationSystem.alpha_involutive] using source.1.2⟩
  have heq :
      pair.sourceCrosscutComplementBoundaryDartAt data boundary index =
        opposite := by
    apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
    calc
      data.toRotationSystem.edgeOf
          (pair.sourceCrosscutComplementBoundaryDartAt data boundary index).1.1 =
          (pair.sourceCrosscutPort data boundary index).1 :=
        pair.sourceCrosscutComplementBoundaryDartAt_edgeOf data boundary index
      _ = data.toRotationSystem.edgeOf source.1.1 :=
        (pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary index).symm
      _ = data.toRotationSystem.edgeOf
          (data.toRotationSystem.alpha source.1.1) :=
        (data.toRotationSystem.edge_alpha source.1.1).symm
      _ = data.toRotationSystem.edgeOf opposite.1.1 := rfl
  exact congrArg
    (fun dart : BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) => dart.1.1)
    heq

/-- Read one literal complementary open-region coloring on the source Cell's
serial open-tangle carrier. -/
noncomputable def sourceCrosscutComplementSerialColoring
    (data : Data G)
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color) :
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring :=
  splitVertexSideColoring data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)
    (pair.sourceCrosscutComplementBoundarySplit data boundary) coloring

/-- A literal complementary open-region Tait coloring remains Tait on the
source Cell's serial presentation. -/
theorem sourceCrosscutComplementSerialColoring_isTait
    (data : Data G)
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color)
    (hcoloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
        coloring) :
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
        (pair.sourceCrosscutComplementSerialColoring data boundary hcubic coloring) := by
  exact splitVertexSideColoring_isTait data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)
    (pair.sourceCrosscutComplementBoundarySplit data boundary) coloring hcoloring

/-- The serial presentation's input colors are exactly the literal left
source boundary word, position for position. -/
@[simp]
theorem sourceCrosscutComplementSerialColoring_leftBoundaryColor
    (data : Data G)
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color)
    (step : Fin pair.left.walk.length) :
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).leftBoundaryColor
          (pair.sourceCrosscutComplementSerialColoring data boundary hcubic coloring) step =
      pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring step := by
  change
    openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (pair.sourceCrosscutComplementBoundaryDartAt data boundary (.inl step)).1.1 _ =
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (data.toRotationSystem.alpha
          (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step)).1.1) _
  apply openOldDartColor_eq_of_dart_eq
  exact pair.sourceCrosscutComplementBoundaryDartAt_eq_alpha_source data boundary
    (.inl step)

/-- The serial presentation's output colors are exactly the literal right
source boundary word, position for position. -/
@[simp]
theorem sourceCrosscutComplementSerialColoring_rightBoundaryColor
    (data : Data G)
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
    (hcubic : data.toRotationSystem.IsCubic)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color)
    (step : Fin pair.right.walk.length) :
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).rightBoundaryColor
          (pair.sourceCrosscutComplementSerialColoring data boundary hcubic coloring) step =
      pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring step := by
  change
    openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (pair.sourceCrosscutComplementBoundaryDartAt data boundary (.inr step)).1.1 _ =
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (data.toRotationSystem.alpha
          (pair.sourceCrosscutBoundaryDartAt data boundary (.inr step)).1.1) _
  apply openOldDartColor_eq_of_dart_eq
  exact pair.sourceCrosscutComplementBoundaryDartAt_eq_alpha_source data boundary
    (.inr step)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
