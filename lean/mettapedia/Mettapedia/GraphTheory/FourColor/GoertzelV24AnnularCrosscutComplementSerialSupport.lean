import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileBoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementSerialColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialTangleOpenRegionColoring
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleCountSupport

/-!
# Exact support semantics of the complementary source Cell

The source Cell has two literal presentations: the removed open region used
by the existing `Count` matrix, and the two-sided serial open tangle used by
composition.  This file proves that they accept exactly the same ordered
boundary words.  It then transports the established full-profile refinement
to the serial presentation.

Thus the serial-composition algebra is connected to the manuscript's actual
color/connectivity/capped-face profiles.  No homogeneous transfer assumption,
configuration catalogue, or covering-style reduction is introduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24FaceOrbitIncidence
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

/-- Reconstruct a literal removed-region coloring from a coloring of the
source Cell's serial presentation. -/
noncomputable def sourceCrosscutComplementOpenRegionColoringOfSerial
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
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring)
    (hcoloring :
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
        coloring) :
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color :=
  openRegionColoringOfSplitVertexSideColoring data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)
    (pair.sourceCrosscutComplementBoundarySplit data boundary) coloring hcoloring

/-- The reconstructed literal removed-region coloring is Tait. -/
theorem sourceCrosscutComplementOpenRegionColoringOfSerial_isTait
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
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring)
    (hcoloring :
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
        coloring) :
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
        coloring hcoloring) := by
  exact openRegionColoringOfSplitVertexSideColoring_isTait data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)
    (pair.sourceCrosscutComplementBoundarySplit data boundary) coloring hcoloring

/-- Reading a reconstructed literal coloring back through the serial adapter
returns the original source-Cell coloring. -/
theorem sourceCrosscutComplementSerialColoring_openRegionColoringOfSerial
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
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring)
    (hcoloring :
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
        coloring) :
    pair.sourceCrosscutComplementSerialColoring data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) =
      coloring := by
  exact splitVertexSideColoring_openRegionColoringOfSplitVertexSideColoring
    data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)
    (pair.sourceCrosscutComplementBoundarySplit data boundary) coloring hcoloring

/-- The reconstructed literal coloring reads the serial input word exactly. -/
theorem sourceCrosscutComplementOpenRegionColoringOfSerial_leftBoundaryWord
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
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring)
    (hcoloring :
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
        coloring) :
    pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) =
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).leftBoundaryColor
        coloring := by
  funext step
  calc
    pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) step =
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).leftBoundaryColor
        (pair.sourceCrosscutComplementSerialColoring data boundary hcubic
          (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
            coloring hcoloring)) step :=
      (pair.sourceCrosscutComplementSerialColoring_leftBoundaryColor data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) step).symm
    _ = (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).leftBoundaryColor
        coloring step := by
      rw [pair.sourceCrosscutComplementSerialColoring_openRegionColoringOfSerial
        data boundary hcubic coloring hcoloring]

/-- The reconstructed literal coloring reads the serial output word exactly. -/
theorem sourceCrosscutComplementOpenRegionColoringOfSerial_rightBoundaryWord
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
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring)
    (hcoloring :
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
        coloring) :
    pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) =
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).rightBoundaryColor
        coloring := by
  funext step
  calc
    pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) step =
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).rightBoundaryColor
        (pair.sourceCrosscutComplementSerialColoring data boundary hcubic
          (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
            coloring hcoloring)) step :=
      (pair.sourceCrosscutComplementSerialColoring_rightBoundaryColor data boundary hcubic
        (pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
          coloring hcoloring) step).symm
    _ = (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).rightBoundaryColor
        coloring step := by
      rw [pair.sourceCrosscutComplementSerialColoring_openRegionColoringOfSerial
        data boundary hcubic coloring hcoloring]

/-- The serial source Cell accepts exactly the boundary-word pairs with a
positive entry in the already established literal source `Count` matrix. -/
theorem sourceCrosscutComplementTwoSidedOpenTangle_acceptsBoundaryWords_iff
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
    (leftWord : Fin pair.left.walk.length → Color)
    (rightWord : Fin pair.right.walk.length → Color) :
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).AcceptsBoundaryWords
        leftWord rightWord ↔
      0 < pair.sourceCrosscutComplementBoundaryColorCount data boundary hcubic
        leftWord rightWord := by
  constructor
  · rintro ⟨coloring, hcoloring, hleft, hright⟩
    rw [pair.sourceCrosscutComplementBoundaryColorCount_apply]
    apply Finset.card_pos.mpr
    let openColoring :=
      pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
        coloring hcoloring
    refine ⟨openColoring, ?_⟩
    apply (pair.mem_sourceCrosscutComplementTaitColoringFiber_iff data boundary hcubic
      leftWord rightWord openColoring).2
    refine ⟨pair.sourceCrosscutComplementOpenRegionColoringOfSerial_isTait
      data boundary hcubic coloring hcoloring, ?_, ?_⟩
    · calc
        pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic
            openColoring =
          (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).leftBoundaryColor
            coloring :=
          pair.sourceCrosscutComplementOpenRegionColoringOfSerial_leftBoundaryWord
            data boundary hcubic coloring hcoloring
        _ = leftWord := hleft
    · calc
        pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic
            openColoring =
          (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).rightBoundaryColor
            coloring :=
          pair.sourceCrosscutComplementOpenRegionColoringOfSerial_rightBoundaryWord
            data boundary hcubic coloring hcoloring
        _ = rightWord := hright
  · rw [pair.sourceCrosscutComplementBoundaryColorCount_apply]
    intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨openColoring, hmember⟩
    rcases (pair.mem_sourceCrosscutComplementTaitColoringFiber_iff data boundary hcubic
      leftWord rightWord openColoring).1 hmember with
      ⟨hcoloring, hleft, hright⟩
    let coloring := pair.sourceCrosscutComplementSerialColoring data boundary hcubic
      openColoring
    refine ⟨coloring,
      pair.sourceCrosscutComplementSerialColoring_isTait data boundary hcubic
        openColoring hcoloring, ?_, ?_⟩
    · funext step
      calc
        (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).leftBoundaryColor
            coloring step =
          pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic
            openColoring step :=
          pair.sourceCrosscutComplementSerialColoring_leftBoundaryColor
            data boundary hcubic openColoring step
        _ = leftWord step := congrFun hleft step
    · funext step
      calc
        (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).rightBoundaryColor
            coloring step =
          pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic
            openColoring step :=
          pair.sourceCrosscutComplementSerialColoring_rightBoundaryColor
            data boundary hcubic openColoring step
        _ = rightWord step := congrFun hright step

/-- Serial acceptance refines to the manuscript's full finite interface
profiles: cut colors, strand connectivity, and capped face progress. -/
theorem sourceCrosscutComplementTwoSidedOpenTangle_acceptsBoundaryWords_iff_exists_profilePair
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
    (leftWord : Fin pair.left.walk.length → Color)
    (rightWord : Fin pair.right.walk.length → Color) :
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).AcceptsBoundaryWords
        leftWord rightWord ↔
      ∃ leftProfile rightProfile :
          pair.SourceCrosscutComplementInterfaceProfile data boundary,
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
            leftProfile = leftWord ∧
          pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
            rightProfile = rightWord ∧
          0 < pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary
            hcubic leftProfile rightProfile := by
  exact
    (pair.sourceCrosscutComplementTwoSidedOpenTangle_acceptsBoundaryWords_iff
      data boundary hcubic leftWord rightWord).trans
      (pair.sourceCrosscutComplementBoundaryColorCount_pos_iff_exists_profilePair
        data boundary hcubic leftWord rightWord)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
