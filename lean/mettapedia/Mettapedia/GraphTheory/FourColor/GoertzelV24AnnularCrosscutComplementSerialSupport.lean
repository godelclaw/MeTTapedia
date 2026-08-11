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

/-- Conversely, serializing a literal removed-region Tait coloring and then
restoring its stubs returns that literal coloring exactly. -/
theorem sourceCrosscutComplementOpenRegionColoringOfSerial_serialColoring
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
    pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
        (pair.sourceCrosscutComplementSerialColoring data boundary hcubic coloring)
        (pair.sourceCrosscutComplementSerialColoring_isTait data boundary hcubic
          coloring hcoloring) =
      coloring := by
  exact openRegionColoringOfSplitVertexSideColoring_splitVertexSideColoring
    data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)
    (pair.sourceCrosscutComplementBoundarySplit data boundary) coloring hcoloring

/-- Tait colorings of the source Cell in its serial presentation. -/
abbrev SourceCrosscutComplementSerialTaitColoring
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
    (hcubic : data.toRotationSystem.IsCubic) :=
  { coloring :
      (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).Coloring //
    (pair.sourceCrosscutComplementTwoSidedOpenTangle data boundary hcubic).IsTaitColoring
      coloring }

/-- Restore a serial source-Cell Tait coloring as a literal open-region Tait
coloring, retaining the proof that the result is Tait. -/
noncomputable def sourceCrosscutComplementOpenTaitColoringOfSerial
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
    (coloring : pair.SourceCrosscutComplementSerialTaitColoring data boundary hcubic) :
    pair.SourceCrosscutComplementLiteralOpenTaitColoring data boundary hcubic :=
  ⟨pair.sourceCrosscutComplementOpenRegionColoringOfSerial data boundary hcubic
      coloring.1 coloring.2,
    pair.sourceCrosscutComplementOpenRegionColoringOfSerial_isTait
      data boundary hcubic coloring.1 coloring.2⟩

/-- Display a literal removed-region Tait coloring on the serial source Cell. -/
noncomputable def sourceCrosscutComplementSerialTaitColoringOfOpen
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
    (coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring
      data boundary hcubic) :
    pair.SourceCrosscutComplementSerialTaitColoring data boundary hcubic :=
  ⟨pair.sourceCrosscutComplementSerialColoring data boundary hcubic coloring.1,
    pair.sourceCrosscutComplementSerialColoring_isTait data boundary hcubic
      coloring.1 coloring.2⟩

/-- The subtype-level literal-to-serial-to-literal composite is the identity. -/
theorem sourceCrosscutComplementOpenTaitColoringOfSerial_serialTaitColoringOfOpen
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
    (coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring
      data boundary hcubic) :
    pair.sourceCrosscutComplementOpenTaitColoringOfSerial data boundary hcubic
        (pair.sourceCrosscutComplementSerialTaitColoringOfOpen data boundary hcubic
          coloring) =
      coloring := by
  apply Subtype.ext
  exact pair.sourceCrosscutComplementOpenRegionColoringOfSerial_serialColoring
    data boundary hcubic coloring.1 coloring.2

/-- A pair of full source profiles is serially realized when one serial Tait
coloring reconstructs to a literal coloring computing exactly those profiles.
This retains connectivity and capped-face data rather than projecting to
boundary colors. -/
def SourceCrosscutComplementSerialRealizesProfiles
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) : Prop :=
  ∃ coloring : pair.SourceCrosscutComplementSerialTaitColoring data boundary hcubic,
    pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        (pair.sourceCrosscutComplementOpenTaitColoringOfSerial
          data boundary hcubic coloring).1
        (pair.sourceCrosscutComplementOpenTaitColoringOfSerial
          data boundary hcubic coloring).2 = left ∧
      pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        (pair.sourceCrosscutComplementOpenTaitColoringOfSerial
          data boundary hcubic coloring).1
        (pair.sourceCrosscutComplementOpenTaitColoringOfSerial
          data boundary hcubic coloring).2 = right

/-- The serial full-profile semantics is exactly positivity of the source's
existing literal full-profile `Count` entry. -/
theorem sourceCrosscutComplementSerialRealizesProfiles_iff
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    pair.SourceCrosscutComplementSerialRealizesProfiles data boundary hcubic
        left right ↔
      0 < pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary hcubic
        left right := by
  constructor
  · rintro ⟨coloring, hleft, hright⟩
    let openColoring := pair.sourceCrosscutComplementOpenTaitColoringOfSerial
      data boundary hcubic coloring
    have hpositive :=
      pair.sourceCrosscutComplementLiteralOpenProfileCount_pos_of_coloring
        data boundary hcubic openColoring
    simpa only [openColoring, hleft, hright] using hpositive
  · intro hpositive
    rcases (pair.sourceCrosscutComplementLiteralOpenProfileCount_pos_iff
      data boundary hcubic left right).1 hpositive with
      ⟨openColoring, hleft, hright⟩
    let coloring := pair.sourceCrosscutComplementSerialTaitColoringOfOpen
      data boundary hcubic openColoring
    have hroundtrip :=
      pair.sourceCrosscutComplementOpenTaitColoringOfSerial_serialTaitColoringOfOpen
        data boundary hcubic openColoring
    refine ⟨coloring, ?_, ?_⟩
    · exact (congrArg (fun reconstructed =>
          pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
            reconstructed.1 reconstructed.2) hroundtrip).trans hleft
    · exact (congrArg (fun reconstructed =>
          pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
            reconstructed.1 reconstructed.2) hroundtrip).trans hright

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
