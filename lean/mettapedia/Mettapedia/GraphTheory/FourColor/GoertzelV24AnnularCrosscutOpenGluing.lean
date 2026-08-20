import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOutputOpenRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionColorGluing

/-!
# Gluing the two literal sides of a source crosscut splice

The paired source crosscuts determine an outer deletion component and a
nonempty complementary side.  This module turns that complementary side into
its own literal open tangle and specializes generic open-region gluing to the
actual source crosscut geometry.

The remaining semantic task is deliberately visible: profile equality must
produce a Tait coloring of this complementary tangle with matching exposed
boundary colors.  Once it does, the theorem below gives the ambient Tait
coloring directly.  No abstract completion field is treated as evidence of
that construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionColorGluing
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Every vertex of a cubic rotation system supports an ambient dart.  The
source crosscut boundary already supplies one deleted vertex, so this turns
the complementary side into a rooted literal open region rather than leaving
it as an unrooted carrier. -/
theorem exists_dartAt_of_isCubic
    (RS : RotationSystem V G.edgeSet) (hcubic : RS.IsCubic) (vertex : V) :
    ∃ dart : RS.D, RS.vertOf dart = vertex := by
  have hcard : (RS.dartsAt vertex).card = 3 := hcubic vertex
  have hpositive : 0 < (RS.dartsAt vertex).card := by
    omega
  rcases Finset.card_pos.mp hpositive with ⟨dart, hdart⟩
  refine ⟨dart, ?_⟩
  simpa [RotationSystem.dartsAt] using hdart

/-- The complementary root dart retained by the geometric source-boundary
package.  Unlike the older constructor below, this requires no global
cubicity: connectedness was used once, when the boundary package was built. -/
noncomputable def sourceCrosscutComplementDartOfBoundary
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
    (boundary : SourceCrosscutBoundaryData data pair) :
    data.toRotationSystem.D :=
  boundary.removedDart

@[simp]
theorem sourceCrosscutComplementDartOfBoundary_vertOf
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
    (boundary : SourceCrosscutBoundaryData data pair) :
    data.toRotationSystem.vertOf
      (pair.sourceCrosscutComplementDartOfBoundary data boundary) =
        boundary.removed :=
  boundary.removedDart_vertOf

/-- A chosen dart at the explicit deleted source vertex. -/
noncomputable def sourceCrosscutComplementDart
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
    (_hcubic : data.toRotationSystem.IsCubic) : data.toRotationSystem.D :=
  pair.sourceCrosscutComplementDartOfBoundary data boundary

/-- The chosen complementary dart is based at the source boundary datum's
explicit removed vertex. -/
theorem sourceCrosscutComplementDart_vertOf
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
    (hcubic : data.toRotationSystem.IsCubic) :
    data.toRotationSystem.vertOf
      (pair.sourceCrosscutComplementDart data boundary hcubic) = boundary.removed :=
  pair.sourceCrosscutComplementDartOfBoundary_vertOf data boundary

/-- The complementary open-region root obtained directly from the retained
source-boundary dart.  This is the source-faithful replacement for threading
an impossible global-cubicity premise through the annular carrier. -/
noncomputable def sourceCrosscutComplementRootOfBoundary
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
    (boundary : SourceCrosscutBoundaryData data pair) :
    Dart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
  Sum.inl ⟨pair.sourceCrosscutComplementDartOfBoundary data boundary, by
    intro hkept
    apply boundary.removed_not_kept
    rw [← pair.sourceCrosscutComplementDartOfBoundary_vertOf data boundary]
    exact hkept⟩

/-- A literal root of the non-retained side of the source crosscut. -/
noncomputable def sourceCrosscutComplementRoot
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
    (_hcubic : data.toRotationSystem.IsCubic) :
    Dart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
  pair.sourceCrosscutComplementRootOfBoundary data boundary

/-- The literal complementary source region rooted by the boundary package,
with no global degree hypothesis on the already-open annular carrier. -/
noncomputable def sourceCrosscutComplementOpenRegionOfBoundary
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
    (boundary : SourceCrosscutBoundaryData data pair) :=
  rotationSystem data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRootOfBoundary data boundary)

/-- The literal complementary source tangle bounded by the same paired
crosscuts.  Unlike a syntactic ``removed region'', this has all its old darts
and fresh degree-one boundary stubs as an actual rotation system. -/
noncomputable def sourceCrosscutComplementOpenRegion
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
    (_hcubic : data.toRotationSystem.IsCubic) :=
  pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary

/-- The exact source-specialized seam condition consumed by literal open
gluing, stated directly from the retained source-boundary root.  It is a
concrete statement about the two actual open tangles; a later profile-factor
theorem must construct it from equal finite profiles rather than postulate a
completion. -/
abbrev SourceCrosscutOpenBoundaryAgreementOfBoundary
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside : (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
      Color) : Prop :=
  BoundaryAgreement data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary)
    (pair.sourceCrosscutComplementRootOfBoundary data boundary)
    inside outside

/-- Compatibility spelling of the source seam agreement for callers that
still carry the former global-cubicity premise. -/
abbrev SourceCrosscutOpenBoundaryAgreement
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
    (_hcubic : data.toRotationSystem.IsCubic)
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside : (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
      Color) : Prop :=
  pair.SourceCrosscutOpenBoundaryAgreementOfBoundary data boundary inside outside

/-- The source crosscut's two literal open pieces glue to an ambient Tait
coloring once both are Tait and their exposed colors agree.  This is the
geometric-and-color-level conclusion required by the eventual profile
completion construction. -/
theorem exists_sourceCrosscutAmbientTaitColoring_of_openColoringsOfBoundary
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
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside : (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
      Color)
    (hinside : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring inside)
    (houtside : (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
      outside)
    (hagreement : pair.SourceCrosscutOpenBoundaryAgreementOfBoundary data boundary
      inside outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact exists_taitColoring_of_openRegionColorings_of_boundaryAgreement
    data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary)
    (pair.sourceCrosscutComplementRootOfBoundary data boundary)
    inside outside hinside houtside hagreement

/-- Compatibility entry point for the former globally cubic gluing API. -/
theorem exists_sourceCrosscutAmbientTaitColoring_of_openColorings
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
    (_hcubic : data.toRotationSystem.IsCubic)
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside : (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
      Color)
    (hinside : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring inside)
    (houtside : (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
      outside)
    (hagreement : pair.SourceCrosscutOpenBoundaryAgreementOfBoundary data boundary
      inside outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact pair.exists_sourceCrosscutAmbientTaitColoring_of_openColoringsOfBoundary
    data boundary inside outside hinside houtside hagreement

/-- Concrete reverse completion for the actual shortened source splice,
conditional only on a Tait coloring of the literal complementary tangle with
the required concrete boundary agreement.  The output coloring is first
restricted to the real retained source tangle, then the two literal pieces
are glued.  Thus the future semantic-profile proof has one exact assembly
target instead of an abstract completion adapter. -/
theorem exists_sourceCrosscutAmbientTaitColoring_of_outputAndComplementOfBoundary
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
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (output :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (houtput : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output)
    (outside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring Color)
    (houtside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        outside)
    (hagreement : pair.SourceCrosscutOpenBoundaryAgreementOfBoundary data boundary
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
      outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact pair.exists_sourceCrosscutAmbientTaitColoring_of_openColoringsOfBoundary
    data boundary
    (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
    outside
    (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary
      seamEndpoints output houtput)
    houtside hagreement

/-- Compatibility entry point for output/complement gluing callers that still
carry the former global-cubicity premise. -/
theorem exists_sourceCrosscutAmbientTaitColoring_of_outputAndComplement
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
    (_hcubic : data.toRotationSystem.IsCubic)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (output :
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output.EdgeColoring
        Color)
    (houtput : RotationSystem.IsTaitEdgeColoring
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output)
    (outside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring Color)
    (houtside :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        outside)
    (hagreement : pair.SourceCrosscutOpenBoundaryAgreementOfBoundary data boundary
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
      outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact pair.exists_sourceCrosscutAmbientTaitColoring_of_outputAndComplementOfBoundary
    data boundary seamEndpoints output houtput outside houtside hagreement

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
