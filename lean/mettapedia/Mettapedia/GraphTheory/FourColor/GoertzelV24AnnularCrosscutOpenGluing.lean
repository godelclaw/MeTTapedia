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
    (hcubic : data.toRotationSystem.IsCubic) : data.toRotationSystem.D :=
  Classical.choose (exists_dartAt_of_isCubic data.toRotationSystem hcubic
    boundary.removed)

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
  Classical.choose_spec (exists_dartAt_of_isCubic data.toRotationSystem hcubic
    boundary.removed)

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
    (hcubic : data.toRotationSystem.IsCubic) :
    Dart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
  Sum.inl ⟨pair.sourceCrosscutComplementDart data boundary hcubic, by
    intro hkept
    apply boundary.removed_not_kept
    rw [← pair.sourceCrosscutComplementDart_vertOf data boundary hcubic]
    exact hkept⟩

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
    (hcubic : data.toRotationSystem.IsCubic) :=
  rotationSystem data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRoot data boundary hcubic)

/-- The exact source-specialized seam condition consumed by literal open
gluing.  It is intentionally a concrete statement about the two actual open
tangles; a later profile-factor theorem must construct it from equal finite
profiles rather than postulate a completion. -/
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
    (hcubic : data.toRotationSystem.IsCubic)
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color) : Prop :=
  BoundaryAgreement data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary)
    (pair.sourceCrosscutComplementRoot data boundary hcubic)
    inside outside

/-- The source crosscut's two literal open pieces glue to an ambient Tait
coloring once both are Tait and their exposed colors agree.  This is the
geometric-and-color-level conclusion required by the eventual profile
completion construction. -/
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
    (hcubic : data.toRotationSystem.IsCubic)
    (inside : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (outside : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hinside : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring inside)
    (houtside : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      outside)
    (hagreement : pair.SourceCrosscutOpenBoundaryAgreement data boundary hcubic
      inside outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact exists_taitColoring_of_openRegionColorings_of_boundaryAgreement
    data.toRotationSystem
    (fun vertex => vertex ∈ pair.componentSide boundary.component)
    (pair.sourceCrosscutOpenRoot data boundary)
    (pair.sourceCrosscutComplementRoot data boundary hcubic)
    inside outside hinside houtside hagreement

/-- Concrete reverse completion for the actual shortened source splice,
conditional only on a Tait coloring of the literal complementary tangle with
the required concrete boundary agreement.  The output coloring is first
restricted to the real retained source tangle, then the two literal pieces
are glued.  Thus the future semantic-profile proof has one exact assembly
target instead of an abstract completion adapter. -/
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
    (hcubic : data.toRotationSystem.IsCubic)
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
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color)
    (houtside :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
        outside)
    (hagreement : pair.SourceCrosscutOpenBoundaryAgreement data boundary hcubic
      (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
      outside) :
    ∃ closed : data.toRotationSystem.EdgeColoring Color,
      data.toRotationSystem.IsTaitEdgeColoring closed := by
  exact pair.exists_sourceCrosscutAmbientTaitColoring_of_openColorings
    data boundary hcubic
    (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
    outside
    (pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary
      seamEndpoints output houtput)
    houtside hagreement

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
