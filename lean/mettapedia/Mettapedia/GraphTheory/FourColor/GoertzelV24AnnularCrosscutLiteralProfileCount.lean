import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralProfileBoundaryWord

/-!
# Literal `Count` fibers for source crosscuts

The compositional proof counts Tait colorings of an *open* region by their
finite interface profile.  This module makes that semantic object literal for
the source crosscut: it is not an ambient coloring of the closed graph, but
the finite type of Tait colorings of the actual opened component.  The
profile-support and multiplicity definitions below are the one-boundary
pieces from which the corridor transfer matrices will be assembled.

No configuration catalogue or covering-style reduction is introduced here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24CorridorProfile
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The finite profile carrier on the actual source crosscut boundary.  Its
face coordinate is the computed set of boundary-local face fragments, not a
free zero-sized placeholder. -/
abbrev SourceCrosscutLiteralProfile
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
  CorridorCutProfile
    (Fintype.card (VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide boundary.component))) 0
    (Fintype.card (BoundaryRegionalFragment data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component))
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component))))

/-- The literal open component's Tait colorings.  This is the source of the
`Count` fibers; it does not presuppose a Tait coloring of the ambient graph. -/
abbrev SourceCrosscutLiteralOpenTaitColoring
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
  { coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color //
    (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring coloring }

/-- The finite source profile read from one literal open Tait coloring. -/
noncomputable def sourceCrosscutLiteralOpenProfileMap
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
  fun coloring : pair.SourceCrosscutLiteralOpenTaitColoring data boundary =>
    pair.sourceCrosscutLiteralOpenProfile data boundary coloring.1 coloring.2

/-- The source component's realized finite profiles.  This is a semantic
support set, defined from the literal open tangle rather than from a chosen
coloring of the ambient graph. -/
def sourceCrosscutLiteralOpenProfileSupport
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
  Set.range (pair.sourceCrosscutLiteralOpenProfileMap data boundary)

/-- The fiber over one finite profile: exactly the literal open Tait colorings
which restrict to that profile. -/
abbrev SourceCrosscutLiteralOpenProfileFiber
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
    (profile : pair.SourceCrosscutLiteralProfile data boundary) :=
  { coloring : pair.SourceCrosscutLiteralOpenTaitColoring data boundary //
    pair.sourceCrosscutLiteralOpenProfileMap data boundary coloring = profile }

/-- The literal multiplicity of a finite profile.  This is the relevant
nonnegative `Count` entry for a one-boundary open piece; later corridor work
will combine such fibers by the source's gluing/matrix law. -/
noncomputable def sourceCrosscutLiteralOpenProfileMultiplicity
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
    (profile : pair.SourceCrosscutLiteralProfile data boundary) : Nat :=
  Nat.card (pair.SourceCrosscutLiteralOpenProfileFiber data boundary profile)

/-- Membership in the semantic support is precisely nonemptiness of the
corresponding literal coloring fiber. -/
theorem mem_sourceCrosscutLiteralOpenProfileSupport_iff
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
    (profile : pair.SourceCrosscutLiteralProfile data boundary) :
    profile ∈ pair.sourceCrosscutLiteralOpenProfileSupport data boundary ↔
      Nonempty (pair.SourceCrosscutLiteralOpenProfileFiber data boundary profile) := by
  constructor
  · rintro ⟨coloring, hcoloring⟩
    exact ⟨⟨coloring, hcoloring⟩⟩
  · rintro ⟨coloring⟩
    exact ⟨coloring.1, coloring.2⟩

/-- A profile has positive literal multiplicity exactly when the open source
component realizes it.  This is the nonnegative counting semantics behind
the support set, not an appeal to a closed ambient coloring. -/
theorem sourceCrosscutLiteralOpenProfileMultiplicity_pos_iff
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
    (profile : pair.SourceCrosscutLiteralProfile data boundary) :
    0 < pair.sourceCrosscutLiteralOpenProfileMultiplicity data boundary profile ↔
      profile ∈ pair.sourceCrosscutLiteralOpenProfileSupport data boundary := by
  rw [sourceCrosscutLiteralOpenProfileMultiplicity, Nat.card_pos_iff]
  constructor
  · intro h
    exact (pair.mem_sourceCrosscutLiteralOpenProfileSupport_iff data boundary profile).2 h.1
  · intro h
    exact ⟨(pair.mem_sourceCrosscutLiteralOpenProfileSupport_iff data boundary profile).1 h,
      inferInstance⟩

/-- Every Tait coloring of the shortened splice supplies an actual member of
the source component's literal profile support.  Together with the seam-word
lemmas, this is the concrete input from a shortened coloring to the source
`Count` semantics. -/
theorem sourceCrosscutSpliceOutputLiteralOpenProfile_mem_support
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
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output output) :
    pair.sourceCrosscutLiteralOpenProfileMap data boundary
      ⟨pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output,
        pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
          output houtput⟩ ∈
        pair.sourceCrosscutLiteralOpenProfileSupport data boundary := by
  exact ⟨⟨pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output,
      pair.sourceCrosscutSpliceOutputOpenColoring_isTait data boundary seamEndpoints
        output houtput⟩, rfl⟩

/-- The finite profile carrier bounds the semantic support without assuming
anything about an ambient closed coloring. -/
theorem sourceCrosscutLiteralOpenProfileSupport_finite
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
    (pair.sourceCrosscutLiteralOpenProfileSupport data boundary).Finite :=
  Set.toFinite _

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
