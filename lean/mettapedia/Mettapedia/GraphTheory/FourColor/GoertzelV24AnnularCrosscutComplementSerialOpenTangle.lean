import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleComposition

/-!
# The complementary source Cell as a serial open tangle

The compositional generator between two source layer boundaries is the
complementary (removed) region, not the retained outer component.  This file
places that literal complementary region in the generic two-sided open-tangle
category.  Its boundary split is forced by two already proved equivalences:
boundary darts are indexed by their physical crossing edges, and those edges
are indexed by the left-then-right source transversal order.

No homogeneity, profile equality, or global corridor assembly is asserted
here.  In particular, this construction does not serially compose retained
outer components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenTangleComposition
open GoertzelV24RotationCutDartDecomposition
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The complementary side's exposed darts, split in the actual source order:
all darts on the left transversal followed by all darts on the right one.
The map is not an arbitrary finite enumeration; both equivalences use the
physical crossing edge as their common carrier. -/
noncomputable def sourceCrosscutComplementBoundarySplit
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
    BoundaryDart data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component) ≃
      Fin pair.left.walk.length ⊕ Fin pair.right.walk.length :=
  (boundaryDartEquivVertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide boundary.component)).trans
    (pair.sourceCrosscutPortEquiv data boundary).symm

/-- The complementary boundary dart at one source coordinate. -/
noncomputable def sourceCrosscutComplementBoundaryDartAt
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
    BoundaryDart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
  (pair.sourceCrosscutComplementBoundarySplit data boundary).symm index

/-- Complement-side boundary coordinates name exactly the physical source
crossing edges. -/
@[simp]
theorem sourceCrosscutComplementBoundaryDartAt_edgeOf
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
    data.toRotationSystem.edgeOf
        (pair.sourceCrosscutComplementBoundaryDartAt data boundary index).1.1 =
      (pair.sourceCrosscutPort data boundary index).1 := by
  let edgeEquiv := boundaryDartEquivVertexSetCrossingEdge
    data.toRotationSystem (pair.componentSide boundary.component)
  change
    (edgeEquiv (edgeEquiv.symm
      (pair.sourceCrosscutPortEquiv data boundary index))).1 =
      (pair.sourceCrosscutPort data boundary index).1
  rw [edgeEquiv.apply_symm_apply]
  rfl

/-- The left input block of the complement adapter is the left source
transversal, position for position. -/
@[simp]
theorem sourceCrosscutComplementBoundaryDartAt_left_edgeOf
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
    (step : Fin pair.left.walk.length) :
    data.toRotationSystem.edgeOf
        (pair.sourceCrosscutComplementBoundaryDartAt data boundary
          (Sum.inl step)).1.1 =
      pair.left.crossingEdge hunique step := by
  rw [pair.sourceCrosscutComplementBoundaryDartAt_edgeOf data boundary]
  rfl

/-- The right output block likewise keeps the right source transversal's
literal order. -/
@[simp]
theorem sourceCrosscutComplementBoundaryDartAt_right_edgeOf
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
    (step : Fin pair.right.walk.length) :
    data.toRotationSystem.edgeOf
        (pair.sourceCrosscutComplementBoundaryDartAt data boundary
          (Sum.inr step)).1.1 =
      pair.right.crossingEdge hunique step := by
  rw [pair.sourceCrosscutComplementBoundaryDartAt_edgeOf data boundary]
  rfl

/-- A retained root for the literal complementary open tangle.  It is the
same old dart used to root the already constructed open-region rotation
system, before that construction adds its fresh boundary stub. -/
noncomputable def sourceCrosscutComplementRetainedRoot
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
    RetainedDart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
  ⟨pair.sourceCrosscutComplementDart data boundary hcubic, by
    intro hkept
    apply boundary.removed_not_kept
    rw [← pair.sourceCrosscutComplementDart_vertOf data boundary hcubic]
    exact hkept⟩

/-- The actual complementary source region as a two-sided literal open
tangle.  Its input and output carriers are the two source transversals, while
its internal carrier consists precisely of old darts whose mates remain in
the complementary Cell. -/
noncomputable def sourceCrosscutComplementTwoSidedOpenTangle
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
    TwoSidedOpenTangleData
      { vertex : V // vertex ∉ pair.componentSide boundary.component }
      (InternalDart data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component))
      (Fin pair.left.walk.length) (Fin pair.right.walk.length) :=
  (OpenTangleData.ofVertexSide data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
      (pair.sourceCrosscutComplementRetainedRoot data boundary hcubic)).splitBoundary
    (pair.sourceCrosscutComplementBoundarySplit data boundary)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
