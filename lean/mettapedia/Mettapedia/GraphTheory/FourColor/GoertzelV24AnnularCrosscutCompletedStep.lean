import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutFiniteSeamAudit

/-!
# A completed source-crosscut reduction step

The literal open-tangle gluing theorem turns a passed generated finite seam
audit into the reverse-completion half of a reductive step.  This file joins
that result to the already proved strict retained-vertex descent.  It remains
at the fixed rotation-system level: packaging varying graph carriers into the
source's full multi-sorted counterexample class is a later assembly step.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- A passed generated seam audit supplies the completed reverse-completion
step for one concrete source crosscut. -/
noncomputable def sourceCrosscutCompletedStep_ofFiniteSeamProfileAudit
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
    (haudit : pair.SourceCrosscutFiniteSeamProfileAuditAgreement
      data boundary hcubic) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).CompletedStep where
  reverse_completion := reverseCompletion_of_semanticProfileBridge
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutSemanticProfileBridge_ofFiniteSeamProfileAudit
      data boundary hcubic seamEndpoints haudit)

/-- The completed source-crosscut step preserves non-colorability in the
required reductive direction. -/
theorem sourceCrosscutCompletedStep_counterexample_preserved_ofFiniteSeamProfileAudit
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
    (haudit : pair.SourceCrosscutFiniteSeamProfileAuditAgreement
      data boundary hcubic)
    (hbad : ¬ TaitColorable (RS := data.toRotationSystem)) :
    ¬ TaitColorable
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output :=
  completedStep_counterexample_preserved
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutCompletedStep_ofFiniteSeamProfileAudit
      data boundary hcubic seamEndpoints haudit) hbad

/-- The same completed step has the strict size decrease required of a
reductive splice. -/
theorem sourceCrosscutCompletedStep_outputSize_lt_ofFiniteSeamProfileAudit
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
    (haudit : pair.SourceCrosscutFiniteSeamProfileAuditAgreement
      data boundary hcubic) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).outputSize <
      Fintype.card V :=
  completedStep_strict_size
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutCompletedStep_ofFiniteSeamProfileAudit
      data boundary hcubic seamEndpoints haudit)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
