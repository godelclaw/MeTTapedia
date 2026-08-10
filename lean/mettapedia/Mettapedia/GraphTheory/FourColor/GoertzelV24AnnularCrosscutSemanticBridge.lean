import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutBoundaryWordGluing

/-!
# Semantic reverse-completion bridge for a literal source crosscut

The source crosscut supplies two literal open tangles: the retained piece and
the removed complementary piece.  Their source-ordered boundary words already
have a kernel-checked gluing theorem.  This file installs that calculation in
the generic `SemanticProfileBridge` used by a reductive splice.

The finite transfer factor is intentionally an explicit input.  It must be
proved from the corridor's computed `Count` profile; this module neither
assumes that factorization nor replaces it with a coloring-extension axiom.
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

/-- Construct the semantic bridge of one literal source crosscut once its
finite transfer factor has identified the actual retained and complementary
extendable-word sets.  The final bridge field is discharged by literal open
tangle gluing, not postulated. -/
noncomputable def sourceCrosscutSemanticProfileBridge_ofFactor
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
    (factor : SemanticProfileFactor pair.left.walk.length)
    (hinner : factor.inner =
      pair.sourceCrosscutOpenExtendableWords data boundary)
    (houter : factor.outer =
      pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic)
    (htarget : factor.innerCode = factor.outerCode) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).SemanticProfileBridge := by
  apply SemanticProfileBridge.ofFactor
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) factor htarget
  · intro coloring hcoloring
    rw [hinner]
    exact pair.seamColorWord_mem_sourceCrosscutOpenExtendableWords
      data boundary seamEndpoints coloring hcoloring
  · intro coloring hcoloring hmember
    rw [houter] at hmember
    exact pair.sourceCrosscutComplete_of_complementSeamWord
      data boundary hcubic seamEndpoints coloring hcoloring hmember

/-- The source crosscut's finite transfer factor gives a genuine reverse
completion theorem for the shortened splice. -/
theorem sourceCrosscutReverseCompletion_ofFactor
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
    (factor : SemanticProfileFactor pair.left.walk.length)
    (hinner : factor.inner =
      pair.sourceCrosscutOpenExtendableWords data boundary)
    (houter : factor.outer =
      pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic)
    (htarget : factor.innerCode = factor.outerCode) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).ReverseCompletion :=
  reverseCompletion_of_semanticProfileBridge
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutSemanticProfileBridge_ofFactor data boundary hcubic
      seamEndpoints factor hinner houter htarget)

/-- With the source factorization in hand, a non-Tait-colorable original map
has a non-Tait-colorable strictly shortened crosscut splice. -/
theorem not_taitColorable_sourceCrosscutSplice_ofFactor
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
    (factor : SemanticProfileFactor pair.left.walk.length)
    (hinner : factor.inner =
      pair.sourceCrosscutOpenExtendableWords data boundary)
    (houter : factor.outer =
      pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic)
    (htarget : factor.innerCode = factor.outerCode)
    (hbad : ¬ TaitColorable (RS := data.toRotationSystem)) :
    ¬ TaitColorable
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output :=
  not_taitColorable_output_of_semanticProfileBridge
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutSemanticProfileBridge_ofFactor data boundary hcubic
      seamEndpoints factor hinner houter htarget)
    hbad

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
