import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralCountGluing

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

/-- The concrete generated `Count` support condition for a source crosscut.
It says exactly that the retained and removed open tangles accept the same
aligned seam words.  This is the source's transfer/identity obligation in a
form that can be discharged by the finite corridor calculation; it does not
postulate semantic equality. -/
def SourceCrosscutSeamSupportAgreement
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
    (hcubic : data.toRotationSystem.IsCubic) : Prop :=
  ∀ word : Fin pair.left.walk.length → Color,
    0 < pair.sourceCrosscutLiteralOpenSeamColorCount data boundary word ↔
      0 < pair.sourceCrosscutComplementSeamColorCount data boundary hcubic word

/-- The source's literal `Count` support agreement is precisely equality of
the two semantic seam-word sets.  This is the finite-to-semantic step needed
by reverse completion, proved from the actual generated counts on both
opened pieces. -/
theorem sourceCrosscutOpenExtendableWords_eq_complementSeamExtendableWords
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
    (hsupport : pair.SourceCrosscutSeamSupportAgreement data boundary hcubic) :
    pair.sourceCrosscutOpenExtendableWords data boundary =
      pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic := by
  ext word
  rw [← pair.sourceCrosscutLiteralOpenSeamColorCount_pos_iff data boundary word,
    ← pair.sourceCrosscutComplementSeamColorCount_pos_iff data boundary hcubic word]
  exact hsupport word

/-- A finite profile factor whose target codes agree gives the concrete
generated `Count` support agreement consumed by the literal source-crosscut
gluing theorem.  This is only the finite-to-support adapter: constructing the
factor from a realized corridor remains the source's transfer obligation. -/
theorem sourceCrosscutSeamSupportAgreement_ofFactor
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
    (factor : SemanticProfileFactor pair.left.walk.length)
    (hinner : factor.inner =
      pair.sourceCrosscutOpenExtendableWords data boundary)
    (houter : factor.outer =
      pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic)
    (htarget : factor.innerCode = factor.outerCode) :
    pair.SourceCrosscutSeamSupportAgreement data boundary hcubic := by
  intro word
  rw [pair.sourceCrosscutLiteralOpenSeamColorCount_pos_iff data boundary word,
    pair.sourceCrosscutComplementSeamColorCount_pos_iff data boundary hcubic word,
    ← hinner, ← houter, factor.equal_of_target_eq htarget]

/-- Construct the source crosscut semantic bridge directly from the concrete
generated `Count` support agreement.  Literal open-tangle gluing discharges
completion; no abstract extension axiom and no one-code factorization are
introduced. -/
noncomputable def sourceCrosscutSemanticProfileBridge_ofSeamSupport
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
    (hsupport : pair.SourceCrosscutSeamSupportAgreement data boundary hcubic) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).SemanticProfileBridge where
  inner := pair.sourceCrosscutOpenExtendableWords data boundary
  outer := pair.sourceCrosscutComplementSeamExtendableWords data boundary hcubic
  equal := pair.sourceCrosscutOpenExtendableWords_eq_complementSeamExtendableWords
    data boundary hcubic hsupport
  shortened_word_mem_inner := fun coloring hcoloring =>
    pair.seamColorWord_mem_sourceCrosscutOpenExtendableWords data boundary
      seamEndpoints coloring hcoloring
  complete_of_outer_word := fun coloring hcoloring hmember =>
    pair.sourceCrosscutComplete_of_complementSeamWord data boundary hcubic
      seamEndpoints coloring hcoloring hmember

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
  exact pair.sourceCrosscutSemanticProfileBridge_ofSeamSupport data boundary hcubic
    seamEndpoints
    (pair.sourceCrosscutSeamSupportAgreement_ofFactor data boundary hcubic factor
      hinner houter htarget)

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
