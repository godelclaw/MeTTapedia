import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileBoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralCountComposition

/-!
# Full-profile diagonal support gives source-crosscut completion

The source transfer state records boundary colors together with strand
connectivity and capped face progress.  A positive diagonal entry in the
removed region's full-profile `Count` matrix therefore says more than color
agreement: the same complete finite state is realized on both interfaces.

For reverse completion, only one polarity is needed.  Every seam word
realized by a coloring of the shortened map must be the color projection of
some positive diagonal full-profile entry of the removed region.  Projecting
that entry to boundary colors supplies the complementary open coloring, and
the literal gluing theorem reconstructs a coloring of the source map.

This file deliberately does not require the converse implication.  Extra
colorings of the removed region cannot obstruct counterexample preservation.
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

/-- The polarity of seam support needed by reverse completion: every word
accepted by the retained open piece is accepted by the removed piece. -/
def SourceCrosscutSeamSupportLift
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
    0 < pair.sourceCrosscutLiteralOpenSeamColorCount data boundary word →
      0 < pair.sourceCrosscutComplementSeamColorCount data boundary hcubic word

/-- The full-profile form of the source pumping obligation.  Each retained
seam word is the color coordinate of a profile whose removed-region `Count`
has a positive diagonal entry.  Equality on that diagonal includes the
connectivity and capped-face coordinates, not only the displayed word. -/
def SourceCrosscutProfileDiagonalLift
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
    0 < pair.sourceCrosscutLiteralOpenSeamColorCount data boundary word →
      ∃ profile : pair.SourceCrosscutComplementInterfaceProfile data boundary,
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
            data boundary profile = word ∧
          0 < pair.sourceCrosscutComplementLiteralOpenProfileCount
            data boundary hcubic profile profile

/-- Reindexing a single full profile to the right interface only transports
its color coordinate along the certified equality of crosscut lengths. -/
theorem sourceCrosscutComplementInterfaceProfileRightColorWord_eq_cast_left
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
    (profile : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    pair.sourceCrosscutComplementInterfaceProfileRightColorWord
        data boundary profile =
      fun step =>
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
          data boundary profile (Fin.cast pair.length_eq.symm step) :=
  rfl

/-- A positive diagonal full-profile witness projects to the one-way seam
support implication consumed by the gluing theorem. -/
theorem sourceCrosscutSeamSupportLift_ofProfileDiagonalLift
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
    (hlift : pair.SourceCrosscutProfileDiagonalLift data boundary hcubic) :
    pair.SourceCrosscutSeamSupportLift data boundary hcubic := by
  intro word hword
  rcases hlift word hword with ⟨profile, hprofileWord, hdiagonal⟩
  rw [pair.sourceCrosscutComplementSeamColorCount_eq_boundaryColorCount_diagonal]
  apply (pair.sourceCrosscutComplementBoundaryColorCount_pos_iff_exists_profilePair
    data boundary hcubic word
      (fun step => word (Fin.cast pair.length_eq.symm step))).2
  refine ⟨profile, profile, hprofileWord, ?_, hdiagonal⟩
  rw [pair.sourceCrosscutComplementInterfaceProfileRightColorWord_eq_cast_left]
  exact congrArg
    (fun projected => fun step => projected (Fin.cast pair.length_eq.symm step))
    hprofileWord

/-- The one-way seam support implication completes every shortened coloring
back to a coloring of the original source rotation system. -/
theorem sourceCrosscutReverseCompletion_ofSeamSupportLift
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
    (hlift : pair.SourceCrosscutSeamSupportLift data boundary hcubic) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).ReverseCompletion := by
  intro output houtput
  apply pair.sourceCrosscutComplete_of_positiveComplementSeamColorCount
    data boundary hcubic seamEndpoints output houtput
  apply hlift
  simpa [sourceCrosscutLiteralOpenSeamColorCount] using
    (pair.sourceCrosscutSpliceOutput_literalBoundaryColorCount_pos
      data boundary seamEndpoints output houtput)

/-- The full-profile diagonal obligation is therefore sufficient for the
reverse-completion field of a reductive source-crosscut step. -/
theorem sourceCrosscutReverseCompletion_ofProfileDiagonalLift
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
    (hlift : pair.SourceCrosscutProfileDiagonalLift data boundary hcubic) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).ReverseCompletion :=
  pair.sourceCrosscutReverseCompletion_ofSeamSupportLift
    data boundary hcubic seamEndpoints
      (pair.sourceCrosscutSeamSupportLift_ofProfileDiagonalLift
        data boundary hcubic hlift)

/-- A full-profile diagonal lift preserves non-colorability in the reductive
direction: a bad source map shortens to another bad map. -/
theorem not_taitColorable_sourceCrosscutSplice_ofProfileDiagonalLift
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
    (hlift : pair.SourceCrosscutProfileDiagonalLift data boundary hcubic)
    (hbad : ¬ TaitColorable (RS := data.toRotationSystem)) :
    ¬ TaitColorable
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output :=
  (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    |>.not_taitColorable_output_of_not_taitColorable
      (pair.sourceCrosscutReverseCompletion_ofProfileDiagonalLift
        data boundary hcubic seamEndpoints hlift) hbad

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
