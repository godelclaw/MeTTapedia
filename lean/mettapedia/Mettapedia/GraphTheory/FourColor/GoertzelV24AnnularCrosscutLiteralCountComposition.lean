import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralCountGluing

/-!
# Literal `Count` composition for source crosscuts

The source's counting functor is compositional in both directions.  The
preceding file proved that matching positive fibers glue to an ambient Tait
coloring.  Here an ambient Tait coloring is restricted back to the two
literal open tangles.  Their source-ordered seam words agree by construction,
so the support-level gluing law is an equivalence rather than a one-way
completion device.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionColorGluing
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Restrict an ambient coloring to the literal complementary source tangle. -/
noncomputable def sourceCrosscutInheritedComplementOpenColoring
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
    (coloring : data.toRotationSystem.EdgeColoring Color) :
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color :=
  inheritedColoring data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring

/-- An ambient Tait coloring restricts to a Tait coloring of the complementary
literal source tangle. -/
theorem sourceCrosscutInheritedComplementOpenColoring_isTait
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
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      (pair.sourceCrosscutInheritedComplementOpenColoring data boundary hcubic coloring) := by
  exact inheritedColoring_isTait data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring hcoloring

/-- The retained literal boundary word of an inherited coloring is the
ambient edge-color word on the same source-ordered boundary darts. -/
theorem sourceCrosscutInheritedOpen_insideBoundaryWord_eq_ambient
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
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (index : pair.SourceCrosscutBoundaryIndex) :
    pair.sourceCrosscutInsideBoundaryWord data boundary
        (pair.sourceCrosscutInheritedOpenColoring data boundary coloring) index =
      coloring (data.toRotationSystem.edgeOf
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1) := by
  unfold sourceCrosscutInsideBoundaryWord
  rw [openOldDartColor_eq_boundaryStubColor]
  exact pair.sourceCrosscutInheritedOpenColoring_stubColor data boundary coloring
    (pair.sourceCrosscutBoundaryDartAt data boundary index)

/-- The complementary literal boundary word of an inherited coloring is the
same ambient edge-color word, read at the opposite source dart. -/
theorem sourceCrosscutInheritedComplement_outsideBoundaryWord_eq_ambient
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
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (index : pair.SourceCrosscutBoundaryIndex) :
    pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic
        (pair.sourceCrosscutInheritedComplementOpenColoring data boundary hcubic coloring)
        index =
      coloring (data.toRotationSystem.edgeOf
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1) := by
  change inheritedColoring data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component)
      (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
      ((rotationSystem data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic)).edgeOf
          (Sum.inl ⟨data.toRotationSystem.alpha
            (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1,
            (pair.sourceCrosscutBoundaryDartAt data boundary index).2⟩)) = _
  rw [inheritedColoring_edgeOf]
  simp [inheritedDartColor]

/-- Restricting one ambient coloring to the two literal source pieces produces
exactly matching source-ordered seam words. -/
theorem sourceCrosscutInherited_boundaryWords_eq
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
    (coloring : data.toRotationSystem.EdgeColoring Color) :
    pair.sourceCrosscutInsideBoundaryWord data boundary
        (pair.sourceCrosscutInheritedOpenColoring data boundary coloring) =
      pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic
        (pair.sourceCrosscutInheritedComplementOpenColoring data boundary hcubic coloring) := by
  funext index
  rw [pair.sourceCrosscutInheritedOpen_insideBoundaryWord_eq_ambient data boundary
      coloring index,
    pair.sourceCrosscutInheritedComplement_outsideBoundaryWord_eq_ambient
      data boundary hcubic coloring index]

/-- The left boundary word of the complementary literal source tangle. -/
noncomputable def sourceCrosscutComplementLeftBoundaryWord
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
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color) :
    Fin pair.left.walk.length → Color :=
  fun step => pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring (.inl step)

/-- The right boundary word of the complementary literal source tangle. -/
noncomputable def sourceCrosscutComplementRightBoundaryWord
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
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color) :
    Fin pair.right.walk.length → Color :=
  fun step => pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic coloring (.inr step)

/-- The finite fiber of complementary literal open Tait colorings with a
specified pair of source boundary words. -/
noncomputable def sourceCrosscutComplementTaitColoringFiber
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
    (left : Fin pair.left.walk.length → Color)
    (right : Fin pair.right.walk.length → Color) :
    Finset ((pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color) := by
  classical
  exact Finset.univ.filter fun coloring =>
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
        coloring ∧
      pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring = left ∧
      pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring = right

/-- The complementary literal `Count` matrix over the actual two-boundary
source interface. -/
noncomputable def sourceCrosscutComplementBoundaryColorCount
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
    Matrix (Fin pair.left.walk.length → Color)
      (Fin pair.right.walk.length → Color) Nat :=
  fun left right =>
    (pair.sourceCrosscutComplementTaitColoringFiber data boundary hcubic left right).card

@[simp]
theorem sourceCrosscutComplementBoundaryColorCount_apply
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
    (left : Fin pair.left.walk.length → Color)
    (right : Fin pair.right.walk.length → Color) :
    pair.sourceCrosscutComplementBoundaryColorCount data boundary hcubic left right =
      (pair.sourceCrosscutComplementTaitColoringFiber data boundary hcubic left right).card :=
  rfl

/-- Membership in a complementary `Count` fiber has precisely its intended
open-coloring and two-boundary-word meaning. -/
theorem mem_sourceCrosscutComplementTaitColoringFiber_iff
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
    (left : Fin pair.left.walk.length → Color)
    (right : Fin pair.right.walk.length → Color)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring Color) :
    coloring ∈ pair.sourceCrosscutComplementTaitColoringFiber data boundary hcubic left right ↔
      (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
          coloring ∧
        pair.sourceCrosscutComplementLeftBoundaryWord data boundary hcubic coloring = left ∧
        pair.sourceCrosscutComplementRightBoundaryWord data boundary hcubic coloring = right := by
  classical
  simp [sourceCrosscutComplementTaitColoringFiber]

/-- The support-level `Count` composition law for one paired source crosscut:
the closed map is Tait-colorable exactly when its two literal open tangles
have positive fibers at a common *pair* of source boundary words. -/
theorem taitColorable_iff_exists_positive_sourceCrosscutBoundaryColorCounts
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
    TaitColorable (RS := data.toRotationSystem) ↔
      ∃ left : Fin pair.left.walk.length → Color,
        ∃ right : Fin pair.right.walk.length → Color,
          0 < pair.sourceCrosscutLiteralOpenBoundaryColorCount data boundary left right ∧
          0 < pair.sourceCrosscutComplementBoundaryColorCount
            data boundary hcubic left right := by
  constructor
  · rintro ⟨coloring, hcoloring⟩
    let inside := pair.sourceCrosscutInheritedOpenColoring data boundary coloring
    let outside := pair.sourceCrosscutInheritedComplementOpenColoring
      data boundary hcubic coloring
    let left := pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary inside
    let right := pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary inside
    refine ⟨left, right, ?_, ?_⟩
    · rw [pair.sourceCrosscutLiteralOpenBoundaryColorCount_apply]
      apply Finset.card_pos.mpr
      refine ⟨inside, (pair.mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff
        data boundary left right inside).2 ?_⟩
      exact ⟨pair.sourceCrosscutInheritedOpenColoring_isTait data boundary
        coloring hcoloring, rfl, rfl⟩
    · rw [pair.sourceCrosscutComplementBoundaryColorCount_apply]
      apply Finset.card_pos.mpr
      refine ⟨outside, (pair.mem_sourceCrosscutComplementTaitColoringFiber_iff
        data boundary hcubic left right outside).2 ?_⟩
      refine ⟨pair.sourceCrosscutInheritedComplementOpenColoring_isTait data
        boundary hcubic coloring hcoloring, ?_, ?_⟩
      · funext step
        exact (congrFun (pair.sourceCrosscutInherited_boundaryWords_eq
          data boundary hcubic coloring) (.inl step)).symm
      · funext step
        exact (congrFun (pair.sourceCrosscutInherited_boundaryWords_eq
          data boundary hcubic coloring) (.inr step)).symm
  · rintro ⟨left, right, hinside, houtside⟩
    rw [pair.sourceCrosscutLiteralOpenBoundaryColorCount_apply] at hinside
    rcases Finset.card_pos.mp hinside with ⟨inside, hinsideMember⟩
    rcases (pair.mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff data boundary
      left right inside).1 hinsideMember with ⟨hinsideTait, hinsideLeft, hinsideRight⟩
    rw [pair.sourceCrosscutComplementBoundaryColorCount_apply] at houtside
    rcases Finset.card_pos.mp houtside with ⟨outside, houtsideMember⟩
    rcases (pair.mem_sourceCrosscutComplementTaitColoringFiber_iff data boundary hcubic
      left right outside).1 houtsideMember with
      ⟨houtsideTait, houtsideLeft, houtsideRight⟩
    apply pair.exists_sourceCrosscutAmbientTaitColoring_of_openColorings_of_words_eq
      data boundary hcubic inside outside hinsideTait houtsideTait
    funext index
    rcases index with step | step
    · calc
        pair.sourceCrosscutInsideBoundaryWord data boundary inside (.inl step) =
            left step := congrFun hinsideLeft step
        _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
            (.inl step) := (congrFun houtsideLeft step).symm
    · calc
        pair.sourceCrosscutInsideBoundaryWord data boundary inside (.inr step) =
            right step := congrFun hinsideRight step
        _ = pair.sourceCrosscutOutsideBoundaryWord data boundary hcubic outside
            (.inr step) := (congrFun houtsideRight step).symm

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
