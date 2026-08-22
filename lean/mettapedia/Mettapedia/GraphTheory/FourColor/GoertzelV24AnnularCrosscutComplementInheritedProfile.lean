import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileOfBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalProfileColorCongruence

/-!
# Ambient colors recover the literal complementary profiles

Restricting an ambient Tait coloring to the boundary-rooted complementary
open region does not change any color observed on the retained edge region.
Consequently the literal open left and right profiles are exactly the ambient
graph-derived profiles on the same physical cut data.  This compares all five
profile coordinates and is the validation bridge used by literal `Count`
support; it makes no converse gluing claim.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationVertexCutProfile
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The literal complementary color obtained by inheriting an ambient
coloring agrees with that ambient coloring throughout the retained region. -/
theorem sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_inherited
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
    (ambient : data.toRotationSystem.EdgeColoring Color)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) :
    pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
        data boundary
        (inheritedColoring data.toRotationSystem
          (fun vertex => vertex ∉ pair.componentSide boundary.component)
          (pair.sourceCrosscutComplementRootOfBoundary data boundary) ambient)
        edge = ambient edge := by
  rw [sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary]
  simp only [dif_pos hedge]
  unfold dartColor
  rw [inheritedColoring_edgeOf]
  simp only [inheritedDartColor]
  exact congrArg ambient
    (vertexSideDart_edgeOf data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ edge hedge)

/-- The inherited literal left profile is the ambient graph-derived profile
on the same physical cut data. -/
theorem sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary_inherited_eq_profile
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
    (ambient : data.toRotationSystem.EdgeColoring Color)
    (hambient : data.toRotationSystem.IsTaitEdgeColoring ambient) :
    pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary data boundary
        (inheritedColoring data.toRotationSystem
          (fun vertex => vertex ∉ pair.componentSide boundary.component)
          (pair.sourceCrosscutComplementRootOfBoundary data boundary) ambient)
        (inheritedColoring_isTait data.toRotationSystem
          (fun vertex => vertex ∉ pair.componentSide boundary.component)
          (pair.sourceCrosscutComplementRootOfBoundary data boundary)
          ambient hambient) =
      (pair.sourceCrosscutComplementLeftCutData data boundary).profile
        ambient hambient := by
  unfold sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
  let cutData := pair.sourceCrosscutComplementLeftCutData data boundary
  let hports := pair.sourceCrosscutComplementLeftCutData_portsInRegion
    data boundary
  have heq : ∀ edge ∈ cutData.regionEdges,
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary data boundary
          (inheritedColoring data.toRotationSystem
            (fun vertex => vertex ∉ pair.componentSide boundary.component)
            (pair.sourceCrosscutComplementRootOfBoundary data boundary) ambient)
          edge = ambient edge := by
    intro edge hedge
    exact pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_inherited
      data boundary ambient hedge
  rw [cutData.regionalProfile_eq_of_eq_on_region hports _ _ _ _ heq]
  exact cutData.regionalProfile_eq_profile ambient hambient

/-- The inherited literal right profile is the ambient graph-derived profile
on the same physical cut data. -/
theorem sourceCrosscutComplementLiteralOpenRightProfileOfBoundary_inherited_eq_profile
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
    (ambient : data.toRotationSystem.EdgeColoring Color)
    (hambient : data.toRotationSystem.IsTaitEdgeColoring ambient) :
    pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary data boundary
        (inheritedColoring data.toRotationSystem
          (fun vertex => vertex ∉ pair.componentSide boundary.component)
          (pair.sourceCrosscutComplementRootOfBoundary data boundary) ambient)
        (inheritedColoring_isTait data.toRotationSystem
          (fun vertex => vertex ∉ pair.componentSide boundary.component)
          (pair.sourceCrosscutComplementRootOfBoundary data boundary)
          ambient hambient) =
      (pair.sourceCrosscutComplementRightCutData data boundary).profile
        ambient hambient := by
  unfold sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
  let cutData := pair.sourceCrosscutComplementRightCutData data boundary
  let hports := pair.sourceCrosscutComplementRightCutData_portsInRegion
    data boundary
  have heq : ∀ edge ∈ cutData.regionEdges,
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary data boundary
          (inheritedColoring data.toRotationSystem
            (fun vertex => vertex ∉ pair.componentSide boundary.component)
            (pair.sourceCrosscutComplementRootOfBoundary data boundary) ambient)
          edge = ambient edge := by
    intro edge hedge
    exact pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_inherited
      data boundary ambient hedge
  rw [cutData.regionalProfile_eq_of_eq_on_region hports _ _ _ _ heq]
  exact cutData.regionalProfile_eq_profile ambient hambient

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
