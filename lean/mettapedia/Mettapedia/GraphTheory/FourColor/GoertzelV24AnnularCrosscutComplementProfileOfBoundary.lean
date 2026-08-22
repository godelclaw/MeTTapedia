import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfile

/-!
# Removed-side profile semantics from the source boundary datum

`SourceCrosscutBoundaryData` already carries a dart at an explicit removed
vertex.  The complementary open region can therefore be rooted directly from
that datum, without a global cubicity hypothesis on the ambient rotation
system.  This matters for the source annulus: its named boundary stubs have
degree one, so global cubicity is false even though every literal interior
Cell is locally cubic.

This file gives the existing removed-side five-coordinate profile and `Count`
semantics a boundary-rooted API.  It changes no profile coordinate and no
notion of support.  The older cubicity-parameterized declarations remain as
compatibility wrappers; the new declarations are the ones that can be
instantiated on the actual opened source carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24CorridorProfile
open GoertzelV24CorridorTransferMatrix
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Read a regional edge from a coloring of the complementary open region,
using the removed dart already stored in the source boundary datum. -/
noncomputable def sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color) :
    G.edgeSet → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ then
      dartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRootOfBoundary data boundary) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ edge hedge, by
            simpa using vertexSideDart_mem_inside data.toRotationSystem
              (pair.componentSide boundary.component)ᶜ edge hedge⟩)
    else 0

/-- Every regional edge receives a nonzero color from a literal Tait coloring
of the boundary-rooted complementary open region. -/
theorem sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) :
    pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
      data boundary coloring edge ≠ 0 := by
  rw [sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary]
  simp only [dif_pos hedge]
  exact dartColor_ne_zero data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRootOfBoundary data boundary)
    coloring hcoloring _

/-- The complete four-port profile of the literal complementary region,
computed without a global degree premise. -/
noncomputable def sourceCrosscutComplementLiteralOpenProfileOfBoundary
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring) :=
  let hregion := pair.sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
    data boundary
  let hports := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    data boundary
  (pair.sourceCrosscutComplementBoundaryProfileData data boundary).regionalProfile
    (pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
      data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
        data boundary coloring hcoloring (hregion (hports (.inl crossing))))

/-- Read the left full source-interface profile from a boundary-rooted
complementary coloring. -/
noncomputable def sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring) :
    pair.SourceCrosscutComplementInterfaceProfile data boundary := by
  let hports := pair.sourceCrosscutComplementLeftCutData_portsInRegion
    data boundary
  exact (pair.sourceCrosscutComplementLeftCutData data boundary).regionalProfile
    (pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
      data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
        data boundary coloring hcoloring (hports (.inl crossing)))

/-- Read the aligned right full source-interface profile from the same
boundary-rooted complementary coloring. -/
noncomputable def sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
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
    (coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring) :
    pair.SourceCrosscutComplementInterfaceProfile data boundary := by
  let hports := pair.sourceCrosscutComplementRightCutData_portsInRegion
    data boundary
  exact (pair.sourceCrosscutComplementRightCutData data boundary).regionalProfile
    (pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary
      data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSideOfBoundary_ne_zero
        data boundary coloring hcoloring (hports (.inl crossing)))

/-- Literal Tait colorings of the boundary-rooted complementary tangle. -/
abbrev SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
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
  { coloring : (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).EdgeColoring Color //
    (pair.sourceCrosscutComplementOpenRegionOfBoundary
      data boundary).IsTaitEdgeColoring coloring }

/-- The finite fiber of boundary-rooted literal colorings realizing a pair
of full source-interface profiles. -/
noncomputable def sourceCrosscutComplementLiteralOpenProfilePairFiberOfBoundary
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    Finset (pair.SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
      data boundary) := by
  classical
  exact Finset.univ.filter fun coloring =>
    pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
        data boundary coloring.1 coloring.2 = left ∧
      pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
        data boundary coloring.1 coloring.2 = right

/-- The removed-side `Count` matrix rooted only by source boundary data. -/
noncomputable def sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
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
    TransferMatrix (pair.SourceCrosscutComplementInterfaceProfile data boundary) :=
  fun left right =>
    (pair.sourceCrosscutComplementLiteralOpenProfilePairFiberOfBoundary
      data boundary left right).card

@[simp]
theorem sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_apply
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        data boundary left right =
      (pair.sourceCrosscutComplementLiteralOpenProfilePairFiberOfBoundary
        data boundary left right).card :=
  rfl

/-- Positivity of the boundary-rooted `Count` entry is exactly realization by
one literal open Tait coloring. -/
theorem sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_pos_iff
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    0 < pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary
        data boundary left right ↔
      ∃ coloring :
          pair.SourceCrosscutComplementLiteralOpenTaitColoringOfBoundary
            data boundary,
        pair.sourceCrosscutComplementLiteralOpenLeftProfileOfBoundary
            data boundary coloring.1 coloring.2 = left ∧
          pair.sourceCrosscutComplementLiteralOpenRightProfileOfBoundary
            data boundary coloring.1 coloring.2 = right := by
  rw [pair.sourceCrosscutComplementLiteralOpenProfileCountOfBoundary_apply]
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    exact ⟨coloring, (Finset.mem_filter.mp hmember).2⟩
  · rintro ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ coloring, hleft, hright⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
