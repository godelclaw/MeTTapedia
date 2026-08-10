import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralCountComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionTaitInheritance

/-!
# Full finite profiles on the removed side of a source crosscut

The source's `Count` functor assigns a profile matrix to every open tangle,
not only to the retained side of a splice.  The paired source transversals
already determine the complementary open tangle.  This module begins the
other half of that construction by carrying their actual source order across
the complementary vertex side.

No profile coordinate is supplied as an assumption: the crossing carrier is
the same finite cut seen from the opposite side, with its source order proved
explicitly below.
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
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The paired source transversals enumerate the same cut edges when viewed
from the removed vertex side. -/
noncomputable def sourceCrosscutComplementPort
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
    Fin pair.left.walk.length ⊕ Fin pair.right.walk.length ≃
      VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
  apply Equiv.ofBijective (fun source =>
    ⟨(pair.sourceCrosscutPort data boundary source).1, by
      rw [mem_vertexSetCrossingEdges_iff]
      apply (edgeCrossesVertexSet_compl data.toRotationSystem
        (pair.componentSide boundary.component) _).2
      rw [← mem_vertexSetCrossingEdges_iff]
      exact (pair.sourceCrosscutPort data boundary source).2⟩)
  constructor
  · intro first second heq
    apply pair.sourceCrosscutPort_injective data boundary
    apply Subtype.ext
    have hval := congrArg Subtype.val heq
    change (pair.sourceCrosscutPort data boundary first).1 =
      (pair.sourceCrosscutPort data boundary second).1 at hval
    exact hval
  · intro crossing
    have hkept : crossing.1 ∈ vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component) := by
      rw [mem_vertexSetCrossingEdges_iff]
      apply (edgeCrossesVertexSet_compl data.toRotationSystem
        (pair.componentSide boundary.component) crossing.1).1
      rw [← mem_vertexSetCrossingEdges_iff]
      exact crossing.2
    obtain ⟨source, hsource⟩ := pair.sourceCrosscutPort_surjective data boundary
      ⟨crossing.1, hkept⟩
    refine ⟨source, ?_⟩
    apply Subtype.ext
    have hval := congrArg Subtype.val hsource
    change (pair.sourceCrosscutPort data boundary source).1 = crossing.1 at hval
    exact hval

/-- Source-order indexing of the complementary boundary cut.  It is an
equivalence, not an arbitrary `Fintype` enumeration, so both literal open
tangles use the same two transversal blocks. -/
noncomputable def sourceCrosscutComplementBoundaryIndexing
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
    VertexSetCrossingIndexing data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ := by
  let hcard : Fintype.card (VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) =
      pair.left.walk.length + pair.right.walk.length := by
    simpa using (Fintype.card_congr
      (pair.sourceCrosscutComplementPort data boundary)).symm
  exact (finCongr hcard).trans
    ((finSumFinEquiv).symm.trans
      (pair.sourceCrosscutComplementPort data boundary))

/-- The left source transversal retains its literal edge order when the cut
is viewed from the removed side. -/
@[simp]
theorem sourceCrosscutComplementPort_left
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
    (pair.sourceCrosscutComplementPort data boundary (Sum.inl step)).1 =
      pair.left.crossingEdge hunique step :=
  rfl

/-- The right source transversal likewise retains its literal edge order on
the removed side. -/
@[simp]
theorem sourceCrosscutComplementPort_right
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
    (pair.sourceCrosscutComplementPort data boundary (Sum.inr step)).1 =
      pair.right.crossingEdge hunique step :=
  rfl

/-- The complete graph-derived profile data on the removed side of the two
source transversals.  Its face fragments are computed from that side's real
regional edges, so it need not be definitionally identified with the retained
side's fragment carrier. -/
noncomputable def sourceCrosscutComplementBoundaryProfileData
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
  vertexSetBoundaryGraphCutDataWithIndexing data.toRotationSystem
    (pair.componentSide boundary.component)ᶜ
    (pair.sourceCrosscutComplementBoundaryIndexing data boundary)

/-- Every complementary profile port is an actual edge of the removed vertex
side.  This is derived from the graph cut data rather than carried as a
semantic premise. -/
theorem sourceCrosscutComplementBoundaryProfileData_portsInRegion
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
    (pair.sourceCrosscutComplementBoundaryProfileData data boundary).PortsInRegion :=
  vertexSetBoundaryGraphCutDataWithIndexing_portsInRegion
    data.toRotationSystem (pair.componentSide boundary.component)ᶜ
    (pair.sourceCrosscutComplementBoundaryIndexing data boundary)

/-- The complementary profile's regional carrier is precisely the real
deleted-side regional edge set. -/
theorem sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
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
    (pair.sourceCrosscutComplementBoundaryProfileData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
  intro edge hedge
  simpa [sourceCrosscutComplementBoundaryProfileData,
    vertexSetBoundaryGraphCutDataWithIndexing] using hedge

/-- Read a regional ambient edge from a coloring of the literal complementary
open tangle.  As on the retained side, values outside the selected region are
zero and cannot enter a profile coordinate. -/
noncomputable def sourceCrosscutComplementLiteralColorOnVertexSide
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color) :
    G.edgeSet → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ then
      dartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ edge hedge, by
            simpa using vertexSideDart_mem_inside data.toRotationSystem
              (pair.componentSide boundary.component)ᶜ edge hedge⟩)
    else 0

/-- A regional edge receives a nonzero color from every literal complementary
open Tait coloring. -/
theorem sourceCrosscutComplementLiteralColorOnVertexSide_ne_zero
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) :
    pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic
      coloring edge ≠ 0 := by
  rw [sourceCrosscutComplementLiteralColorOnVertexSide]
  simp only [dif_pos hedge]
  exact dartColor_ne_zero data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRoot data boundary hcubic) coloring hcoloring _

/-- The complete finite five-coordinate profile of the literal removed-side
open tangle.  This is a computed `Count` interface: boundary colors,
two-color connectivity, and capped face progress are all read from the actual
complementary region. -/
noncomputable def sourceCrosscutComplementLiteralOpenProfile
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring) :=
  let hregion := pair.sourceCrosscutComplementBoundaryProfileData_regionEdges_subset
    data boundary
  let hports := pair.sourceCrosscutComplementBoundaryProfileData_portsInRegion
    data boundary
  (pair.sourceCrosscutComplementBoundaryProfileData data boundary).regionalProfile
    (pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring)
    (fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSide_ne_zero data boundary
        hcubic coloring hcoloring (hregion (hports (.inl crossing))))

/-! ## The two source interfaces as a removed-side `Count` matrix -/

/-- The number of boundary-local face fragments on the removed side.  Unlike
the retained-side carrier this is computed from the complementary regional
edges, because the source `Count` functor assigns data to each open tangle in
its own right. -/
abbrev sourceCrosscutComplementFaceFragmentCount
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
    (boundary : SourceCrosscutBoundaryData data pair) : Nat :=
  Fintype.card (BoundaryRegionalFragment data.toRotationSystem
    (vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ)
    (vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ))

/-- Raw graph-derived profile data for one source interface on the removed
side.  The caller supplies the source-order crossing list; all region and
face information is calculated from the literal complementary tangle. -/
noncomputable def sourceCrosscutComplementCutData
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
    {width : Nat} (crossingEdge : Fin width → G.edgeSet) :
    GraphCorridorCutData data.toRotationSystem width 0
      (pair.sourceCrosscutComplementFaceFragmentCount data boundary) where
  regionEdges := vertexSetRegionEdges data.toRotationSystem
    (pair.componentSide boundary.component)ᶜ
  crossingEdge := crossingEdge
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment =>
    (boundaryRegionalFragmentAt data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ) fragment).1.1
  fragmentEdges := fun fragment =>
    boundaryRegionalFragmentEdges data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (boundaryRegionalFragmentAt data.toRotationSystem
        (vertexSetCrossingEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ)
        (vertexSetRegionEdges data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ) fragment)

/-- The left source interface on the complementary open tangle. -/
noncomputable def sourceCrosscutComplementLeftCutData
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
    GraphCorridorCutData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutComplementFaceFragmentCount data boundary) :=
  pair.sourceCrosscutComplementCutData data boundary
    (pair.left.crossingEdge hunique)

/-- The right source interface on the complementary open tangle, reindexed
to the aligned left-hand rung coordinate. -/
noncomputable def sourceCrosscutComplementRightCutData
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
    GraphCorridorCutData data.toRotationSystem pair.left.walk.length 0
      (pair.sourceCrosscutComplementFaceFragmentCount data boundary) :=
  pair.sourceCrosscutComplementCutData data boundary
    (fun step => pair.right.crossingEdge hunique (Fin.cast pair.length_eq step))

/-- The actual left transversal ports lie in the complementary region because
they are crossing edges of that same cut. -/
theorem sourceCrosscutComplementLeftCutData_portsInRegion
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
    (pair.sourceCrosscutComplementLeftCutData data boundary).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · change pair.left.crossingEdge hunique crossing ∈
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ
    apply vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem
    simpa using (pair.sourceCrosscutComplementPort data boundary
      (Sum.inl crossing)).2
  · exact Fin.elim0 terminal

/-- The aligned right transversal ports lie in the complementary region as
well; the cast is only the already-proved rung correspondence. -/
theorem sourceCrosscutComplementRightCutData_portsInRegion
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
    (pair.sourceCrosscutComplementRightCutData data boundary).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · change pair.right.crossingEdge hunique (Fin.cast pair.length_eq crossing) ∈
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ
    apply vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem
    simpa using (pair.sourceCrosscutComplementPort data boundary
      (Sum.inr (Fin.cast pair.length_eq crossing))).2
  · exact Fin.elim0 terminal

/-- The finite profile carrier at either complementary source interface. -/
abbrev SourceCrosscutComplementInterfaceProfile
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
  CorridorCutProfile pair.left.walk.length 0
    (pair.sourceCrosscutComplementFaceFragmentCount data boundary)

/-- Read the left full source profile from a literal complementary Tait
coloring. -/
noncomputable def sourceCrosscutComplementLiteralOpenLeftProfile
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring) :
    pair.SourceCrosscutComplementInterfaceProfile data boundary := by
  let hregion : (pair.sourceCrosscutComplementLeftCutData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
    intro edge hedge
    exact hedge
  let hports := pair.sourceCrosscutComplementLeftCutData_portsInRegion data boundary
  exact (pair.sourceCrosscutComplementLeftCutData data boundary).regionalProfile
    (pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring)
    (fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSide_ne_zero data boundary
        hcubic coloring hcoloring (hregion (hports (.inl crossing))))

/-- Read the aligned right full source profile from the same literal
complementary coloring. -/
noncomputable def sourceCrosscutComplementLiteralOpenRightProfile
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
    (coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color)
    (hcoloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring) :
    pair.SourceCrosscutComplementInterfaceProfile data boundary := by
  let hregion : (pair.sourceCrosscutComplementRightCutData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
    intro edge hedge
    exact hedge
  let hports := pair.sourceCrosscutComplementRightCutData_portsInRegion data boundary
  exact (pair.sourceCrosscutComplementRightCutData data boundary).regionalProfile
    (pair.sourceCrosscutComplementLiteralColorOnVertexSide data boundary hcubic coloring)
    (fun crossing =>
      pair.sourceCrosscutComplementLiteralColorOnVertexSide_ne_zero data boundary
        hcubic coloring hcoloring (hregion (hports (.inl crossing))))

/-- Literal Tait colorings of the removed-side source tangle.  This is an
open object in the compositional `Count` semantics, not a coloring assumed on
the ambient closed map. -/
abbrev SourceCrosscutComplementLiteralOpenTaitColoring
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
  { coloring : (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).EdgeColoring
      Color //
    (pair.sourceCrosscutComplementOpenRegion data boundary hcubic).IsTaitEdgeColoring
      coloring }

/-- The finite fiber of removed-side literal Tait colorings at a selected
pair of full source-interface profiles. -/
noncomputable def sourceCrosscutComplementLiteralOpenProfilePairFiber
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    Finset (pair.SourceCrosscutComplementLiteralOpenTaitColoring data boundary
      hcubic) := by
  classical
  exact Finset.univ.filter fun coloring =>
    pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
      coloring.1 coloring.2 = left ∧
    pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
      coloring.1 coloring.2 = right

/-- The removed-side `Count` matrix indexed by its two actual, finite source
profiles.  It is computed by finite filtering of literal open tangle
colorings; no externally searched data enter this definition. -/
noncomputable def sourceCrosscutComplementLiteralOpenProfileCount
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
    TransferMatrix (pair.SourceCrosscutComplementInterfaceProfile data boundary) :=
  fun left right =>
    (pair.sourceCrosscutComplementLiteralOpenProfilePairFiber data boundary
      hcubic left right).card

@[simp]
theorem sourceCrosscutComplementLiteralOpenProfileCount_apply
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary hcubic
      left right =
      (pair.sourceCrosscutComplementLiteralOpenProfilePairFiber data boundary
        hcubic left right).card :=
  rfl

/-- Membership in a removed-side full-profile fiber says exactly that the
literal coloring realizes both selected source profiles. -/
theorem mem_sourceCrosscutComplementLiteralOpenProfilePairFiber_iff
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary)
    (coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring data
      boundary hcubic) :
    coloring ∈ pair.sourceCrosscutComplementLiteralOpenProfilePairFiber
      data boundary hcubic left right ↔
      pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        coloring.1 coloring.2 = left ∧
      pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        coloring.1 coloring.2 = right := by
  classical
  simp [sourceCrosscutComplementLiteralOpenProfilePairFiber]

/-- Each literal removed-side Tait coloring makes a positive contribution to
the entry selected by its own two computed profiles. -/
theorem sourceCrosscutComplementLiteralOpenProfileCount_pos_of_coloring
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
    (coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring data
      boundary hcubic) :
    0 < pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary hcubic
      (pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
        coloring.1 coloring.2)
      (pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
        coloring.1 coloring.2) := by
  rw [pair.sourceCrosscutComplementLiteralOpenProfileCount_apply]
  apply Finset.card_pos.mpr
  refine ⟨coloring, ?_⟩
  exact (pair.mem_sourceCrosscutComplementLiteralOpenProfilePairFiber_iff
    data boundary hcubic _ _ coloring).2 ⟨rfl, rfl⟩

/-- Positivity of a removed-side full-profile entry is exactly the existence
of a literal open Tait coloring realizing its two endpoints. -/
theorem sourceCrosscutComplementLiteralOpenProfileCount_pos_iff
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
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    0 < pair.sourceCrosscutComplementLiteralOpenProfileCount data boundary hcubic
      left right ↔
      ∃ coloring : pair.SourceCrosscutComplementLiteralOpenTaitColoring data
        boundary hcubic,
        pair.sourceCrosscutComplementLiteralOpenLeftProfile data boundary hcubic
          coloring.1 coloring.2 = left ∧
        pair.sourceCrosscutComplementLiteralOpenRightProfile data boundary hcubic
          coloring.1 coloring.2 = right := by
  rw [pair.sourceCrosscutComplementLiteralOpenProfileCount_apply]
  constructor
  · intro h
    obtain ⟨coloring, hmem⟩ := Finset.card_pos.mp h
    exact ⟨coloring,
      (pair.mem_sourceCrosscutComplementLiteralOpenProfilePairFiber_iff
        data boundary hcubic _ _ coloring).1 hmem⟩
  · rintro ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring, ?_⟩
    exact (pair.mem_sourceCrosscutComplementLiteralOpenProfilePairFiber_iff
      data boundary hcubic _ _ coloring).2 ⟨hleft, hright⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
