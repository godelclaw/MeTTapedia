import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSpliceBoundary

/-!
# Source splice boundary from a Cell-3 local layer

The Cell-3 open-tangle branch obtains its deletion component locally, from
the two-sided interior faces actually traversed by a simple layer loop.  This
adapter places that concrete component in the existing ordered-crosscut splice
interface.  It deliberately isolates the older full splice API here: the
Cell-3 component proof itself remains on the lightweight local separator
imports and makes no global two-sidedness assertion about hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24FramedLocalDualCycleSeparator
open GoertzelV24HexFaceRungType
open GoertzelV24SpliceUnification
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSpliceBoundaryEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerPair

/-- The concrete Cell-3 local layer supplies the complete geometric boundary
package used by the ordered source splice.  The retained side is selected by
the distinguished outer dart; every crossing orientation and every boundary
port is then computed from that component.  No global `OrbitFacesTwoSided`
hypothesis is used: the only two-sidedness needed was discharged locally in
`exists_outer_component_exactBoundary_and_removed`. -/
theorem sourceCrosscutBoundaryData_nonempty
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Nonempty (SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      (layers.separatedLocalLayerPair hunique)) := by
  rcases layers.exists_outer_component_exactBoundary_and_removed hunique with
    ⟨component, removed, houter, hremoved, hboundary⟩
  have hboundary' : componentCrossingEdges
      ((layers.separatedLocalLayerPair hunique).primalCutEdges
        web.annular.cellulation.rotation) component =
      (layers.separatedLocalLayerPair hunique).primalCutEdges
        web.annular.cellulation.rotation := by
    change componentCrossingEdges
        (dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
          (layers.separatedLocalLayerPair hunique).dualLoop) component =
      dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
        (layers.separatedLocalLayerPair hunique).dualLoop
    ext edge
    have hmem := Finset.ext_iff.mp hboundary edge
    simpa [cutEdges, localEdgeFinsetValueSet, edgeFinsetValueSet,
      localComponentCrossingEdges, componentCrossingEdges] using hmem
  exact ⟨{
    component := component
    component_boundary := hboundary'
    outer_kept := (layers.separatedLocalLayerPair hunique).mem_componentSide_iff
      component (web.annular.RS.vertOf web.annular.RS.outer) |>.2 houter
    removed := removed
    removed_not_kept := by
      intro hkept
      exact hremoved
        ((layers.separatedLocalLayerPair hunique).mem_componentSide_iff
          component removed |>.1 hkept)
    leftCrosses := by
      intro step
      apply GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.exists_oriented_componentSide_crossingDart
          web.annular.cellulation.rotation
          (layers.separatedLocalLayerPair hunique) component hboundary'
      rw [GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.primalCutEdges_eq_sourceCrossingSupport
          web.annular.cellulation.rotation
          (layers.separatedLocalLayerPair hunique)]
      exact Finset.mem_union_left _
        ((SimpleDualCrosscut.mem_crossingEdges_iff
          (layers.separatedLocalLayerPair hunique).left hunique _).2
          ⟨step, rfl⟩)
    rightCrosses := by
      intro step
      apply GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.exists_oriented_componentSide_crossingDart
          web.annular.cellulation.rotation
          (layers.separatedLocalLayerPair hunique) component hboundary'
      rw [GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.primalCutEdges_eq_sourceCrossingSupport
          web.annular.cellulation.rotation
          (layers.separatedLocalLayerPair hunique)]
      exact Finset.mem_union_right _
        ((SimpleDualCrosscut.mem_crossingEdges_iff
          (layers.separatedLocalLayerPair hunique).right hunique _).2
          ⟨step, rfl⟩)
    leftInjective := by
      exact (layers.separatedLocalLayerPair hunique).left.crossingEdge_injective
        (orbitFace_incidence_le_two web.annular.RS) hunique
    rightInjective := by
      exact (layers.separatedLocalLayerPair hunique).right.crossingEdge_injective
        (orbitFace_incidence_le_two web.annular.RS) hunique
    cover := by
      intro exposed
      have hcut : web.annular.cellulation.rotation.toRotationSystem.edgeOf
          exposed.1.1 ∈
          (layers.separatedLocalLayerPair hunique).primalCutEdges
            web.annular.cellulation.rotation := by
        rw [← GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
            web.annular.cellulation.rotation
            (layers.separatedLocalLayerPair hunique) component hboundary']
        exact GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.boundaryDart_edge_mem_vertexSetCrossingEdges
            web.annular.cellulation.rotation.toRotationSystem
            ((layers.separatedLocalLayerPair hunique).componentSide component)
            exposed
      rw [GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.primalCutEdges_eq_sourceCrossingSupport
          web.annular.cellulation.rotation
          (layers.separatedLocalLayerPair hunique)] at hcut
      rcases Finset.mem_union.1 hcut with hleft | hright
      · left
        rw [GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.orderedCut_crossingEdge_eq_crossingEdges
          (layers.separatedLocalLayerPair hunique).left hunique]
        exact hleft
      · right
        rw [GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.orderedCut_crossingEdge_eq_crossingEdges
          (layers.separatedLocalLayerPair hunique).right hunique]
        exact hright
    disjoint := by
      rw [GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.orderedCut_crossingEdge_eq_crossingEdges
          (layers.separatedLocalLayerPair hunique).left hunique,
        GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.orderedCut_crossingEdge_eq_crossingEdges
            (layers.separatedLocalLayerPair hunique).right hunique]
      exact (layers.separatedLocalLayerPair hunique).crossing_disjoint
    }⟩

/-- The canonical source-local boundary package.  Keeping this choice behind
one definition prevents downstream profile code from selecting an arbitrary
side of the Cell-3 layer. -/
noncomputable def sourceCrosscutBoundaryData
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    SeparatedAlignedSimpleDualCrosscuts.SourceCrosscutBoundaryData
      web.annular.cellulation.rotation
      (layers.separatedLocalLayerPair hunique) :=
  Classical.choice (layers.sourceCrosscutBoundaryData_nonempty hunique)

/-- Read the actual Cell-3 local layer boundary in the ordered port carrier
consumed by the finite-profile and splice libraries.  This is only the
geometric interface: equality of two such profiles and the construction of a
larger repeated region remain separate source obligations. -/
noncomputable def orderedCutSidesData
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    OrderedCutSidesData web.annular.RS layers.firstLayer.walk.length 0
      ((layers.separatedLocalLayerPair hunique).sourceCrosscutFaceFragmentCount
        web.annular.cellulation.rotation
        (layers.sourceCrosscutBoundaryData hunique)) :=
  (layers.separatedLocalLayerPair hunique).sourceCrosscutOrderedCutSidesData
    web.annular.cellulation.rotation (layers.sourceCrosscutBoundaryData hunique)

/-- The left ordered ports are literally the first source-layer crossings in
facial-dual path order. -/
@[simp]
theorem orderedCutSidesData_left
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (step : Fin layers.firstLayer.walk.length) :
    (layers.orderedCutSidesData hunique).left.crossingEdge step =
      layers.firstLayer.crossingEdge hunique step :=
  GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutOrderedCutSidesData_left
    web.annular.cellulation.rotation (layers.separatedLocalLayerPair hunique)
    (layers.sourceCrosscutBoundaryData hunique) step

/-- The right ordered ports are literally the second source-layer crossings,
transported only through the proved equality of the two local widths. -/
@[simp]
theorem orderedCutSidesData_right
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (step : Fin layers.firstLayer.walk.length) :
    (layers.orderedCutSidesData hunique).right.crossingEdge step =
      layers.secondLayer.crossingEdge hunique
        (Fin.cast (layers.separatedLocalLayerPair hunique).length_eq step) :=
  GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts.sourceCrosscutOrderedCutSidesData_right
    web.annular.cellulation.rotation (layers.separatedLocalLayerPair hunique)
    (layers.sourceCrosscutBoundaryData hunique) step

end LocalLayerPair

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
