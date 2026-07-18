import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapReindexColor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutGluing
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalCyclicThreeEdgeConnected
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ThreeEdgeCutMinimality

open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24FaceDualConnectedness
open GoertzelV24MinimalCyclicThreeEdgeConnected
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutCapBridge
open GoertzelV24TwoEdgeCutCapGeometry
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The finite vertex side carried by a predicate-defined cyclic cut. -/
def cyclicCutVertexSide (cut : SmallCyclicEdgeCut G) : Finset V :=
  by
    classical
    exact Finset.univ.filter cut.side

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_cyclicCutVertexSide_iff
    (cut : SmallCyclicEdgeCut G) (vertex : V) :
    vertex ∈ cyclicCutVertexSide cut ↔ cut.side vertex := by
  classical
  simp [cyclicCutVertexSide]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A cycle on one side contains two distinct vertices on that side. -/
theorem HasCycleOnSide.exists_two_ne
    {side : V → Prop} (hcycle : HasCycleOnSide G side) :
    ∃ first second : V,
      side first ∧ side second ∧ second ≠ first := by
  rcases hcycle with ⟨first, hfirst, walk, hwalkCycle, hwalkSide⟩
  let second := walk.getVert 1
  have hpositive : 0 < walk.length :=
    lt_of_lt_of_le (by omega) hwalkCycle.three_le_length
  have hadj : G.Adj first second := by
    simpa [second] using walk.adj_getVert_succ (i := 0) hpositive
  exact ⟨first, second, hfirst,
    hwalkSide second (walk.getVert_mem_support 1), hadj.ne.symm⟩

/-- Enumerate the three edges of an exact cyclic cut. -/
def cyclicCutCrossingOfCardThree
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) :
    Fin 3 → G.edgeSet :=
  fun step =>
    ((Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 3).symm step).1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cyclicCutCrossingOfCardThree_injective
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) :
    Function.Injective (cyclicCutCrossingOfCardThree cut hcard) := by
  intro left right heq
  apply (Fintype.equivFinOfCardEq (by simpa using hcard) :
    cut.edgeCut ≃ Fin 3).symm.injective
  exact Subtype.ext heq

omit [Fintype V] [DecidableRel G.Adj] in
theorem orderedCut_cyclicCutCrossingOfCardThree
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) :
    orderedCut (cyclicCutCrossingOfCardThree cut hcard) = cut.edgeCut := by
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_image.mp hedge with ⟨step, _hstep, rfl⟩
    exact ((Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 3).symm step).2
  · intro hedge
    let edgeInCut : cut.edgeCut := ⟨edge, hedge⟩
    let step := (Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 3) edgeInCut
    apply Finset.mem_image.mpr
    refine ⟨step, Finset.mem_univ step, ?_⟩
    change ((Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 3).symm step).1 = edge
    have hinverse :
        (Fintype.equivFinOfCardEq (by simpa using hcard) :
          cut.edgeCut ≃ Fin 3).symm step = edgeInCut := by
      exact Equiv.symm_apply_apply _ edgeInCut
    exact congrArg Subtype.val hinverse

/-- An exact three-edge cyclic cut canonically determines the ordered pair
of complementary three-star caps required by the gluing theorem. -/
def cyclicCutThreeEdgeCutPairData
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (hcard : cut.edgeCut.card = 3) :
    graphData.toRotationSystem.ThreeEdgeCutPairData where
  side := cyclicCutVertexSide cut
  crossing := cyclicCutCrossingOfCardThree cut hcard
  crossing_injective := cyclicCutCrossingOfCardThree_injective cut hcard
  boundary_eq := by
    rw [← vertexSetCrossingEdges_eq_vertexSideEdgeBoundary]
    rw [orderedCut_cyclicCutCrossingOfCardThree cut hcard]
    ext edge
    rw [mem_simpleGraph_vertexSetCrossingEdges_iff]
    simpa using (cut.hcut_eq edge).symm

@[simp]
theorem cyclicCutThreeEdgeCutPairData_side_mem_iff
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (hcard : cut.edgeCut.card = 3) (vertex : V) :
    vertex ∈ (cyclicCutThreeEdgeCutPairData graphData cut hcard).side ↔
      cut.side vertex := by
  simp [cyclicCutThreeEdgeCutPairData, mem_cyclicCutVertexSide_iff]

/-- A graph-backed vertex-minimal Tait counterexample has no exact cyclic
three-edge cut. Each side is capped by one cubic vertex, the two caps remain
connected bridgeless spherical cubic maps, minimality colors them, and the
three-edge gluing equation colors the ambient map. -/
theorem no_exactCyclicThreeEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 3)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) : False := by
  let RS := graphData.toRotationSystem
  let pair := cyclicCutThreeEdgeCutPairData graphData cut hcard
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hsides := induce_both_sides_connected_of_card_eq_three
    hconnected hcyclic cut hcard
  have hsideKeep : pair.sideData.keep = cut.side := by
    funext vertex
    simp [pair, cyclicCutThreeEdgeCutPairData,
      RotationSystem.ThreeEdgeCutPairData.sideData,
      RotationSystem.ThreeEdgeCutSideData.keep]
  have hcomplementKeep : pair.complementData.keep = cut.compl.side := by
    funext vertex
    simp [pair, cyclicCutThreeEdgeCutPairData,
      RotationSystem.ThreeEdgeCutPairData.complementData,
      RotationSystem.ThreeEdgeCutSideData.keep,
      SmallCyclicEdgeCut.compl]
  have hsideTwoSided : OrbitFacesTwoSided pair.sideRootedRotationSystem := by
    simpa [pair,
      RotationSystem.ThreeEdgeCutPairData.sideRootedRotationSystem]
      using minimal.facesTwoSided
  have hcomplementTwoSided :
      OrbitFacesTwoSided pair.complementRootedRotationSystem := by
    simpa [pair,
      RotationSystem.ThreeEdgeCutPairData.complementRootedRotationSystem]
      using minimal.facesTwoSided
  have hsideRootCyclic : VertexRotationCyclic
      pair.sideRootedRotationSystem := by
    simpa [pair,
      RotationSystem.ThreeEdgeCutPairData.sideRootedRotationSystem]
      using minimal.vertexRotationCyclic
  have hcomplementRootCyclic : VertexRotationCyclic
      pair.complementRootedRotationSystem := by
    simpa [pair,
      RotationSystem.ThreeEdgeCutPairData.complementRootedRotationSystem]
      using minimal.vertexRotationCyclic
  have hsideRootFree : EdgeBridgeFree pair.sideRootedRotationSystem := by
    simpa [pair,
      RotationSystem.ThreeEdgeCutPairData.sideRootedRotationSystem]
      using minimal.edgeBridgeFree
  have hcomplementRootFree :
      EdgeBridgeFree pair.complementRootedRotationSystem := by
    simpa [pair,
      RotationSystem.ThreeEdgeCutPairData.complementRootedRotationSystem]
      using minimal.edgeBridgeFree
  have hsideRetained :
      (retainedAmbientPrimalGraph pair.sideRootedRotationSystem
        (pair.sideData.planarOrdered hsideTwoSided).keep).Connected := by
    change
      ((rotationPrimalGraph pair.sideRootedRotationSystem).induce
        {vertex |
          (pair.sideData.planarOrdered hsideTwoSided).keep vertex}).Connected
    change
      ((rotationPrimalGraph graphData.toRotationSystem).induce
        {vertex |
          (pair.sideData.planarOrdered hsideTwoSided).keep vertex}).Connected
    rw [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
    change (G.induce pair.sideData.keep).Connected
    rw [hsideKeep]
    exact hsides.1
  have hcomplementRetained :
      (retainedAmbientPrimalGraph pair.complementRootedRotationSystem
        (pair.complementData.planarOrdered hcomplementTwoSided).keep).Connected := by
    change
      ((rotationPrimalGraph pair.complementRootedRotationSystem).induce
        {vertex |
          (pair.complementData.planarOrdered hcomplementTwoSided).keep
            vertex}).Connected
    change
      ((rotationPrimalGraph graphData.toRotationSystem).induce
        {vertex |
          (pair.complementData.planarOrdered hcomplementTwoSided).keep
            vertex}).Connected
    rw [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
    change (G.induce pair.complementData.keep).Connected
    rw [hcomplementKeep]
    exact hsides.2
  have hsideSpherical : OrbitSphericalCubicMapData
      (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem := by
    exact pair.sideData.planarOrdered_cap_orbitSphericalCubicMapData_of_exactCyclicThreeCut
      (graphDataWithOuter graphData pair.sideRoot) cut hsideKeep hcard hcyclic
      ((orbitSphericalCubicMapData_withOuter_iff RS pair.sideRoot).2
        minimal.spherical)
      hsideTwoSided hconnected hsideRootCyclic
  have hcomplementSpherical : OrbitSphericalCubicMapData
      (pair.complementData.planarOrdered
        hcomplementTwoSided).capRotationSystem := by
    exact pair.complementData.planarOrdered_cap_orbitSphericalCubicMapData_of_exactCyclicThreeCut
      (graphDataWithOuter graphData pair.complementRoot) cut.compl
      hcomplementKeep (by simpa using hcard) hcyclic
      ((orbitSphericalCubicMapData_withOuter_iff RS pair.complementRoot).2
        minimal.spherical)
      hcomplementTwoSided hconnected hcomplementRootCyclic
  have hsideMap : BridgelessSphericalCubicMapData
      (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem :=
    { spherical := hsideSpherical
      primalConnected :=
        (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem_primalConnected
          hsideRetained
      vertexRotationCyclic :=
        (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem_vertexRotationCyclic
          hsideRootCyclic
      edgeBridgeFree :=
        (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem_edgeBridgeFree
          hsideRootFree hsideRetained }
  have hcomplementMap : BridgelessSphericalCubicMapData
      (pair.complementData.planarOrdered
        hcomplementTwoSided).capRotationSystem :=
    { spherical := hcomplementSpherical
      primalConnected :=
        (pair.complementData.planarOrdered
          hcomplementTwoSided).capRotationSystem_primalConnected
            hcomplementRetained
      vertexRotationCyclic :=
        (pair.complementData.planarOrdered
          hcomplementTwoSided).capRotationSystem_vertexRotationCyclic
            hcomplementRootCyclic
      edgeBridgeFree :=
        (pair.complementData.planarOrdered
          hcomplementTwoSided).capRotationSystem_edgeBridgeFree
            hcomplementRootFree hcomplementRetained }
  rcases HasCycleOnSide.exists_two_ne cut.houtside_cycle with
    ⟨outsideFirst, outsideSecond, houtsideFirst, houtsideSecond,
      houtsideNe⟩
  rcases HasCycleOnSide.exists_two_ne cut.hinside_cycle with
    ⟨insideFirst, insideSecond, hinsideFirst, hinsideSecond, hinsideNe⟩
  have hsideSmaller :
      Fintype.card (pair.sideData.planarOrdered hsideTwoSided).CapVertex <
        Fintype.card V := by
    apply (pair.sideData.planarOrdered
      hsideTwoSided).card_capVertex_lt_of_two_deleted
        outsideFirst outsideSecond
    · simpa [pair, cyclicCutThreeEdgeCutPairData,
        RotationSystem.ThreeEdgeCutSideData.planarOrdered,
        RotationSystem.ThreeEdgeCutSideData.reindex,
        RotationSystem.ThreeEdgeCutPairData.sideData] using houtsideFirst
    · simpa [pair, cyclicCutThreeEdgeCutPairData,
        RotationSystem.ThreeEdgeCutSideData.planarOrdered,
        RotationSystem.ThreeEdgeCutSideData.reindex,
        RotationSystem.ThreeEdgeCutPairData.sideData] using houtsideSecond
    · exact houtsideNe
  have hcomplementSmaller :
      Fintype.card
          (pair.complementData.planarOrdered
            hcomplementTwoSided).CapVertex < Fintype.card V := by
    apply (pair.complementData.planarOrdered
      hcomplementTwoSided).card_capVertex_lt_of_two_deleted
        insideFirst insideSecond
    · simpa [pair, cyclicCutThreeEdgeCutPairData,
        RotationSystem.ThreeEdgeCutSideData.planarOrdered,
        RotationSystem.ThreeEdgeCutSideData.reindex,
        RotationSystem.ThreeEdgeCutPairData.complementData] using hinsideFirst
    · simpa [pair, cyclicCutThreeEdgeCutPairData,
        RotationSystem.ThreeEdgeCutSideData.planarOrdered,
        RotationSystem.ThreeEdgeCutSideData.reindex,
        RotationSystem.ThreeEdgeCutPairData.complementData] using hinsideSecond
    · exact hinsideNe
  have hsidePlanarColorable : RotationSystemTaitColorable
      (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem :=
    minimal.smallerColorable
      (pair.sideData.planarOrdered hsideTwoSided).capRotationSystem
      hsideSmaller hsideMap
  have hcomplementPlanarColorable : RotationSystemTaitColorable
      (pair.complementData.planarOrdered
        hcomplementTwoSided).capRotationSystem :=
    minimal.smallerColorable
      (pair.complementData.planarOrdered
        hcomplementTwoSided).capRotationSystem
      hcomplementSmaller hcomplementMap
  have hsideColorable : RotationSystemTaitColorable
      pair.sideData.capRotationSystem :=
    pair.sideData.cap_taitColorable_of_planarOrdered
      hsideTwoSided hsidePlanarColorable
  have hcomplementColorable : RotationSystemTaitColorable
      pair.complementData.capRotationSystem :=
    pair.complementData.cap_taitColorable_of_planarOrdered
      hcomplementTwoSided hcomplementPlanarColorable
  apply minimal.notColorable
  exact pair.taitColorable_of_caps hsideColorable hcomplementColorable

/-- Exact cyclic three-edge cuts are impossible in a graph-backed
vertex-minimal Tait counterexample. -/
theorem no_smallCyclicEdgeCut_card_eq_three_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) : cut.edgeCut.card ≠ 3 := by
  intro hcard
  exact no_exactCyclicThreeEdgeCut graphData minimal
    (cyclicEdgeConnectivityAtLeast_three_of_vertexMinimalTaitCounterexample
      graphData minimal) cut hcard

/-- The exact three-star cap reduction raises the established cyclic
connectivity of every graph-backed vertex-minimal Tait counterexample from
three to four. -/
theorem cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    CyclicEdgeConnectivityAtLeast G 4 := by
  intro cut
  have hthree :=
    smallCyclicEdgeCut_card_three_le_of_vertexMinimalTaitCounterexample
      graphData minimal cut
  have hne :=
    no_smallCyclicEdgeCut_card_eq_three_of_vertexMinimalTaitCounterexample
      graphData minimal cut
  omega

/-- After the one-, two-, and exact three-edge reductions, excluding only
the four-edge cyclic cut is sufficient for cyclic five-edge-connectivity. -/
theorem cyclicallyFiveEdgeConnected_of_no_four_cyclicEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (hfour : ∀ cut : SmallCyclicEdgeCut G, cut.edgeCut.card ≠ 4) :
    CyclicallyFiveEdgeConnected G := by
  exact cyclicallyFiveEdgeConnected_of_no_three_or_four_cyclicEdgeCut
    graphData minimal
      (no_smallCyclicEdgeCut_card_eq_three_of_vertexMinimalTaitCounterexample
        graphData minimal)
      hfour

end

end GoertzelV24ThreeEdgeCutMinimality

end Mettapedia.GraphTheory.FourColor
