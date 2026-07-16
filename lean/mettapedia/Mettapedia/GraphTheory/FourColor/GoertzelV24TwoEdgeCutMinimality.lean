import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapBridge

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoEdgeCutMinimality

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24TwoEdgeCutCapBridge
open GoertzelV24TwoEdgeCutCapGeometry
open SimpleGraphDartRotation

universe u v

variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace RotationSystem.TwoEdgeCutSideData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutSideData)

/-- Transporting the old vertex permutation to an exact two-edge cap
preserves the fact that each vertex fiber is one cyclic order. -/
theorem capRotationSystem_vertexRotationCyclic
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic data.capRotationSystem := by
  intro left right hvertex
  let parts := retainedDartEquivMatchedParts RS data.keep
    (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
    data.boundaryCover data.cutsDisjoint
  have hunderlyingVertex :
      RS.vertOf (parts.symm left).1 = RS.vertOf (parts.symm right).1 := by
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS data.keep
      (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
      data.boundaryCover data.cutsDisjoint left]
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS data.keep
      (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
      data.boundaryCover data.cutsDisjoint right]
    change
      (data.capRotationSystem.vertOf left).1 =
        (data.capRotationSystem.vertOf right).1
    exact congrArg Subtype.val hvertex
  have hambient :
      RS.rho.SameCycle (parts.symm left).1 (parts.symm right).1 :=
    hcyclic _ _ hunderlyingVertex
  have hretained :
      (retainedRho RS data.keep).SameCycle
        (parts.symm left) (parts.symm right) :=
    Equiv.Perm.SameCycle.subtypePerm hambient
  rcases hretained with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  have hrho : data.capRotationSystem.rho =
      matchedPartsRho RS data.keep
        (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
        data.boundaryCover data.cutsDisjoint := by
    rfl
  rw [hrho]
  change
    ((parts.permCongr (retainedRho RS data.keep)) ^ power) left = right
  have hmap :
      parts.permCongr ((retainedRho RS data.keep) ^ power) =
        (parts.permCongr (retainedRho RS data.keep)) ^ power := by
    exact map_zpow parts.permCongrHom (retainedRho RS data.keep) power
  rw [← hmap]
  change parts (((retainedRho RS data.keep) ^ power)
    (parts.symm left)) = right
  rw [hpower, parts.apply_symm_apply]

end RotationSystem.TwoEdgeCutSideData

namespace RotationSystem.TwoEdgeCutPairData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutPairData)

/-- The chosen cap inherits cyclic vertex rotations. -/
theorem sideCap_vertexRotationCyclic
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic data.sideData.capRotationSystem := by
  apply RotationSystem.TwoEdgeCutSideData.capRotationSystem_vertexRotationCyclic
  simpa [RotationSystem.TwoEdgeCutPairData.sideRootedRotationSystem]
    using hcyclic

/-- The complementary cap inherits cyclic vertex rotations as well. -/
theorem complementCap_vertexRotationCyclic
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic data.complementData.capRotationSystem := by
  apply RotationSystem.TwoEdgeCutSideData.capRotationSystem_vertexRotationCyclic
  simpa [RotationSystem.TwoEdgeCutPairData.complementRootedRotationSystem]
    using hcyclic

end RotationSystem.TwoEdgeCutPairData

/-- Rotation-system Tait colorability, stated directly using the standard
proper edge-coloring and nonzero-color predicates. -/
def RotationSystemTaitColorable (RS : RotationSystem V E) : Prop :=
  ∃ coloring : RS.EdgeColoring Color, RS.IsTaitEdgeColoring coloring

/-- The cap-stable structural class used for vertex minimality: a connected
bridgeless cubic spherical rotation map with one cyclic order at each vertex. -/
structure BridgelessSphericalCubicMapData (RS : RotationSystem V E) where
  spherical : OrbitSphericalCubicMapData RS
  primalConnected : (rotationPrimalGraph RS).Connected
  vertexRotationCyclic : VertexRotationCyclic RS
  edgeBridgeFree : EdgeBridgeFree RS

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A counterexample minimal by vertex count among the same cap-stable class.
The two-sided-face field supplies the local spherical-map fact needed to
preserve Euler data under graph-backed capping. -/
structure GraphBackedVertexMinimalTaitCounterexample
    (graphData : Data G) : Type
    extends BridgelessSphericalCubicMapData graphData.toRotationSystem where
  facesTwoSided : OrbitFacesTwoSided graphData.toRotationSystem
  notColorable : ¬ RotationSystemTaitColorable graphData.toRotationSystem
  smallerColorable :
    ∀ {V' E' : Type u} [Fintype V'] [DecidableEq V']
      [Fintype E'] [DecidableEq E']
      (candidate : RotationSystem.{u, u, u} V' E'),
      Fintype.card V' < Fintype.card V →
      BridgelessSphericalCubicMapData candidate →
      RotationSystemTaitColorable candidate

/-- A graph-backed vertex-minimal Tait counterexample has no exact
non-colliding two-edge cut whose two induced sides are connected. Both capped
halves lie in the same structural class, have fewer vertices, and their Tait
colorings glue to one of the ambient map. -/
theorem no_connected_twoEdgeCutPairData
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : graphData.toRotationSystem.TwoEdgeCutPairData)
    (hsideConnected :
      (G.induce {vertex | vertex ∈ cut.side}).Connected)
    (hcomplementConnected :
      (G.induce {vertex | vertex ∈ cut.sideᶜ}).Connected) : False := by
  let RS := graphData.toRotationSystem
  have hsideConnectedRS :
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ cut.side}).Connected := by
    rw [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
    exact hsideConnected
  have hcomplementConnectedRS :
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ cut.sideᶜ}).Connected := by
    rw [GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq]
    exact hcomplementConnected
  have hgraphConnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  have hsideMap : BridgelessSphericalCubicMapData
      cut.sideData.capRotationSystem :=
    { spherical :=
        GoertzelV24TwoEdgeCutCapGeometry.RotationSystem.TwoEdgeCutPairData.sideCap_orbitSphericalCubicMapData
          graphData cut minimal.spherical minimal.facesTwoSided
          hgraphConnected
          minimal.vertexRotationCyclic hsideConnected hcomplementConnected
      primalConnected :=
        GoertzelV24TwoEdgeCutCapGeometry.RotationSystem.TwoEdgeCutPairData.sideCap_primal_connected
          cut hsideConnectedRS
      vertexRotationCyclic :=
        RotationSystem.TwoEdgeCutPairData.sideCap_vertexRotationCyclic
          cut minimal.vertexRotationCyclic
      edgeBridgeFree :=
        GoertzelV24TwoEdgeCutCapBridge.RotationSystem.TwoEdgeCutPairData.sideCap_edgeBridgeFree
          cut minimal.edgeBridgeFree hsideConnectedRS }
  have hcomplementMap : BridgelessSphericalCubicMapData
      cut.complementData.capRotationSystem :=
    { spherical :=
        GoertzelV24TwoEdgeCutCapGeometry.RotationSystem.TwoEdgeCutPairData.complementCap_orbitSphericalCubicMapData
          graphData cut minimal.spherical minimal.facesTwoSided
          hgraphConnected
          minimal.vertexRotationCyclic hsideConnected hcomplementConnected
      primalConnected :=
        GoertzelV24TwoEdgeCutCapGeometry.RotationSystem.TwoEdgeCutPairData.complementCap_primal_connected
          cut hcomplementConnectedRS
      vertexRotationCyclic :=
        RotationSystem.TwoEdgeCutPairData.complementCap_vertexRotationCyclic
          cut minimal.vertexRotationCyclic
      edgeBridgeFree :=
        GoertzelV24TwoEdgeCutCapBridge.RotationSystem.TwoEdgeCutPairData.complementCap_edgeBridgeFree
          cut minimal.edgeBridgeFree hcomplementConnectedRS }
  have hsideColorable :
      RotationSystemTaitColorable cut.sideData.capRotationSystem :=
    minimal.smallerColorable cut.sideData.capRotationSystem
      cut.card_sideCapVertex_lt hsideMap
  have hcomplementColorable :
      RotationSystemTaitColorable cut.complementData.capRotationSystem :=
    minimal.smallerColorable cut.complementData.capRotationSystem
      cut.card_complementCapVertex_lt hcomplementMap
  apply minimal.notColorable
  exact cut.taitColorable_of_caps hsideColorable hcomplementColorable

end

end GoertzelV24TwoEdgeCutMinimality

end Mettapedia.GraphTheory.FourColor
