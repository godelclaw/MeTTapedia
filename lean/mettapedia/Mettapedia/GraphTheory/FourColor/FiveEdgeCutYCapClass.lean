import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapEuler
import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The Y-capped shore is in the cap-stable class, and minimality colours it

With the structural ladder assembled — spherical Euler data, primal
connectivity, cyclic rotations, bridge-freeness — the Y-capped shore lies
in the cap-stable class.  When the deleted side has at least two vertices
the replacement is strictly smaller, so a graph-backed vertex-minimal Tait
counterexample colours it.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace FiveEdgeCutYCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutYCapData RS)

/-- Two deleted vertices make the Y-capped carrier strictly smaller. -/
theorem card_capVertex_lt
    (removedLeft removedRight : V) (hne : removedLeft ≠ removedRight)
    (hleft : ¬ data.keep removedLeft) (hright : ¬ data.keep removedRight) :
    Fintype.card data.CapVertex < Fintype.card V := by
  classical
  have hcap := data.card_capVertex
  have hretained : Fintype.card (RetainedVertex data.keep) =
      (Finset.univ.filter data.keep).card := by
    rw [Fintype.card_subtype]
  have hdisjoint : Disjoint (Finset.univ.filter data.keep)
      ({removedLeft, removedRight} : Finset V) := by
    rw [Finset.disjoint_right]
    intro vertex hvertex
    rcases Finset.mem_insert.mp hvertex with rfl | hvertex
    · simp only [Finset.mem_filter]
      rintro ⟨-, hkeep⟩
      exact hleft hkeep
    · rcases Finset.mem_singleton.mp hvertex with rfl
      simp only [Finset.mem_filter]
      rintro ⟨-, hkeep⟩
      exact hright hkeep
  have hunion :
      (Finset.univ.filter data.keep).card + 2 ≤ Fintype.card V := by
    have hpair : ({removedLeft, removedRight} : Finset V).card = 2 :=
      Finset.card_pair hne
    calc
      (Finset.univ.filter data.keep).card + 2 =
          ((Finset.univ.filter data.keep) ∪
            {removedLeft, removedRight}).card := by
        rw [Finset.card_union_of_disjoint hdisjoint, hpair]
      _ ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetFintypeClass : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEqClass : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The Y-capped shore of a graph-backed spherical bond lies in the
cap-stable structural class. -/
def capBridgelessSphericalCubicMapData
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (capData : FiveEdgeCutYCapData rotation.toRotationSystem)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hsucc : retainedRegionBoundarySuccessor rotation.toRotationSystem
        capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ deletedRegionKeep deleted vertex}).Connected)
    (hkeep : capData.keep = deletedRegionKeep deleted)
    (hretainedAmbient :
      (retainedAmbientPrimalGraph rotation.toRotationSystem
        capData.keep).Connected)
    (hdetour : ∀ removed : InternalDart rotation.toRotationSystem
        capData.keep,
      (capData.internalDetourGraph removed).Reachable
        (rotation.toRotationSystem.vertOf removed.1.1)
        (rotation.toRotationSystem.vertOf
          (rotation.toRotationSystem.alpha removed.1.1))) :
    GoertzelV24TwoEdgeCutMinimality.BridgelessSphericalCubicMapData
      capData.capRotationSystem where
  spherical := capData.cap_orbitSphericalCubicMapData_of_planarBond
    rotation deleted hsphere htwoSided hconnected hrotation hsucc
    hretainedConnected hdeletedConnected hkeep
  primalConnected :=
    capData.capRotationSystem_primalConnected hretainedAmbient
  vertexRotationCyclic :=
    capData.capRotationSystem_vertexRotationCyclic hrotation
  edgeBridgeFree :=
    capData.capRotationSystem_edgeBridgeFree hretainedAmbient hdetour

/-- Vertex minimality colours the Y-capped shore. -/
theorem capTaitColorable_of_vertexMinimal
    (rotation : SimpleGraphDartRotation.Data G)
    (deleted : Finset V)
    (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample
      rotation)
    (capData : FiveEdgeCutYCapData rotation.toRotationSystem)
    (hsucc : retainedRegionBoundarySuccessor rotation.toRotationSystem
        capData.keep =
      capData.crossingBoundaryDartEquiv.permCongr (finRotate 5)⁻¹)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep deleted vertex}).Connected)
    (hdeletedConnected :
      (G.induce {vertex |
        ¬ deletedRegionKeep deleted vertex}).Connected)
    (hkeep : capData.keep = deletedRegionKeep deleted)
    (hretainedAmbient :
      (retainedAmbientPrimalGraph rotation.toRotationSystem
        capData.keep).Connected)
    (hdetour : ∀ removed : InternalDart rotation.toRotationSystem
        capData.keep,
      (capData.internalDetourGraph removed).Reachable
        (rotation.toRotationSystem.vertOf removed.1.1)
        (rotation.toRotationSystem.vertOf
          (rotation.toRotationSystem.alpha removed.1.1)))
    (removedLeft removedRight : V) (hne : removedLeft ≠ removedRight)
    (hleft : ¬ capData.keep removedLeft)
    (hright : ¬ capData.keep removedRight) :
    GoertzelV24TwoEdgeCutMinimality.RotationSystemTaitColorable
      capData.capRotationSystem := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G rotation]
    exact minimal.primalConnected
  apply minimal.smallerColorable capData.capRotationSystem
    (capData.card_capVertex_lt removedLeft removedRight hne hleft hright)
  exact capData.capBridgelessSphericalCubicMapData rotation deleted
    minimal.spherical minimal.facesTwoSided hconnected
    minimal.vertexRotationCyclic hsucc hretainedConnected
    hdeletedConnected hkeep hretainedAmbient hdetour

end FiveEdgeCutYCapData

end

end Mettapedia.GraphTheory.FourColor
