import Mettapedia.GraphTheory.FourColor.SphericalContourBondChain

/-!
# Constructed contour bonds feed exact Count descent

The two terminal contours are cycles on opposite sides of each bond.
The existing incident-edge adapter therefore supplies connected shores
with nonempty majority sides. A crossing-dart equivalence bounds the
literal middle set by the original exposed-port count. No equality of a
majority side with the original vertex side is needed.

The constructed nested bonds become nested exact-support nodes. Pigeonhole
in their card-phased state then bounds the face-dual distance in an exact
mesh-free least counterexample. This is a distance bound, not yet a vertex
bound or a completed branch-decomposition theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24DeletedRegionRotationSplice GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter GoertzelV24MeshIsoperimetry
open GoertzelV24InjectiveMeshWidthExclusion GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24SimpleGraphTaitBridge
open GoertzelV24NormalizedShoreDescent GoertzelV24MajorityShoreStateDescent
open SphericalDistanceContours

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The two dart presentations have identical underlying oriented edges. -/
def crossingEquivBoundary (data : Data G) (side : V → Prop) :
    CrossingSideDart G side ≃ BoundaryDart data.toRotationSystem side where
  toFun d := ⟨⟨d.val, d.property.1⟩, d.property.2⟩
  invFun d := ⟨d.val.val, d.val.property, d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def OrderedContourBond.toConnectedNode (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {lo hi w : ℕ}
    (C : OrderedContourBond data root far lo hi w)
    (hlo : lo < (orbitFaceDualGraph data).dist root far)
    (hhi : hi < (orbitFaceDualGraph data).dist root far) :
    ConnectedShoreNode (G := G) w w := by
  classical
  have hinside : HasCycleOnSide G (deletedRegionKeep C.deleted) := by
    obtain ⟨a, p, hp, _, hv⟩ := exists_distance_contour data hclass htwo root far lo hlo
    exact ⟨a, C.first ((hv a).mp p.start_mem_support), p, hp, fun v h => C.first ((hv v).mp h)⟩
  have houtside : HasCycleOnSide G (fun v => ¬ deletedRegionKeep C.deleted v) := by
    obtain ⟨b, q, hq, _, hw⟩ := exists_distance_contour data hclass htwo root far hi hhi
    exact ⟨b, C.last ((hw b).mp q.start_mem_support), q, hq, fun v h => C.last ((hw v).mp h)⟩
  have hg := connected_edgeShores_and_nonempty_majoritySides_of_cycles
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data hclass.spherical.cubic)
    (deletedRegionKeep C.deleted) C.connected C.complement_connected hinside houtside
  have hwidth : (edgeShoreMiddleVertices G (incidentEdgeShore G (deletedRegionKeep C.deleted))).card ≤ w :=
    calc
      _ ≤ Fintype.card (CrossingSideDart G (deletedRegionKeep C.deleted)) :=
        card_middle_incidentEdgeShore_le_crossingSideDart _
      _ = Fintype.card (BoundaryDart data.toRotationSystem (deletedRegionKeep C.deleted)) :=
        Fintype.card_congr (crossingEquivBoundary data _)
      _ ≤ w := C.port_bound
  exact ⟨incidentEdgeShore G (deletedRegionKeep C.deleted), hg.1, hg.2.1,
    hg.2.2.1, hg.2.2.2, hwidth, hwidth⟩

@[simp] theorem OrderedContourBond.toConnectedNode_shore (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {lo hi w : ℕ}
    (C : OrderedContourBond data root far lo hi w) (hlo hhi) :
    (C.toConnectedNode data hclass htwo root far hlo hhi).shore =
      incidentEdgeShore G (deletedRegionKeep C.deleted) := rfl

/-- The exact varying-width state count already used by Count descent. -/
def contourStateBound (w : ℕ) : ℕ :=
  (6 * w + 1) * (∑ j : Fin (w + 1), Nat.factorial j.val * 2 ^ (3 ^ j.val))

theorem le_contourStateBound_of_nested_nodes (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data) {w n : ℕ}
    (nodes : Fin n → ConnectedShoreNode (G := G) w w)
    (hnested : ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore) :
    n ≤ contourStateBound w := by
  classical
  let f := fun i => (nodes i).cardPhasedState data minimal
  have hf : Function.Injective f := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact cardPhasedState_ne_of_ssubset data minimal
        ((nodes j).toLiteral data minimal) ((nodes i).toLiteral data minimal)
        (hnested i j hij) heq.symm
    · exact cardPhasedState_ne_of_ssubset data minimal
        ((nodes i).toLiteral data minimal) ((nodes j).toLiteral data minimal)
        (hnested j i hji) heq
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_prod, card_stateAtBound, contourStateBound] using hc

/-- No geometric chain is assumed: distance and mesh exclusion supply it. -/
theorem exists_nested_contour_nodes (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (root far : OrbitFace data.toRotationSystem) (a b n : ℕ)
    (ha : 2 ≤ a) (hd : n * a ≤ (orbitFaceDualGraph data).dist root far)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G) (3 * (b - 1)) (3 * (b - 1)),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore := by
  classical
  obtain ⟨cuts, hnested⟩ := exists_nested_contour_bonds data
    minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided root far a b n ha hd hno
  have hdepth (t : Fin n) : t.val * a + a ≤ (orbitFaceDualGraph data).dist root far := by
    have hmul := Nat.mul_le_mul_right a (Nat.succ_le_of_lt t.isLt)
    simp only [Nat.succ_mul] at hmul
    exact hmul.trans hd
  let nodes := fun t => (cuts t).toConnectedNode data minimal.toBridgelessSphericalCubicMapData
    minimal.facesTwoSided root far (by have := hdepth t; omega) (by have := hdepth t; omega)
  exact ⟨nodes, fun i j hij => (hnested i j hij).2⟩

/-- Exact mesh-free least counterexamples have explicitly bounded dual diameter. -/
theorem dual_distance_lt_of_no_injectiveMesh (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (root far : OrbitFace data.toRotationSystem) (a b : ℕ)
    (ha : 2 ≤ a)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) :
    (orbitFaceDualGraph data).dist root far < (contourStateBound (3 * (b - 1)) + 1) * a := by
  classical
  by_contra hn
  obtain ⟨nodes, hnested⟩ := exists_nested_contour_nodes data minimal root far a b
    (contourStateBound (3 * (b - 1)) + 1) ha (Nat.le_of_not_gt hn) hno
  have := le_contourStateBound_of_nested_nodes data minimal nodes hnested
  omega

end
end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
