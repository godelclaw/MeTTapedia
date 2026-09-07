import Mettapedia.GraphTheory.FourColor.SphericalCotreeCutWidth
import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond
import Mettapedia.GraphTheory.FourColor.SphericalContourNodeChain

/-!
# Complete bounded shores from primal cotree edges

Delete one edge of the constructed primal tree and take an endpoint's
reachable region. Both induced original shores are connected, and the
entire original cut meets the primal tree in exactly the deleted edge.
The dual BFS parity theorem therefore bounds its full width.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalCotreeShore

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open GoertzelV24FramedLocalDualCycleBond
open SphericalDualBFSTree SphericalCotreeCutWidth
open SphericalContourSeparators GoertzelV24RotationMultigraphAdapter
open GoertzelV24MeshIsoperimetry GoertzelV24InjectiveMeshWidthExclusion

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

omit [Fintype V] in
/-- Deleting one edge of a connected graph leaves at most its two endpoint regions. -/
theorem reachable_or_reachable_after_delete (H : SimpleGraph V) (hconn : H.Connected)
    (u v w : V) :
    (H.deleteEdges {s(u, v)}).Reachable u w ∨ (H.deleteEdges {s(u, v)}).Reachable v w := by
  let K := H.deleteEdges {s(u, v)}
  have hstep : ∀ {a b}, H.Adj a b →
      (K.Reachable u a ∨ K.Reachable v a) → (K.Reachable u b ∨ K.Reachable v b) := by
    intro a b hab hreach
    by_cases he : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr .rfl
      · exact Or.inl .rfl
    · have ha : K.Adj a b := by
        exact SimpleGraph.deleteEdges_adj.mpr ⟨hab, he⟩
      exact hreach.imp (fun h => h.trans ha.reachable) (fun h => h.trans ha.reachable)
  have hwalk : ∀ {a b} (p : H.Walk a b),
      (K.Reachable u a ∨ K.Reachable v a) → (K.Reachable u b ∨ K.Reachable v b) := by
    intro a b p
    induction p with
    | nil => exact id
    | cons ha p ih => exact fun h => ih (hstep ha h)
  obtain ⟨p⟩ := hconn u w
  exact hwalk p (Or.inl .rfl)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A reachable region of a spanning subgraph is connected in the original graph. -/
theorem connected_reachable_region (K : SimpleGraph V) (hKG : K ≤ G) (u : V) :
    (G.induce {w | K.Reachable u w}).Connected := by
  apply VertexSeparatorBond.connected_of_walks G (a := u) (show K.Reachable u u from .rfl)
  intro w hw
  obtain ⟨p⟩ := hw
  refine ⟨p.map (SimpleGraph.Hom.ofLE hKG), ?_⟩
  intro a ha
  have hmem : a ∈ p.support := by
    change a ∈ (p.map (SimpleGraph.Hom.ofLE hKG)).support at ha
    rw [SimpleGraph.Walk.support_map, List.mem_map] at ha
    obtain ⟨b, hb, hab⟩ := ha
    exact hab ▸ hb
  exact ⟨p.takeUntil a hmem⟩

variable {data : Data G} {root : OrbitFace data.toRotationSystem}

/-- The endpoint component of a deleted primal-tree edge has full bounded boundary. -/
theorem bounded_fundamental_shore (T : DualBFSTree data root)
    (htree : T.toRankedDualForest.complementGraph.IsTree)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (u v : V) (huv : T.toRankedDualForest.complementGraph.Adj u v)
    (h : ℕ) (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h) :
    let side := (T.toRankedDualForest.complementGraph.deleteEdges {s(u, v)}).Reachable u
    ¬ side v ∧
      (G.induce {w | side w}).Connected ∧ (G.induce {w | ¬ side w}).Connected ∧
      (localCrossingEdgeFinset G side).card ≤ 2 * h + 1 ∧
      localCrossingEdgeFinset G side \ T.edges = {⟨s(u, v), huv.1⟩} := by
  classical
  let H := T.toRankedDualForest.complementGraph
  let K := H.deleteEdges {s(u, v)}
  let side : V → Prop := K.Reachable u
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hKG : K ≤ G := (SimpleGraph.deleteEdges_le _).trans hHG
  have hbridge : H.IsBridge s(u, v) :=
    SimpleGraph.isAcyclic_iff_forall_isBridge.mp htree.isAcyclic (by simpa using huv)
  have hnot : ¬ side v := SimpleGraph.isBridge_iff.mp hbridge
  have hside : (G.induce {w | side w}).Connected := connected_reachable_region K hKG u
  have hcomp : (G.induce {w | ¬ side w}).Connected := by
    have heq : {w | ¬ side w} = {w | K.Reachable v w} := by
      ext w
      constructor
      · intro hw
        exact (reachable_or_reachable_after_delete H htree.connected u v w).resolve_left hw
      · intro hw hu
        exact hnot (hu.trans hw.symm)
    rw [heq]
    exact connected_reachable_region K hKG v
  let e : G.edgeSet := ⟨s(u, v), hHG huv⟩
  have heNot : e ∉ T.edges := (T.toRankedDualForest.complement_adj_iff (hHG huv)).mp huv
  have heCut : e ∈ localCrossingEdgeFinset G side := by
    apply (mem_localCrossingEdgeFinset_iff side e).mpr
    exact ⟨u, v, by simp [e], by simp [e], .rfl, hnot⟩
  have hout : localCrossingEdgeFinset G side \ T.edges = {e} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨heCut, heNot⟩, ?_⟩
    intro a ha
    obtain ⟨hcut, hnotTree⟩ := Finset.mem_sdiff.mp ha
    have hcross := (mem_localCrossingEdgeFinset_iff side a).mp hcut
    obtain ⟨edge, hedge⟩ := a
    induction edge using Sym2.ind with
    | h a b =>
      by_contra hne
      have hne' : s(a, b) ≠ s(u, v) := fun heq => hne (Subtype.ext heq)
      have hHab : H.Adj a b := (T.toRankedDualForest.complement_adj_iff hedge).mpr hnotTree
      have hKab : K.Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨hHab, hne'⟩
      apply (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq rfl hcross)
      exact ⟨fun ha => ha.trans hKab.reachable, fun hb => hb.trans hKab.symm.reachable⟩
  refine ⟨hnot, hside, hcomp, ?_, hout⟩
  exact crossing_card_le_of_singleton_sdiff T htwo side e hout h hradius

/-- Every edge of the primal tree supplies a full connected-shore cut of bounded width. -/
theorem exists_bounded_fundamental_shore (T : DualBFSTree data root)
    (htree : T.toRankedDualForest.complementGraph.IsTree)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (u v : V) (huv : T.toRankedDualForest.complementGraph.Adj u v)
    (h : ℕ) (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h) :
    ∃ side : V → Prop, side u ∧ ¬ side v ∧
      (G.induce {w | side w}).Connected ∧ (G.induce {w | ¬ side w}).Connected ∧
      (localCrossingEdgeFinset G side).card ≤ 2 * h + 1 ∧
      localCrossingEdgeFinset G side \ T.edges = {⟨s(u, v), huv.1⟩} := by
  exact ⟨_, .rfl, bounded_fundamental_shore T htree htwo u v huv h hradius⟩

/-- Instantiate the complete-shore construction with the actual dual BFS tree. -/
theorem exists_bounded_cotree_shore (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root : OrbitFace data.toRotationSystem) (h : ℕ)
    (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h)
    (u v : V)
    (huv : (of_connected data (orbitFaceDualGraph_connected data hclass) root).toRankedDualForest.complementGraph.Adj u v) :
    ∃ side : V → Prop, side u ∧ ¬ side v ∧
      (G.induce {w | side w}).Connected ∧ (G.induce {w | ¬ side w}).Connected ∧
      (localCrossingEdgeFinset G side).card ≤ 2 * h + 1 := by
  let T := of_connected data (orbitFaceDualGraph_connected data hclass) root
  obtain ⟨side, hu, hv, hs, hc, hw, _⟩ := exists_bounded_fundamental_shore T
    (of_connected_complement_isTree data hclass htwo root) htwo u v huv h hradius
  exact ⟨side, hu, hv, hs, hc, hw⟩

/-- The explicit full-cut width obtained from the mesh-free dual-distance bound. -/
def meshFreeCotreeWidth (a b : ℕ) : ℕ :=
  2 * ((contourStateBound (3 * (b - 1)) + 1) * a) + 1

/-- In the target class the radius, too, is supplied by the existing mesh theorem. -/
theorem exists_bounded_cotree_shore_of_no_injectiveMesh [G.LocallyFinite]
    (data : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (root : OrbitFace data.toRotationSystem) (a b : ℕ) (ha : 2 ≤ a)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M)
    (u v : V)
    (huv : (of_connected data
      (orbitFaceDualGraph_connected data minimal.toBridgelessSphericalCubicMapData)
      root).toRankedDualForest.complementGraph.Adj u v) :
    ∃ side : V → Prop, side u ∧ ¬ side v ∧
      (G.induce {w | side w}).Connected ∧ (G.induce {w | ¬ side w}).Connected ∧
      (localCrossingEdgeFinset G side).card ≤ meshFreeCotreeWidth a b := by
  apply exists_bounded_cotree_shore data minimal.toBridgelessSphericalCubicMapData
    minimal.facesTwoSided root ((contourStateBound (3 * (b - 1)) + 1) * a) ?_ u v huv
  intro f
  exact Nat.le_of_lt (dual_distance_lt_of_no_injectiveMesh data minimal f root a b ha hno)

end
end Mettapedia.GraphTheory.FourColor.SphericalCotreeShore
