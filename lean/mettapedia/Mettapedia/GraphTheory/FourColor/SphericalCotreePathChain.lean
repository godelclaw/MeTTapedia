import Mettapedia.GraphTheory.FourColor.TreePathShore
import Mettapedia.GraphTheory.FourColor.SphericalCotreeShore

/-!
# Large primal cotrees supply nested cyclic cuts

A bounded-degree long path supplies fundamental shores. The complete-cut
bound controls their width, while discarding both short ends leaves enough
vertices that cubic counting forces a cycle on each shore. These actual
cuts feed the connected-shore node constructor and exact Count descent.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalCotreePathChain

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24FramedLocalDualCycleBond GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24RotationMultigraphAdapter GoertzelV24MeshIsoperimetry
open GoertzelV24InjectiveMeshWidthExclusion
open SphericalDualBFSTree SphericalCotreeShore SphericalContourSeparators

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A connected acyclic cubic shore has at most boundary minus two vertices. -/
theorem hasCycle_of_boundary_lt_card (hcubic : ∀ v, G.degree v = 3)
    (side : V → Prop) (hconn : (G.induce side).Connected)
    (hlarge : (localCrossingEdgeFinset G side).card < Nat.card {v // side v}) :
    HasCycleOnSide G side := by
  classical
  have hcross : ∀ d : CrossingSideDart G side,
      (⟨d.val.edge, d.val.edge_mem⟩ : G.edgeSet) ∈ localCrossingEdgeFinset G side := by
    intro d
    apply (mem_localCrossingEdgeFinset_iff side _).mpr
    exact ⟨d.val.fst, d.val.snd, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _,
      d.property.1, d.property.2⟩
  have h := hasCycleOnSide_or_card_le_two_mul_exception_add_removed_sub_two
    side (fun _ => False) (by simp) (fun v _ _ => hcubic v) hconn
    (localCrossingEdgeFinset G side) hcross
  rcases h with h | h
  · exact h
  · simp only [Finset.filter_false, Finset.card_empty, mul_zero, zero_add] at h
    rw [Nat.card_eq_fintype_card] at hlarge
    omega

omit [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem crossing_complement (side : V → Prop) :
    localCrossingEdgeFinset G (fun v => ¬ side v) = localCrossingEdgeFinset G side := by
  ext e
  simp only [mem_localCrossingEdgeFinset_iff, edgeCrossesVertexSide_compl]

variable {data : Data G} {root : OrbitFace data.toRotationSystem}

omit [G.LocallyFinite] in
/-- The path's start component is the explicit bounded cotree shore. -/
theorem path_shore_bounds (T : DualBFSTree data root)
    (htree : T.toRankedDualForest.complementGraph.IsTree)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    {a b : V} (p : T.toRankedDualForest.complementGraph.Walk a b) (hp : p.IsPath)
    {i : ℕ} (hi : i < p.length) (h : ℕ)
    (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h) :
    (G.induce (TreePathShore.shore p i)).Connected ∧
      (G.induce (TreePathShore.shore p i)ᶜ).Connected ∧
      (localCrossingEdgeFinset G (TreePathShore.shore p i)).card ≤ 2 * h + 1 := by
  have hs := bounded_fundamental_shore T htree htwo
    (p.getVert i) (p.getVert (i + 1)) (p.adj_getVert_succ hi) h hradius
  rw [TreePathShore.shore_eq_endpoint_region p hp hi]
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1⟩

/-- A long cotree path supplies actual nested nodes using spherical geometry
alone, before imposing any zero-Count or vertex-minimality assumption. -/
theorem exists_nested_nodes_of_long_path_of_spherical (T : DualBFSTree data root)
    (htree : T.toRankedDualForest.complementGraph.IsTree)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (h : ℕ) (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h)
    {a b : V} (p : T.toRankedDualForest.complementGraph.Walk a b) (hp : p.IsPath)
    (n : ℕ) (hlen : n + 2 * (2 * h + 1) ≤ p.length) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G) (2 * h + 1) (2 * h + 1),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore := by
  classical
  let w := 2 * h + 1
  let idx : Fin n → ℕ := fun i => w + i.val
  have hi : ∀ i, idx i < p.length := by intro i; dsimp [idx, w]; omega
  let sides : Fin n → Set V := fun i => TreePathShore.shore p (idx i)
  have hprops := fun i => path_shore_bounds T htree htwo p hp (hi i) h hradius
  have hcubic : ∀ v, G.degree v = 3 := by
    intro v
    exact (degree_instance_independent v _ (Subtype.fintype _)).trans
      (by
        letI : G.LocallyFinite := fun _ => Subtype.fintype _
        exact (data.toRotationSystem_isCubic_iff.mp hclass.spherical.cubic).degree_eq v)
  have hinside : ∀ i, HasCycleOnSide G (sides i) := by
    intro i
    apply hasCycle_of_boundary_lt_card hcubic (sides i) (hprops i).1
    have hc := TreePathShore.prefix_card_le p hp (hi i)
    have hw := (hprops i).2.2
    change (localCrossingEdgeFinset G (TreePathShore.shore p (idx i))).card <
      Nat.card (TreePathShore.shore p (idx i))
    have hidx : 2 * h + 1 ≤ idx i := by dsimp [idx, w]; omega
    omega
  have houtside : ∀ i, HasCycleOnSide G (fun v => v ∉ sides i) := by
    intro i
    apply hasCycle_of_boundary_lt_card hcubic (fun v => v ∉ sides i) (hprops i).2.1
    rw [crossing_complement]
    have hc := TreePathShore.suffix_card_le htree p hp (hi i)
    have hw := (hprops i).2.2
    change (localCrossingEdgeFinset G (TreePathShore.shore p (idx i))).card <
      Nat.card ↥(TreePathShore.shore p (idx i))ᶜ
    have hidx : idx i < 2 * h + 1 + n := by dsimp [idx, w]; omega
    omega
  let cuts : ∀ i : Fin n, CyclicEdgeCutRealization G (localCrossingEdgeFinset G (sides i)) :=
    fun i => ⟨sides i, mem_localCrossingEdgeFinset_iff _, hinside i, houtside i⟩
  let nodes := fun i => (cuts i).toConnectedShoreNodeOfConnectedSides
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data hclass.spherical.cubic)
    (hprops i).1 (hprops i).2.1 w (hprops i).2.2
  refine ⟨nodes, ?_⟩
  intro i j hij
  have hss := TreePathShore.shore_ssubset htree p hp
    (show idx i < idx j by dsimp [idx]; exact Nat.add_lt_add_left hij w) (hi j)
  have hnew : ∃ v, v ∈ sides j ∧ v ∉ sides i := Set.exists_of_ssubset hss
  change incidentEdgeShore G (sides i) ⊂ incidentEdgeShore G (sides j)
  exact NestedCyclicCutStrictness.incidentEdgeShore_ssubset (fun _ hv => hss.1 hv)
    hnew ⟨b, TreePathShore.end_not_mem htree p hp (hi j)⟩ (hprops i).2.1.preconnected

/-- Compatibility with the original target-class path supplier. -/
theorem exists_nested_nodes_of_long_path (T : DualBFSTree data root)
    (htree : T.toRankedDualForest.complementGraph.IsTree)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (h : ℕ) (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h)
    {a b : V} (p : T.toRankedDualForest.complementGraph.Walk a b) (hp : p.IsPath)
    (n : ℕ) (hlen : n + 2 * (2 * h + 1) ≤ p.length) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G) (2 * h + 1) (2 * h + 1),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore :=
  exists_nested_nodes_of_long_path_of_spherical T htree
    minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided h hradius p hp n hlen

/-- Large vertex count constructs the cotree, path and full nested cuts from
spherical geometry alone. -/
theorem exists_nested_nodes_of_large_card_of_spherical (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root : OrbitFace data.toRotationSystem) (h n : ℕ)
    (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h)
    (hlarge : 4 ^ (n + 2 * (2 * h + 1)) < Fintype.card V) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G) (2 * h + 1) (2 * h + 1),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore := by
  classical
  let T := of_connected data
    (orbitFaceDualGraph_connected data hclass) root
  let H := T.toRankedDualForest.complementGraph
  letI : H.LocallyFinite := fun _ => Subtype.fintype _
  have htree : H.IsTree := of_connected_complement_isTree data
    hclass htwo root
  have hdegree : ∀ v, H.degree v ≤ 3 := by
    intro v
    have hG : G.degree v = 3 := by
      exact (degree_instance_independent v _ (Subtype.fintype _)).trans
        (by
          letI : G.LocallyFinite := fun _ => Subtype.fintype _
          exact (data.toRotationSystem_isCubic_iff.mp hclass.spherical.cubic).degree_eq v)
    exact (SimpleGraph.degree_le_of_le (G := H) (SimpleGraph.deleteEdges_le _)).trans hG.le
  obtain ⟨a, b, p, hp, _, hlen⟩ :=
    GoertzelV24BoundedDegreePath.exists_geodesicPath_length_ge_of_pow_lt_card
      H htree.connected 3 (n + 2 * (2 * h + 1)) hdegree hlarge
  exact exists_nested_nodes_of_long_path_of_spherical T htree hclass htwo h hradius p hp n hlen

/-- Compatibility with the original target-class cardinality supplier. -/
theorem exists_nested_nodes_of_large_card (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (root : OrbitFace data.toRotationSystem) (h n : ℕ)
    (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h)
    (hlarge : 4 ^ (n + 2 * (2 * h + 1)) < Fintype.card V) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G) (2 * h + 1) (2 * h + 1),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore :=
  exists_nested_nodes_of_large_card_of_spherical data
    minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided root h n hradius hlarge

/-- Explicit size threshold supplied by mesh exclusion and complete cotree cuts. -/
def meshFreeVertexBound (a b : ℕ) : ℕ :=
  4 ^ (contourStateBound (meshFreeCotreeWidth a b) + 1 + 2 * meshFreeCotreeWidth a b)

/-- The exact mesh-free target class is bounded without a face-size assumption. -/
theorem vertex_card_le_of_no_injectiveMesh (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (a b : ℕ) (ha : 2 ≤ a)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) :
    Fintype.card V ≤ meshFreeVertexBound a b := by
  classical
  let root := dartOrbitFace data.toRotationSystem data.toRotationSystem.outer
  let h := (contourStateBound (3 * (b - 1)) + 1) * a
  have hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h := by
    intro f
    exact Nat.le_of_lt (dual_distance_lt_of_no_injectiveMesh data minimal f root a b ha hno)
  by_contra hlarge
  have hlarge' : 4 ^ ((contourStateBound (2 * h + 1) + 1) + 2 * (2 * h + 1)) <
      Fintype.card V := Nat.lt_of_not_ge hlarge
  obtain ⟨nodes, hnested⟩ := exists_nested_nodes_of_large_card data minimal root h
    (contourStateBound (2 * h + 1) + 1) hradius hlarge'
  have := le_contourStateBound_of_nested_nodes data minimal nodes hnested
  omega

/-- The positive structural alternative: every larger target instance supplies a mesh. -/
theorem exists_injectiveMesh_of_large_card (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (a b : ℕ) (ha : 2 ≤ a) (hlarge : meshFreeVertexBound a b < Fintype.card V) :
    ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M := by
  by_contra hno
  exact (Nat.not_lt_of_ge (vertex_card_le_of_no_injectiveMesh data minimal a b ha hno)) hlarge

end
end Mettapedia.GraphTheory.FourColor.SphericalCotreePathChain
