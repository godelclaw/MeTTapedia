import Mathlib.Combinatorics.SimpleGraph.Metric
import Mettapedia.GraphTheory.FourColor.RankedDualForestComplement
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond

/-!
# A dual BFS tree on original edges

Every nonroot quotient face chooses an adjacent predecessor at distance one
less and an original edge shared with that predecessor. Two different faces
cannot choose the same edge: its two incidences would force their distances
to decrease in both directions. The selected ranked forest has exactly one
edge per nonroot face. Spherical Euler then makes its primal complement a
spanning tree, using the generic ranked-forest complement theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalDualBFSTree

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphTaitBridge RankedDualForestComplement
open GoertzelV24SimpleGraphFaceDualConnectedness

noncomputable section

/-- The first edge of a shortest walk goes one step closer to the root. -/
theorem exists_adj_dist_pred {F : Type*} (H : SimpleGraph F)
    (hconn : H.Connected) (root v : F) (hne : v ≠ root) :
    ∃ p, H.Adj v p ∧ H.dist p root + 1 = H.dist v root := by
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist v root
  cases q with
  | nil => exact (hne rfl).elim
  | @cons v p root h q =>
    refine ⟨p, h, ?_⟩
    have hle := SimpleGraph.dist_le q
    have htri := hconn.dist_triangle (u := v) (v := p) (w := root)
    have hone := SimpleGraph.dist_eq_one_iff_adj.mpr h
    simp only [SimpleGraph.Walk.length_cons] at hq
    omega

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two distinct incident quotient faces exhaust the incidence of an edge. -/
theorem edge_incidence_iff_pair (data : Data G) (e : G.edgeSet)
    {f g : OrbitFace data.toRotationSystem} (hne : f ≠ g)
    (hf : e ∈ orbitFaceBoundary data.toRotationSystem f)
    (hg : e ∈ orbitFaceBoundary data.toRotationSystem g)
    (a : OrbitFace data.toRotationSystem) :
    e ∈ orbitFaceBoundary data.toRotationSystem a ↔ f = a ∨ g = a := by
  classical
  let S := Finset.univ.filter fun h => e ∈ orbitFaceBoundary data.toRotationSystem h
  have hle : S.card ≤ 2 := orbitFace_totalIncidenceCount_le_two data.toRotationSystem e
  have hsub : ({f, g} : Finset (OrbitFace data.toRotationSystem)) ⊆ S := by
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl <;> simp [S, hf, hg]
  have hpair : ({f, g} : Finset (OrbitFace data.toRotationSystem)).card = 2 := by
    simp [hne]
  have heq : S = {f, g} :=
    (Finset.eq_of_subset_of_card_le hsub (hpair ▸ hle)).symm
  have ha : e ∈ orbitFaceBoundary data.toRotationSystem a ↔ a ∈ S := by simp [S]
  rw [ha, heq]
  simp [eq_comm]

/-- A face-rooted ranked forest with shortest-path ranks and full coverage. -/
structure DualBFSTree (data : Data G) (root : OrbitFace data.toRotationSystem)
    extends RankedDualForest data where
  rank_eq : rank = fun f => (orbitFaceDualGraph data).dist f root
  step : ∀ e ∈ edges, rank (parent e) + 1 = rank (child e)
  covers : ∀ f, f ≠ root → ∃ e ∈ edges, child e = f
  size : edges.card + 1 = Fintype.card (OrbitFace data.toRotationSystem)

/-- Construct the selected original edges from connected dual geometry alone. -/
def of_connected (data : Data G) (hconn : (orbitFaceDualGraph data).Connected)
    (root : OrbitFace data.toRotationSystem) : DualBFSTree data root := by
  classical
  let F := OrbitFace data.toRotationSystem
  let X := {f : F // f ≠ root}
  let rank : F → ℕ := fun f => (orbitFaceDualGraph data).dist f root
  have hex : ∀ x : X, ∃ p : F, ∃ e : G.edgeSet,
      rank p + 1 = rank x.val ∧ x.val ≠ p ∧
      e ∈ orbitFaceBoundary data.toRotationSystem x.val ∧
      e ∈ orbitFaceBoundary data.toRotationSystem p := by
    intro x
    obtain ⟨p, hp, hd⟩ := exists_adj_dist_pred (orbitFaceDualGraph data) hconn root x.val x.property
    obtain ⟨hne, e, _, hx, he⟩ := (interiorDualGraph_adj_iff _ _).mp hp
    exact ⟨p, e, hd, hne, hx, he⟩
  choose pred edge hdist hne hchild hparent using hex
  have hinc : ∀ x : X, ∀ f : F,
      edge x ∈ orbitFaceBoundary data.toRotationSystem f ↔ x.val = f ∨ pred x = f :=
    fun x f => edge_incidence_iff_pair data (edge x) (hne x) (hchild x) (hparent x) f
  have hinj : Function.Injective edge := by
    intro x y heq
    by_cases hxy : x.val = y.val
    · exact Subtype.ext hxy
    · have hyx := (hinc x y.val).mp (heq ▸ hchild y)
      have hxy' := (hinc y x.val).mp (heq ▸ hchild x)
      have hpy : pred x = y.val := hyx.resolve_left hxy
      have hpx : pred y = x.val := hxy'.resolve_left (Ne.symm hxy)
      have hx := hdist x
      have hy := hdist y
      rw [hpy] at hx
      rw [hpx] at hy
      omega
  let edges := Finset.univ.image edge
  let child := Function.extend edge (fun x : X => x.val) (fun _ => root)
  let parent := Function.extend edge pred (fun _ => root)
  have hc : ∀ x, child (edge x) = x.val := hinj.extend_apply _ _
  have hp : ∀ x, parent (edge x) = pred x := hinj.extend_apply _ _
  have hmem : ∀ e, e ∈ edges ↔ ∃ x : X, edge x = e := by simp [edges]
  have hsize : edges.card + 1 = Fintype.card F := by
    have hcX : Fintype.card X = Fintype.card F - 1 := by
      simp [X, Fintype.card_subtype_compl]
    have hpos : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨root⟩
    have hcE : edges.card = Fintype.card X := by
      simp only [edges, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    omega
  refine
    { edges := edges
      child := child
      parent := parent
      rank := rank
      child_injective := ?_
      descending := ?_
      incidence := ?_
      rank_eq := rfl
      step := ?_
      covers := ?_
      size := hsize }
  · intro e he f hf hef
    obtain ⟨x, rfl⟩ := (hmem e).mp he
    obtain ⟨y, rfl⟩ := (hmem f).mp hf
    rw [hc, hc] at hef
    exact congrArg edge (Subtype.ext hef)
  · intro e he
    obtain ⟨x, rfl⟩ := (hmem e).mp he
    rw [hp, hc]
    have := hdist x
    omega
  · intro e he f
    obtain ⟨x, rfl⟩ := (hmem e).mp he
    rw [hp, hc]
    exact hinc x f
  · intro e he
    obtain ⟨x, rfl⟩ := (hmem e).mp he
    rw [hp, hc]
    exact hdist x
  · intro f hf
    exact ⟨edge ⟨f, hf⟩, (hmem _).mpr ⟨⟨f, hf⟩, rfl⟩, hc _⟩

namespace DualBFSTree

variable {data : Data G} {root : OrbitFace data.toRotationSystem}
  (T : DualBFSTree data root)

/-- The selected face graph remembers adjacency via the original chosen edges. -/
def faceGraph : SimpleGraph (OrbitFace data.toRotationSystem) where
  Adj f g := ∃ e ∈ T.edges,
    (T.child e = f ∧ T.parent e = g) ∨ (T.child e = g ∧ T.parent e = f)
  symm := ⟨by
    rintro f g ⟨e, he, h⟩
    exact ⟨e, he, h.symm⟩⟩
  loopless := ⟨by
    rintro f ⟨e, he, h⟩
    have hd := T.descending e he
    rcases h with h | h <;> rw [h.1, h.2] at hd <;> exact (Nat.lt_irrefl _ hd)⟩

local instance faceGraphDecidableRel : DecidableRel T.faceGraph.Adj := Classical.decRel _

theorem child_parent_adj (e : G.edgeSet) (he : e ∈ T.edges) :
    T.faceGraph.Adj (T.child e) (T.parent e) := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

/-- The selected face graph is a spanning subgraph of the actual full dual. -/
theorem faceGraph_le : T.faceGraph ≤ orbitFaceDualGraph data := by
  intro f g ha
  have hfg := ha.ne
  obtain ⟨e, he, h⟩ := ha
  have hf := (T.incidence e he f).mpr
    (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2))
  have hg := (T.incidence e he g).mpr
    (h.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1))
  exact interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
    (orbitFaceBoundary data.toRotationSystem) Finset.univ
    (orbitFace_totalIncidenceCount_le_two data.toRotationSystem) hfg hf hg

/-- Following the constructed predecessors reaches the root in its actual distance. -/
theorem exists_root_walk (f : OrbitFace data.toRotationSystem) :
    ∃ p : T.faceGraph.Walk f root,
      p.length = (orbitFaceDualGraph data).dist f root := by
  have aux : ∀ n, ∀ f, T.rank f = n → ∃ p : T.faceGraph.Walk f root, p.length = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hrank
      by_cases hf : f = root
      · subst f
        exact ⟨.nil, by simpa [T.rank_eq] using hrank⟩
      · obtain ⟨e, he, hc⟩ := T.covers f hf
        have hd := T.step e he
        rw [hc, hrank] at hd
        obtain ⟨p, hp⟩ := ih (T.rank (T.parent e)) (by omega) (T.parent e) rfl
        have ha : T.faceGraph.Adj f (T.parent e) := hc ▸ T.child_parent_adj e he
        refine ⟨p.cons ha, ?_⟩
        simp only [SimpleGraph.Walk.length_cons, hp]
        omega
  obtain ⟨p, hp⟩ := aux (T.rank f) f rfl
  exact ⟨p, by simpa only [T.rank_eq] using hp⟩

/-- In particular the selected face graph really spans every quotient face. -/
theorem faceGraph_connected : T.faceGraph.Connected := by
  letI : Nonempty (OrbitFace data.toRotationSystem) := ⟨root⟩
  refine ⟨?_⟩
  intro f g
  obtain ⟨p, _⟩ := T.exists_root_walk f
  obtain ⟨q, _⟩ := T.exists_root_walk g
  exact ⟨p.append q.reverse⟩

/-- A selected-edge walk between two faces costs at most their two root distances. -/
theorem faceGraph_dist_le (f g : OrbitFace data.toRotationSystem) :
    T.faceGraph.dist f g ≤ (orbitFaceDualGraph data).dist f root +
      (orbitFaceDualGraph data).dist g root := by
  obtain ⟨p, hp⟩ := T.exists_root_walk f
  obtain ⟨q, hq⟩ := T.exists_root_walk g
  have h := SimpleGraph.dist_le (p.append q.reverse)
  simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hp, hq] using h

/-- Each selected edge changes the root rank by exactly one. -/
theorem rank_le_length_add {f g : OrbitFace data.toRotationSystem}
    (p : T.faceGraph.Walk f g) : T.rank f ≤ p.length + T.rank g := by
  induction p with
  | nil => simp
  | @cons f a g ha p ih =>
    obtain ⟨e, he, h⟩ := ha
    have hd := T.step e he
    rcases h with h | h <;> rw [h.1, h.2] at hd
    all_goals simp only [SimpleGraph.Walk.length_cons]; omega

/-- The selected graph preserves the exact distance to its root. -/
theorem dist_root_eq (f : OrbitFace data.toRotationSystem) :
    T.faceGraph.dist f root = (orbitFaceDualGraph data).dist f root := by
  apply Nat.le_antisymm
  · obtain ⟨p, hp⟩ := T.exists_root_walk f
    exact hp ▸ SimpleGraph.dist_le p
  · obtain ⟨p, hp⟩ := T.faceGraph_connected.exists_walk_length_eq_dist f root
    have h := T.rank_le_length_add p
    simpa only [T.rank_eq, SimpleGraph.dist_self, Nat.add_zero, hp] using h

/-- The distance-realizing root walks may be taken as simple paths. -/
theorem exists_root_path (f : OrbitFace data.toRotationSystem) :
    ∃ p : T.faceGraph.Walk f root, p.IsPath ∧
      p.length = (orbitFaceDualGraph data).dist f root := by
  obtain ⟨p, hp⟩ := T.exists_root_walk f
  exact ⟨p, p.isPath_of_length_eq_dist (hp.trans (T.dist_root_eq f).symm), hp⟩

/-- The face edges are precisely the endpoint pairs of the selected original edges. -/
theorem faceGraph_edgeFinset :
    T.faceGraph.edgeFinset = T.edges.image (fun e => s(T.child e, T.parent e)) := by
  classical
  ext pair
  induction pair using Sym2.ind with
  | h f g =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, faceGraph,
      Finset.mem_image, Sym2.eq_iff]

/-- Connectedness and the constructed count make the selected dual graph a tree. -/
theorem faceGraph_isTree : T.faceGraph.IsTree := by
  classical
  have hle : T.faceGraph.edgeFinset.card ≤ T.edges.card := by
    rw [T.faceGraph_edgeFinset]
    exact Finset.card_image_le
  have hlo : Fintype.card (OrbitFace data.toRotationSystem) ≤
      T.faceGraph.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      T.faceGraph_connected.card_vert_le_card_edgeSet_add_one
  have hs := T.size
  have heq : T.faceGraph.edgeFinset.card + 1 =
      Fintype.card (OrbitFace data.toRotationSystem) := by omega
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨T.faceGraph_connected, ?_⟩
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using heq

end DualBFSTree

/-- The actual dual BFS construction has a primal spanning-tree complement. -/
theorem of_connected_complement_isTree (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root : OrbitFace data.toRotationSystem) :
    (of_connected data (orbitFaceDualGraph_connected data hclass) root).toRankedDualForest.complementGraph.IsTree := by
  let T := of_connected data (orbitFaceDualGraph_connected data hclass) root
  apply T.toRankedDualForest.complement_isTree _ htwo hclass.spherical.euler T.size
  simpa only [rotationPrimalGraph_toRotationSystem_eq] using hclass.primalConnected

end
end Mettapedia.GraphTheory.FourColor.SphericalDualBFSTree
