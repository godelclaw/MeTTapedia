import MettapediaFourColor.StripSixConnection
import Mettapedia.GraphTheory.Kempe.NeighborRelease
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # A degree bound supplies the neighbour-release condition

At an exterior vertex of degree at most four, two distinct neighbours of
colour three, a neighbour of colour one, and an actual zero/two connection
exhaust the possible neighbours. The colour-one neighbour is therefore
unique. A missing colour at that neighbour supplies the existing two-step
release, with complete source reconstruction. Exterior size is unrestricted.
-/

namespace FourColor.StripDegreeRelease

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- An omitted ambient neighbour makes the exterior degree strictly smaller.
The embedding retains every exterior edge; no surjectivity is assumed. -/
theorem exterior_degree_lt {W : Type*} [Fintype W] {H : SimpleGraph W}
    (e : G ↪g H) (v : V) (w : W) (edge : H.Adj (e v) w)
    (outside : ∀ x, e x ≠ w) : G.degree v < H.degree (e v) := by
  classical
  let ns := (G.neighborFinset v).image e
  have count : ns.card = G.degree v := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact G.card_neighborFinset_eq_degree v
  have absent : w ∉ ns := by
    intro hw
    obtain ⟨x,_,eq⟩ := Finset.mem_image.mp hw
    exact outside x eq
  have subset : insert w ns ⊆ H.neighborFinset (e v) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (H.mem_neighborFinset _ _).mpr edge
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact (H.mem_neighborFinset _ _).mpr
        (e.map_adj_iff.mpr ((G.mem_neighborFinset _ _).mp hx))
  have bound := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem absent,count,H.card_neighborFinset_eq_degree] at bound
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem active_neighbour (C : G.Coloring Color) {v t : V}
    (cv : C v = c0) (different : v ≠ t)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (hv : v ∈ C.kempeComponentSet c0 c2 K)
    (ht : t ∈ C.kempeComponentSet c0 c2 K) :
    ∃ z, G.Adj v z ∧ C z = c2 := by
  obtain ⟨av,kv⟩ := hv
  obtain ⟨activeT,kt⟩ := ht
  obtain ⟨p⟩ := ConnectedComponent.exact (kv.trans kt.symm)
  let forget : C.bicoloredSubgraph c0 c2 →g G := ⟨Subtype.val,fun h => h⟩
  have active : ∀ w ∈ (p.map forget).support, C w = c0 ∨ C w = c2 := by
    intro w hw
    rw [Walk.support_map,List.mem_map] at hw
    obtain ⟨x,_,rfl⟩ := hw
    exact x.property
  generalize p.map forget = q at active
  cases q with
  | nil => exact (different rfl).elim
  | @cons v z t edge tail =>
    refine ⟨z,edge,?_⟩
    rcases active z (by simp) with h | h
    · exact (C.valid edge (cv.trans h.symm)).elim
    · exact h

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The degree bound converts retained geometric neighbours and a real
connection into the release condition; no colouring table is assumed. -/
theorem unique_one_neighbour (C : G.Coloring Color) (v u x w t : V)
    (degree : G.degree v ≤ 4)
    (vu : G.Adj v u) (vx : G.Adj v x) (vw : G.Adj v w)
    (uw : G.Adj u w) (wx : w ≠ x)
    (cv : C v = c0) (cu : C u = c1) (cx : C x = c3)
    (missing : ∀ y, G.Adj u y → C y ≠ c2)
    (different : v ≠ t)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (hv : v ∈ C.kempeComponentSet c0 c2 K)
    (ht : t ∈ C.kempeComponentSet c0 c2 K) :
    ∀ y, G.Adj v y → C y = c1 → y = u := by
  classical
  have cw : C w = c3 := by
    have n0 := C.valid vw
    have n1 := C.valid uw
    have n2 := missing w uw
    cases h : C w <;> simp_all
  obtain ⟨z,vz,cz⟩ := active_neighbour C cv different K hv ht
  have ux : u ≠ x := by intro h; have := congrArg C h; simp_all
  have uw' : u ≠ w := by intro h; have := congrArg C h; simp_all
  have uz : u ≠ z := by intro h; have := congrArg C h; simp_all
  have xz : x ≠ z := by intro h; have := congrArg C h; simp_all
  have wz : w ≠ z := by intro h; have := congrArg C h; simp_all
  let neighbours : Finset V := {u,x,w,z}
  have count : neighbours.card = 4 := by
    simp [neighbours,ux,uw',uz,wx.symm,xz,wz]
  have subset : neighbours ⊆ G.neighborFinset v := by
    intro y hy
    simp only [neighbours,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simpa using (by assumption : G.Adj v _)
  have eq : neighbours = G.neighborFinset v :=
    Finset.eq_of_subset_of_card_le subset
      (by simpa only [count,G.card_neighborFinset_eq_degree] using degree)
  intro y adj colour
  have hy : y ∈ neighbours := eq.symm ▸ (G.mem_neighborFinset v y).mpr adj
  simp only [neighbours,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with h | rfl | rfl | rfl
  · exact h
  all_goals simp_all

def repairedBoundary : Boundary := ![c0,c2,c1,c3,c2,c3,c1,c2,c1,c3,c1]
def repairedCore : Fin 8 → Color := ![c3,c2,c1,c0,c0,c0,c2,c3]

theorem core_valid : ValidCore repairedBoundary repairedCore := by
  unfold ValidCore
  decide +kernel

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The local degree and triangular-corner observations supply both actual
switches. The retained component is only used for its connection, not for
an enumerated repair history. -/
theorem repair (C : G.Coloring Color) (ports : Fin 11 → V)
    (injective : Function.Injective ports)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      G.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixConnection.input true i)
    (degree : G.degree (ports 2) ≤ 4)
    (w : V) (one_w : G.Adj (ports 1) w) (two_w : G.Adj (ports 2) w)
    (distinct : w ≠ ports 3)
    (missing : ∀ v, G.Adj (ports 1) v → C v ≠ c2)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (m2 : ports 2 ∈ C.kempeComponentSet c0 c2 K)
    (m4 : ports 4 ∈ C.kempeComponentSet c0 c2 K) :
    ∃ D : G.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  have unique := unique_one_neighbour C (ports 2) (ports 1) (ports 3) w (ports 4)
    degree (embedding 2 1 (by decide +kernel)) (embedding 2 3 (by decide +kernel))
    two_w one_w distinct (initial 2) (initial 1) (initial 3) missing
    (fun h => (by decide : (2 : Fin 11) ≠ 4) (injective h)) K m2 m4
  let S : KempeSeparatedChains.Certificate C c1 c2 := {
    vertices := [ports 1]
    root := ports 1
    root_mem := by simp
    connected := by simp
    active := by
      intro x hx
      have eq := List.mem_singleton.mp hx
      subst x
      exact Or.inl (initial 1)
    closed := by
      intro x hx y adj active
      have eq := List.mem_singleton.mp hx
      subst x
      rcases active with h | h
      · exact (C.valid adj ((initial 1).trans h.symm)).elim
      · exact (missing y adj h).elim }
  have exits : ∀ y, G.Adj (ports 2) y → C y = c1 →
      y ∈ C.kempeComponentSet c1 c2 S.component := by
    intro y adj colour
    rw [unique y adj colour,S.component_mem]
    simp [S]
  have no_entry : ∀ y ∈ C.kempeComponentSet c1 c2 S.component,
      G.Adj (ports 2) y → C y ≠ c2 := by
    intro y hy _
    have eq : y = ports 1 := by simpa [S] using (S.component_mem y).mp hy
    rw [eq,initial]
    decide
  let T := KempeNeighborRelease.second C c1 c2 c0 S.component (ports 2)
    (initial 2) (by decide) (by decide) (by decide) exits no_entry
  have values (i : Fin 11) : T.swap (ports i) = repairedBoundary i := by
    rw [show T.swap (ports i) = if ports i = ports 2 then c1 else S.swap (ports i) from
      KempeNeighborRelease.endpoint C c1 c2 c0 S.component (ports 2)
        (initial 2) (by decide) (by decide) (by decide) exits no_entry (ports i)]
    rw [S.swap_apply]
    have at1 : ports i ∈ S.vertices ↔ i = 1 := by simpa [S] using injective.eq_iff
    simp only [injective.eq_iff,at1,initial]
    fin_cases i <;> decide
  have valid : ValidCore (fun i => T.swap (ports i)) repairedCore := by
    simpa only [values] using core_valid
  let k := colouring (fun i => T.swap (ports i)) repairedCore
    (fun i j edge => T.swap.valid (embedding i j edge)) valid
  exact ⟨T.swap,KempeNeighborRelease.history C c1 c2 c0 S.component (ports 2)
    (initial 2) (by decide) (by decide) (by decide) exits no_entry,rfl,k,
    fun i => colour_port (fun j => T.swap (ports j)) repairedCore i⟩

end FourColor.StripDegreeRelease
