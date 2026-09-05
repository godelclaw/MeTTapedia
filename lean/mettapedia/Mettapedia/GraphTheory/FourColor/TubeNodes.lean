import Mettapedia.GraphTheory.FourColor.TubeCorridorExclusion

/-!
# Literal shore nodes from tube sides (stage one)

The exclusion theorem `le_of_tube_nodes` takes literal shore nodes whose
majority vertex sides are the tube sides.  This file starts the construction
of those nodes from a tube: the edge shore of a vertex side is the set of
edges with both ends in the side, and for a *good* side — every inside vertex
sees at least two inside edges, every outside vertex at most one — the
majority vertex side of that shore is the side itself
(`majorityRetainedKeep_sideShore`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance tubeNodesEdgeSetFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance tubeNodesEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- the edge shore of a vertex side: edges with both ends in the side -/
noncomputable def sideShore (side : V → Prop) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => ∀ v ∈ (e : Sym2 V), side v

theorem mem_sideShore {side : V → Prop} {e : G.edgeSet} :
    e ∈ sideShore (G := G) side ↔ ∀ v ∈ (e : Sym2 V), side v := by
  classical
  simp [sideShore]

/-- a side whose shore has it as majority vertex side -/
structure GoodSide (side : V → Prop) : Prop where
  inside : ∀ v, side v → 2 ≤ (shoreIncidentEdges G (sideShore side) v).card
  outside : ∀ v, ¬ side v → (shoreIncidentEdges G (sideShore side) v).card ≤ 1

/-- **the majority vertex side of a good side's shore is the side** -/
theorem majorityRetainedKeep_sideShore {side : V → Prop} (h : GoodSide (G := G) side) :
    majorityRetainedKeep G (sideShore side) = side := by
  funext v
  apply propext
  rw [majorityRetainedKeep_iff]
  unfold majorityVertexSide
  constructor
  · intro h2
    by_contra hv
    have := h.outside v hv
    omega
  · exact h.inside v

/-! ## Stage two: the good-side property propagates through a slab -/

open ZigzagRing

/-- the edge of a dart, as an element of the edge set -/
def dartEdge (d : G.Dart) : G.edgeSet := ⟨d.edge, d.edge_mem⟩

theorem dartEdge_mem_shoreIncident {side : V → Prop} (d : G.Dart)
    (h1 : side d.fst) (h2 : side d.snd) :
    dartEdge d ∈ shoreIncidentEdges G (sideShore side) d.fst := by
  simp only [shoreIncidentEdges, Finset.mem_filter, incidentEdgeFinset, Finset.mem_univ,
    true_and, mem_sideShore]
  refine ⟨?_, ?_⟩
  · show d.fst ∈ s(d.fst, d.snd)
    exact Sym2.mem_mk_left _ _
  · intro w hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    exacts [h1, h2]

theorem dartEdge_ne {d d' : G.Dart} (h1 : d ≠ d') (h2 : d ≠ d'.symm) :
    dartEdge d ≠ dartEdge d' := by
  intro h
  have := congrArg Subtype.val h
  rcases (SimpleGraph.dart_edge_eq_iff d d').mp this with h | h
  exacts [h1 h, h2 h]

theorem two_le_card_of_two_darts {side : V → Prop} {v : V} (d d' : G.Dart)
    (hd : d.fst = v) (hd' : d'.fst = v) (hne : d ≠ d') (hne' : d ≠ d'.symm)
    (h1 : side d.fst) (h2 : side d.snd) (h1' : side d'.fst) (h2' : side d'.snd) :
    2 ≤ (shoreIncidentEdges G (sideShore side) v).card := by
  subst hd
  have hm := dartEdge_mem_shoreIncident d h1 h2
  have hm' := dartEdge_mem_shoreIncident d' h1' h2'
  rw [hd'] at hm'
  calc 2 = ({dartEdge d, dartEdge d'} : Finset G.edgeSet).card :=
        (Finset.card_pair (dartEdge_ne hne hne')).symm
    _ ≤ _ := Finset.card_le_card (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        exacts [hm, hm'])

theorem shoreIncidentEdges_mono {side side' : V → Prop} (h : ∀ v, side v → side' v) (v : V) :
    shoreIncidentEdges G (sideShore side) v ⊆ shoreIncidentEdges G (sideShore side') v := by
  intro e he
  simp only [shoreIncidentEdges, Finset.mem_filter, mem_sideShore] at he ⊢
  exact ⟨he.1, fun w hw => h w (he.2 w hw)⟩

variable (rotation : SimpleGraphDartRotation.Data G) {k : Nat} [NeZero k]

/-- **a slab keeps the side good** -/
theorem GoodSide.slab {inner : V → Prop} (h : GoodSide (G := G) inner)
    (S : ZigzagSlab rotation.toRotationSystem k inner) : GoodSide (G := G) S.inner' where
  outside := by
    intro v hv
    have : shoreIncidentEdges G (sideShore S.inner') v = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he hmem
      rw [mem_sideShore] at hmem
      simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact hv (hmem v he)
    rw [this]; simp
  inside := by
    intro v hv
    rcases hv with hv | ⟨u, rfl⟩
    · exact le_trans (h.inside v hv)
        (Finset.card_le_card (shoreIncidentEdges_mono (fun _ => S.inner'_of_inner) v))
    · rcases u with i | i
      · apply two_le_card_of_two_darts (S.ι (Sum.inl (Sum.inl (i, false))))
          (S.ι (Sum.inl (Sum.inr (i - 1, true))))
        · exact S.vert_ι _
        · show rotation.toRotationSystem.vertOf _ = _
          rw [S.vert_ι]
          show S.vtx (Sum.inl (i - 1 + 1)) = S.vtx (Sum.inl i)
          rw [sub_add_cancel]
        · intro h; exact absurd (S.ι_inj h) (by simp)
        · intro h
          have : S.ι (Sum.inl (Sum.inl (i, false))) = S.ι (Sum.inl (flip k (Sum.inr (i - 1, true)))) := by
            rw [← S.alpha_interior]; exact h
          exact absurd (S.ι_inj this) (by simp [ZigzagRing.flip])
        · exact S.slab_inner' _
        · show S.inner' (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _))
          rw [S.alpha_interior]; exact S.slab_inner' _
        · exact S.slab_inner' _
        · show S.inner' (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _))
          rw [S.alpha_interior]; exact S.slab_inner' _
      · apply two_le_card_of_two_darts (S.ι (Sum.inl (Sum.inl (i, true))))
          (S.ι (Sum.inl (Sum.inr (i, false))))
        · exact S.vert_ι _
        · exact S.vert_ι _
        · intro h; exact absurd (S.ι_inj h) (by simp)
        · intro h
          have : S.ι (Sum.inl (Sum.inl (i, true))) = S.ι (Sum.inl (flip k (Sum.inr (i, false)))) := by
            rw [← S.alpha_interior]; exact h
          exact absurd (S.ι_inj this) (by simp [ZigzagRing.flip])
        · exact S.slab_inner' _
        · show S.inner' (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _))
          rw [S.alpha_interior]; exact S.slab_inner' _
        · exact S.slab_inner' _
        · show S.inner' (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _))
          rw [S.alpha_interior]; exact S.slab_inner' _

/-! ## Stage three: shore connectivity propagates through a slab -/

open SimpleGraph

/-- a walk all of whose edges lie in the shore -/
def ShoreWalk (shore : Finset G.edgeSet) (u v : V) : Prop :=
  ∃ w : G.Walk u v, ∀ e : G.edgeSet, (e : Sym2 V) ∈ w.edges → e ∈ shore

namespace ShoreWalk

variable {shore : Finset G.edgeSet} {u v x : V}

theorem refl : ShoreWalk (G := G) shore u u := ⟨Walk.nil, by simp⟩

theorem symm (h : ShoreWalk (G := G) shore u v) : ShoreWalk (G := G) shore v u := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, fun e he => hw e (by simpa [Walk.edges_reverse] using he)⟩

theorem trans (h1 : ShoreWalk (G := G) shore u v) (h2 : ShoreWalk (G := G) shore v x) :
    ShoreWalk (G := G) shore u x := by
  obtain ⟨w1, hw1⟩ := h1
  obtain ⟨w2, hw2⟩ := h2
  refine ⟨w1.append w2, fun e he => ?_⟩
  rw [Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  exacts [hw1 e he, hw2 e he]

theorem step (d : G.Dart) (hd : dartEdge d ∈ shore) :
    ShoreWalk (G := G) shore d.fst d.snd := by
  refine ⟨Walk.cons d.adj Walk.nil, fun e he => ?_⟩
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he
  have : e = dartEdge d := Subtype.ext he
  rw [this]; exact hd

theorem mono {shore' : Finset G.edgeSet} (h : shore ⊆ shore') (hw : ShoreWalk (G := G) shore u v) :
    ShoreWalk (G := G) shore' u v := by
  obtain ⟨w, hw⟩ := hw
  exact ⟨w, fun e he => h (hw e he)⟩

end ShoreWalk

theorem edgeShoreConnected_iff (shore : Finset G.edgeSet) :
    EdgeShoreConnected G shore ↔
      ∀ ⦃u v : V⦄, (∃ e ∈ shore, u ∈ (e : Sym2 V)) → (∃ e ∈ shore, v ∈ (e : Sym2 V)) →
        ShoreWalk (G := G) shore u v := Iff.rfl

theorem sideShore_mono {side side' : V → Prop} (h : ∀ v, side v → side' v) :
    sideShore (G := G) side ⊆ sideShore side' := by
  intro e he
  rw [mem_sideShore] at he ⊢
  exact fun w hw => h w (he w hw)

/-- a vertex with two shore edges touches the shore -/
theorem touches_of_goodSide {side : V → Prop} (h : GoodSide (G := G) side) {v : V} (hv : side v) :
    ∃ e ∈ sideShore (G := G) side, v ∈ (e : Sym2 V) := by
  have h2 := h.inside v hv
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (shoreIncidentEdges G (sideShore side) v).card)
  simp only [shoreIncidentEdges, Finset.mem_filter, incidentEdgeFinset, Finset.mem_univ,
    true_and] at he
  exact ⟨e, he.2, he.1⟩

namespace ZigzagSlab

section Slab

variable {rotation} {k : Nat} [NeZero k] {inner : V → Prop}
variable (S : ZigzagSlab rotation.toRotationSystem k inner)

theorem ofNat'_succ (m : Nat) : Fin.ofNat k (m + 1) = Fin.ofNat k m + 1 := by
  ext
  simp [Fin.val_add, Fin.val_ofNat, Fin.val_one', Nat.add_mod]

theorem ofNat'_val (i : Fin k) : Fin.ofNat k (i : Nat) = i := Fin.ofNat_val_eq_self i

/-- ring edges lie in the enlarged shore -/
theorem slabEdge_mem (x : ZigzagRing.Dart k) :
    dartEdge (S.ι (Sum.inl x)) ∈ sideShore (G := G) S.inner' := by
  rw [mem_sideShore]
  intro w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact S.slab_inner' _
  · show S.inner' (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _))
    rw [S.alpha_interior]; exact S.slab_inner' _

/-- in-edges lie in the enlarged shore -/
theorem inEdge_mem (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inl i))) ∈ sideShore (G := G) S.inner' := by
  rw [mem_sideShore]
  intro w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact S.slab_inner' _
  · exact Or.inl (S.in_inner i)

/-- the base vertex `d 0` -/
def base : V := S.vtx (Sum.inl 0)

/-- around the ring: `d 0` reaches `d m`, in any shore containing the ring edges -/
theorem walk_to_d {shore : Finset G.edgeSet}
    (hs : ∀ x : ZigzagRing.Dart k, dartEdge (S.ι (Sum.inl x)) ∈ shore) : ∀ m : Nat,
    ShoreWalk (G := G) shore S.base (S.vtx (Sum.inl (Fin.ofNat k m)))
  | 0 => by simpa [base] using (ShoreWalk.refl (G := G) (shore := shore) (u := S.base))
  | m + 1 => by
    have ih := walk_to_d hs m
    have h1 : ShoreWalk (G := G) shore (S.vtx (Sum.inl (Fin.ofNat k m)))
        (S.vtx (Sum.inr (Fin.ofNat k m))) := by
      have := ShoreWalk.step _ (hs (Sum.inl (Fin.ofNat k m, false)))
      rwa [show (S.ι (Sum.inl (Sum.inl (Fin.ofNat k m, false)))).fst = S.vtx (Sum.inl (Fin.ofNat k m)) from
        S.vert_ι _, show (S.ι (Sum.inl (Sum.inl (Fin.ofNat k m, false)))).snd =
          S.vtx (Sum.inr (Fin.ofNat k m)) from by
            show rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _) = _
            rw [S.alpha_interior, S.vert_ι]; rfl] at this
    have h2 : ShoreWalk (G := G) shore (S.vtx (Sum.inr (Fin.ofNat k m)))
        (S.vtx (Sum.inl (Fin.ofNat k (m + 1)))) := by
      have := ShoreWalk.step _ (hs (Sum.inr (Fin.ofNat k m, false)))
      rwa [show (S.ι (Sum.inl (Sum.inr (Fin.ofNat k m, false)))).fst = S.vtx (Sum.inr (Fin.ofNat k m)) from
        S.vert_ι _, show (S.ι (Sum.inl (Sum.inr (Fin.ofNat k m, false)))).snd =
          S.vtx (Sum.inl (Fin.ofNat k (m + 1))) from by
            show rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _) = _
            rw [S.alpha_interior, S.vert_ι]
            show S.vtx (Sum.inl (Fin.ofNat k m + 1)) = _
            rw [ofNat'_succ]] at this
    exact ih.trans (h1.trans h2)

/-- `d 0` reaches every slab vertex, in any shore containing the ring edges -/
theorem walk_to_slab {shore : Finset G.edgeSet}
    (hs : ∀ x : ZigzagRing.Dart k, dartEdge (S.ι (Sum.inl x)) ∈ shore) (u : ZigzagRing.Vtx k) :
    ShoreWalk (G := G) shore S.base (S.vtx u) := by
  rcases u with i | i
  · simpa [ofNat'_val] using S.walk_to_d hs (i : Nat)
  · have hd := S.walk_to_d hs (i : Nat)
    rw [ofNat'_val] at hd
    have := ShoreWalk.step _ (hs (Sum.inl (i, false)))
    rw [show (S.ι (Sum.inl (Sum.inl (i, false)))).fst = S.vtx (Sum.inl i) from S.vert_ι _,
      show (S.ι (Sum.inl (Sum.inl (i, false)))).snd = S.vtx (Sum.inr i) from by
        show rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _) = _
        rw [S.alpha_interior, S.vert_ι]; rfl] at this
    exact hd.trans this

/-- the in-partner vertex of in-port `i` -/
def inVertex (i : Fin k) : V := (S.ι (Sum.inr (Sum.inl i))).snd

theorem inVertex_inner (i : Fin k) : inner (S.inVertex i) := S.in_inner i

/-- `d 0` reaches every in-partner vertex, in any shore containing the ring and in-edges -/
theorem walk_to_inVertex {shore : Finset G.edgeSet}
    (hs : ∀ x : ZigzagRing.Dart k, dartEdge (S.ι (Sum.inl x)) ∈ shore)
    (hin : ∀ i, dartEdge (S.ι (Sum.inr (Sum.inl i))) ∈ shore) (i : Fin k) :
    ShoreWalk (G := G) shore S.base (S.inVertex i) := by
  have := ShoreWalk.step _ (hin i)
  rw [show (S.ι (Sum.inr (Sum.inl i))).fst = S.vtx (Sum.inl i) from S.vert_ι _] at this
  exact (S.walk_to_slab hs (Sum.inl i)).trans this

/-- **a slab keeps the shore connected** -/
theorem edgeShoreConnected_slab (hgood : GoodSide (G := G) inner)
    (hconn : EdgeShoreConnected G (sideShore inner)) :
    EdgeShoreConnected G (sideShore S.inner') := by
  rw [edgeShoreConnected_iff]
  -- every vertex touching the enlarged shore reaches the base
  have key : ∀ u : V, (∃ e ∈ sideShore (G := G) S.inner', u ∈ (e : Sym2 V)) →
      ShoreWalk (G := G) (sideShore S.inner') S.base u := by
    intro u ⟨e, he, hu⟩
    rw [mem_sideShore] at he
    rcases he u hu with hin | ⟨w, rfl⟩
    · -- an inner vertex: through the inner shore to the base in-partner, unless `u` is one
      have hp0 := touches_of_goodSide hgood (S.inVertex_inner 0)
      by_cases htouch : ∃ e ∈ sideShore (G := G) inner, u ∈ (e : Sym2 V)
      · have hw := hconn htouch hp0
        exact (S.walk_to_inVertex S.slabEdge_mem S.inEdge_mem 0).trans
          ((ShoreWalk.mono (sideShore_mono (fun _ => S.inner'_of_inner)) hw).symm)
      · -- the shore edge at `u` leads to a slab vertex; the dart back is an in-port
        let w := Sym2.Mem.other hu
        have hz : s(u, w) = (e : Sym2 V) := Sym2.other_spec hu
        have hw' : S.inner' w := he w (by rw [← hz]; exact Sym2.mem_mk_right _ _)
        rcases hw' with hwin | ⟨v', hv'⟩
        · exfalso
          apply htouch
          refine ⟨e, ?_, hu⟩
          rw [mem_sideShore]
          intro x hx
          rw [← hz] at hx
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          exacts [hin, hwin]
        · have hadj : G.Adj w u := by
            have := e.2
            rw [← hz, SimpleGraph.mem_edgeSet] at this
            exact this.symm
          let d : G.Dart := ⟨(w, u), hadj⟩
          obtain ⟨y, hy⟩ := S.cubic_slab d ⟨v', hv'⟩
          have hsnd : (S.ι y).snd = u := by rw [hy]
          rcases y with y | i | i
          · exfalso
            apply S.slab_not_inner (Sum.inl (ZigzagRing.flip k y))
            show inner (rotation.toRotationSystem.vertOf (S.ι (Sum.inl (ZigzagRing.flip k y))))
            rw [← S.alpha_interior]
            show inner (S.ι (Sum.inl y)).snd
            rw [hsnd]; exact hin
          · have : S.inVertex i = u := hsnd
            rw [← this]
            exact S.walk_to_inVertex S.slabEdge_mem S.inEdge_mem i
          · exfalso
            apply S.out_not_inner i
            show inner (S.ι (Sum.inr (Sum.inr i))).snd
            rw [hsnd]; exact hin
    · exact S.walk_to_slab S.slabEdge_mem w
  intro u v hu hv
  exact (key u hu).symm.trans (key v hv)

/-! ## Stage four: complement connectivity propagates inward through a slab -/

/-- the complement shore: edges with an end outside the side -/
noncomputable def compShore (side : V → Prop) : Finset G.edgeSet :=
  Finset.univ \ sideShore side

theorem mem_compShore {side : V → Prop} {e : G.edgeSet} :
    e ∈ compShore (G := G) side ↔ ∃ v ∈ (e : Sym2 V), ¬ side v := by
  classical
  simp [compShore, mem_sideShore]

theorem compShore_mono {side side' : V → Prop} (h : ∀ v, side v → side' v) :
    compShore (G := G) side' ⊆ compShore side := by
  intro e he
  rw [mem_compShore] at he ⊢
  obtain ⟨v, hv, hn⟩ := he
  exact ⟨v, hv, fun h' => hn (h v h')⟩

theorem slabEdge_mem_comp (x : ZigzagRing.Dart k) :
    dartEdge (S.ι (Sum.inl x)) ∈ compShore (G := G) inner := by
  rw [mem_compShore]
  exact ⟨(S.ι (Sum.inl x)).fst, Sym2.mem_mk_left _ _, S.slab_not_inner _⟩

theorem inEdge_mem_comp (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inl i))) ∈ compShore (G := G) inner := by
  rw [mem_compShore]
  exact ⟨(S.ι (Sum.inr (Sum.inl i))).fst, Sym2.mem_mk_left _ _, S.slab_not_inner _⟩

theorem outEdge_mem_comp (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inr i))) ∈ compShore (G := G) inner := by
  rw [mem_compShore]
  exact ⟨(S.ι (Sum.inr (Sum.inr i))).fst, Sym2.mem_mk_left _ _, S.slab_not_inner _⟩

theorem outEdge_mem_comp' (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inr i))) ∈ compShore (G := G) S.inner' := by
  rw [mem_compShore]
  exact ⟨(S.ι (Sum.inr (Sum.inr i))).snd, Sym2.mem_mk_right _ _, (S.outPort i).2⟩

/-- the out-port partner vertex -/
def outVertex (i : Fin k) : V := (S.ι (Sum.inr (Sum.inr i))).snd

theorem outVertex_touches (i : Fin k) :
    ∃ e ∈ compShore (G := G) S.inner', S.outVertex i ∈ (e : Sym2 V) :=
  ⟨_, S.outEdge_mem_comp' i, Sym2.mem_mk_right _ _⟩

/-- the base out-partner reaches every slab vertex in the complement of `inner` -/
theorem cwalk_to_slab (u : ZigzagRing.Vtx k) :
    ShoreWalk (G := G) (compShore inner) (S.outVertex 0) (S.vtx u) := by
  have h1 := ShoreWalk.step _ (S.outEdge_mem_comp 0)
  rw [show (S.ι (Sum.inr (Sum.inr 0))).fst = S.vtx (Sum.inr 0) from S.vert_ι _] at h1
  exact h1.symm.trans ((S.walk_to_slab S.slabEdge_mem_comp (Sum.inr 0)).symm.trans
    (S.walk_to_slab S.slabEdge_mem_comp u))

/-- **a slab keeps the complement connected, inward** -/
theorem edgeShoreConnected_comp_slab
    (hconn : EdgeShoreConnected G (compShore S.inner')) :
    EdgeShoreConnected G (compShore inner) := by
  rw [edgeShoreConnected_iff]
  have key : ∀ u : V, (∃ e ∈ compShore (G := G) inner, u ∈ (e : Sym2 V)) →
      ShoreWalk (G := G) (compShore inner) (S.outVertex 0) u := by
    intro u ⟨e, he, hu⟩
    by_cases htouch : ∃ e ∈ compShore (G := G) S.inner', u ∈ (e : Sym2 V)
    · exact ShoreWalk.mono (compShore_mono (fun _ => S.inner'_of_inner))
        (hconn (S.outVertex_touches 0) htouch)
    · -- `u` is in the enlarged side, and `e` has an end in the slab
      have hu' : S.inner' u := by
        by_contra hn
        exact htouch ⟨e, by rw [mem_compShore]; exact ⟨u, hu, hn⟩, hu⟩
      rcases hu' with hin | ⟨w, rfl⟩
      · -- an inner vertex with a complement edge: its other end lies in the slab
        let x := Sym2.Mem.other hu
        have hz : s(u, x) = (e : Sym2 V) := Sym2.other_spec hu
        have hx : ¬ inner x := by
          rw [mem_compShore] at he
          obtain ⟨y, hy, hny⟩ := he
          rw [← hz] at hy
          rcases Sym2.mem_iff.mp hy with rfl | rfl
          · exact absurd hin hny
          · exact hny
        have hx' : S.inner' x := by
          by_contra hn
          exact htouch ⟨e, by rw [mem_compShore]; exact ⟨x, by rw [← hz]; exact Sym2.mem_mk_right _ _, hn⟩, hu⟩
        rcases hx' with hxin | ⟨v', hv'⟩
        · exact absurd hxin hx
        · have hadj : G.Adj x u := by
            have := e.2
            rw [← hz, SimpleGraph.mem_edgeSet] at this
            exact this.symm
          let d : G.Dart := ⟨(x, u), hadj⟩
          obtain ⟨y, hy⟩ := S.cubic_slab d ⟨v', hv'⟩
          have hsnd : (S.ι y).snd = u := by rw [hy]
          rcases y with y | i | i
          · exfalso
            apply S.slab_not_inner (Sum.inl (ZigzagRing.flip k y))
            show inner (rotation.toRotationSystem.vertOf (S.ι (Sum.inl (ZigzagRing.flip k y))))
            rw [← S.alpha_interior]
            show inner (S.ι (Sum.inl y)).snd
            rw [hsnd]; exact hin
          · have : S.inVertex i = u := hsnd
            rw [← this]
            exact (S.cwalk_to_slab (Sum.inl 0)).trans
              ((S.walk_to_inVertex S.slabEdge_mem_comp S.inEdge_mem_comp i))
          · exfalso
            apply S.out_not_inner i
            show inner (S.ι (Sum.inr (Sum.inr i))).snd
            rw [hsnd]; exact hin
      · exact S.cwalk_to_slab w
  intro u v hu hv
  exact (key u hu).symm.trans (key v hv)

end Slab

end ZigzagSlab

end TubeSlab
end Mettapedia.GraphTheory.FourColor
