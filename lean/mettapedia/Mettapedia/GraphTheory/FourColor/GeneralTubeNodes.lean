import Mettapedia.GraphTheory.FourColor.GeneralTubeExclusion
import Mettapedia.GraphTheory.FourColor.TubeNodes

/-!
# Literal shore nodes along a periodic corridor of any slab shape

`TubeNodes` built the nodes for zigzag tubes.  Here the same construction is
carried out for chains of copies of an abstract slab shape `T`, under two
finite hypotheses on the shape (`SlabShape`): every vertex carries two darts
that are not out-ports and have distinct edges, and the interior edges
connect all vertices.  The result `TubeOf.le_of_tubeOf` is the exclusion
theorem from base hypotheses only.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition
open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance gtnEdgeSetFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance gtnEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable {rotation : SimpleGraphDartRotation.Data G} {k : Nat} [NeZero k]
variable {Vt It : Type u} {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)}

/-- a dart of the shape that is not an out-port -/
def NotOut (x : SlabDart T) : Prop := ∀ i, x ≠ Sum.inr (Sum.inr i)

/-- two darts of the shape with distinct edges -/
def DistinctEdge (x x' : SlabDart T) : Prop :=
  x ≠ x' ∧ ∀ y y', x = Sum.inl y → x' = Sum.inl y' → y ≠ T.interiorAlpha y'

/-- interior adjacency of the shape -/
def InteriorAdj (T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)) (u v : Vt) : Prop :=
  ∃ y : It, T.interiorVert y = u ∧ T.interiorVert (T.interiorAlpha y) = v

/-- the two finite hypotheses on a slab shape -/
structure SlabShape (T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)) : Prop where
  two_darts : ∀ v : Vt, ∃ x x' : SlabDart T, T.vertOf x = v ∧ T.vertOf x' = v ∧
    NotOut x ∧ NotOut x' ∧ DistinctEdge x x'
  connected : ∀ u v : Vt, Relation.ReflTransGen (InteriorAdj T) u v

namespace SlabOf

variable {inner : V → Prop} (S : SlabOf rotation.toRotationSystem T inner)

theorem fst_ι (x : SlabDart T) : (S.ι x).fst = S.vtx (T.vertOf x) := S.vert_ι x

theorem snd_ι_interior (y : It) :
    (S.ι (Sum.inl y)).snd = S.vtx (T.vertOf (Sum.inl (T.interiorAlpha y))) := by
  show rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _) = _
  rw [S.alpha_interior, S.vert_ι]

/-- the other end of a non-out-port dart lies in the enlarged side -/
theorem snd_inner'_of_notOut (x : SlabDart T) (hx : NotOut x) : S.inner' (S.ι x).snd := by
  rcases x with y | i | i
  · show S.inner' (rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha _))
    rw [S.alpha_interior]; exact S.slab_inner' _
  · exact Or.inl (S.in_inner i)
  · exact absurd rfl (hx i)

/-- distinct edges of the shape have distinct images -/
theorem dartEdge_ne_of_distinct {x x' : SlabDart T} (h : DistinctEdge x x') :
    dartEdge (S.ι x) ≠ dartEdge (S.ι x') := by
  apply dartEdge_ne
  · intro heq; exact h.1 (S.ι_inj heq)
  · intro heq
    rcases x' with y' | i' | i'
    · have : S.ι x = S.ι (Sum.inl (T.interiorAlpha y')) := by
        rw [← S.alpha_interior]; exact heq
      have hx := S.ι_inj this
      subst hx
      exact h.2 _ _ rfl rfl rfl
    · -- `x` would be the in-partner dart, whose vertex is in `inner`, not in the slab
      have hv : rotation.toRotationSystem.vertOf (S.ι x) =
          rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha (S.ι (Sum.inr (Sum.inl i')))) := by
        rw [heq]; rfl
      exact S.slab_not_inner x (by rw [hv]; exact S.in_inner i')
    · have hv : rotation.toRotationSystem.vertOf (S.ι x) =
          rotation.toRotationSystem.vertOf (rotation.toRotationSystem.alpha (S.ι (Sum.inr (Sum.inr i')))) := by
        rw [heq]; rfl
      exact S.out_not_slab i' (T.vertOf x) (by rw [← hv]; exact S.vert_ι x)

/-- **a slab keeps the side good** -/
theorem goodSide_slab (hT : SlabShape T) (h : GoodSide (G := G) inner) :
    GoodSide (G := G) S.inner' where
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
    · obtain ⟨x, x', hx, hx', hnx, hnx', hd⟩ := hT.two_darts u
      have hm := dartEdge_mem_shoreIncident (S.ι x) (S.slab_inner' x) (S.snd_inner'_of_notOut x hnx)
      have hm' := dartEdge_mem_shoreIncident (S.ι x') (S.slab_inner' x')
        (S.snd_inner'_of_notOut x' hnx')
      rw [S.fst_ι, hx] at hm
      rw [S.fst_ι, hx'] at hm'
      calc 2 = ({dartEdge (S.ι x), dartEdge (S.ι x')} : Finset G.edgeSet).card :=
            (Finset.card_pair (S.dartEdge_ne_of_distinct hd)).symm
        _ ≤ _ := Finset.card_le_card (by
            intro e he
            simp only [Finset.mem_insert, Finset.mem_singleton] at he
            rcases he with rfl | rfl
            exacts [hm, hm'])

/-- interior edges lie in every shore containing them; in particular in the enlarged shore -/
theorem slabEdge_mem (y : It) : dartEdge (S.ι (Sum.inl y)) ∈ sideShore (G := G) S.inner' := by
  rw [mem_sideShore]
  intro w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact S.slab_inner' _
  · exact S.snd_inner'_of_notOut _ (fun _ h => by cases h)

theorem inEdge_mem (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inl i))) ∈ sideShore (G := G) S.inner' := by
  rw [mem_sideShore]
  intro w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact S.slab_inner' _
  · exact Or.inl (S.in_inner i)

/-- interior reachability gives shore walks between slab vertices -/
theorem walk_of_reach {shore : Finset G.edgeSet}
    (hs : ∀ y : It, dartEdge (S.ι (Sum.inl y)) ∈ shore) {u v : Vt}
    (h : Relation.ReflTransGen (InteriorAdj T) u v) :
    ShoreWalk (G := G) shore (S.vtx u) (S.vtx v) := by
  induction h with
  | refl => exact ShoreWalk.refl
  | tail _ hadj ih =>
    obtain ⟨y, rfl, rfl⟩ := hadj
    refine ih.trans ?_
    have := ShoreWalk.step _ (hs y)
    rw [S.fst_ι, S.snd_ι_interior] at this
    exact this

def inVertex (i : Fin k) : V := (S.ι (Sum.inr (Sum.inl i))).snd

theorem inVertex_inner (i : Fin k) : inner (S.inVertex i) := S.in_inner i

def outVertex (i : Fin k) : V := (S.ι (Sum.inr (Sum.inr i))).snd

/-- **a slab keeps the shore connected** -/
theorem edgeShoreConnected_slab (hT : SlabShape T) (hgood : GoodSide (G := G) inner)
    (hconn : EdgeShoreConnected G (sideShore inner)) :
    EdgeShoreConnected G (sideShore S.inner') := by
  rw [edgeShoreConnected_iff]
  let base := S.vtx (T.vertOf (Sum.inr (Sum.inl 0)))
  have hslab : ∀ u : Vt, ShoreWalk (G := G) (sideShore S.inner') base (S.vtx u) :=
    fun u => S.walk_of_reach S.slabEdge_mem (hT.connected _ u)
  have hinV : ∀ i, ShoreWalk (G := G) (sideShore S.inner') base (S.inVertex i) := fun i => by
    have := ShoreWalk.step _ (S.inEdge_mem i)
    rw [S.fst_ι] at this
    exact (hslab _).trans this
  have key : ∀ u : V, (∃ e ∈ sideShore (G := G) S.inner', u ∈ (e : Sym2 V)) →
      ShoreWalk (G := G) (sideShore S.inner') base u := by
    intro u ⟨e, he, hu⟩
    rw [mem_sideShore] at he
    rcases he u hu with hin | ⟨w, rfl⟩
    · have hp0 := touches_of_goodSide hgood (S.inVertex_inner 0)
      by_cases htouch : ∃ e ∈ sideShore (G := G) inner, u ∈ (e : Sym2 V)
      · have hw := hconn htouch hp0
        exact (hinV 0).trans
          ((ShoreWalk.mono (sideShore_mono (fun _ => S.inner'_of_inner)) hw).symm)
      · let w := Sym2.Mem.other hu
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
            apply S.slab_not_inner (Sum.inl (T.interiorAlpha y))
            show inner (rotation.toRotationSystem.vertOf (S.ι (Sum.inl (T.interiorAlpha y))))
            rw [← S.alpha_interior]
            show inner (S.ι (Sum.inl y)).snd
            rw [hsnd]; exact hin
          · have : S.inVertex i = u := hsnd
            rw [← this]
            exact hinV i
          · exfalso
            apply S.out_not_inner i
            show inner (S.ι (Sum.inr (Sum.inr i))).snd
            rw [hsnd]; exact hin
    · exact hslab w
  intro u v hu hv
  exact (key u hu).symm.trans (key v hv)

theorem slabEdge_mem_comp (y : It) :
    dartEdge (S.ι (Sum.inl y)) ∈ ZigzagSlab.compShore (G := G) inner := by
  rw [ZigzagSlab.mem_compShore]
  exact ⟨(S.ι (Sum.inl y)).fst, Sym2.mem_mk_left _ _, S.slab_not_inner _⟩

theorem inEdge_mem_comp (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inl i))) ∈ ZigzagSlab.compShore (G := G) inner := by
  rw [ZigzagSlab.mem_compShore]
  exact ⟨(S.ι (Sum.inr (Sum.inl i))).fst, Sym2.mem_mk_left _ _, S.slab_not_inner _⟩

theorem outEdge_mem_comp (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inr i))) ∈ ZigzagSlab.compShore (G := G) inner := by
  rw [ZigzagSlab.mem_compShore]
  exact ⟨(S.ι (Sum.inr (Sum.inr i))).fst, Sym2.mem_mk_left _ _, S.slab_not_inner _⟩

theorem outEdge_mem_comp' (i : Fin k) :
    dartEdge (S.ι (Sum.inr (Sum.inr i))) ∈ ZigzagSlab.compShore (G := G) S.inner' := by
  rw [ZigzagSlab.mem_compShore]
  exact ⟨(S.ι (Sum.inr (Sum.inr i))).snd, Sym2.mem_mk_right _ _, (S.outPort i).2⟩

theorem outVertex_touches (i : Fin k) :
    ∃ e ∈ ZigzagSlab.compShore (G := G) S.inner', S.outVertex i ∈ (e : Sym2 V) :=
  ⟨_, S.outEdge_mem_comp' i, Sym2.mem_mk_right _ _⟩

/-- **a slab keeps the complement connected, inward** -/
theorem edgeShoreConnected_comp_slab (hT : SlabShape T)
    (hconn : EdgeShoreConnected G (ZigzagSlab.compShore S.inner')) :
    EdgeShoreConnected G (ZigzagSlab.compShore inner) := by
  rw [edgeShoreConnected_iff]
  -- from the base out-partner to every slab vertex, in the complement of `inner`
  have cwalk : ∀ u : Vt, ShoreWalk (G := G) (ZigzagSlab.compShore inner) (S.outVertex 0) (S.vtx u) := by
    intro u
    have h1 := ShoreWalk.step _ (S.outEdge_mem_comp 0)
    rw [S.fst_ι] at h1
    exact h1.symm.trans (S.walk_of_reach S.slabEdge_mem_comp (hT.connected _ u))
  have key : ∀ u : V, (∃ e ∈ ZigzagSlab.compShore (G := G) inner, u ∈ (e : Sym2 V)) →
      ShoreWalk (G := G) (ZigzagSlab.compShore inner) (S.outVertex 0) u := by
    intro u ⟨e, he, hu⟩
    by_cases htouch : ∃ e ∈ ZigzagSlab.compShore (G := G) S.inner', u ∈ (e : Sym2 V)
    · exact ShoreWalk.mono (ZigzagSlab.compShore_mono (fun _ => S.inner'_of_inner))
        (hconn (S.outVertex_touches 0) htouch)
    · have hu' : S.inner' u := by
        by_contra hn
        exact htouch ⟨e, by rw [ZigzagSlab.mem_compShore]; exact ⟨u, hu, hn⟩, hu⟩
      rcases hu' with hin | ⟨w, rfl⟩
      · let x := Sym2.Mem.other hu
        have hz : s(u, x) = (e : Sym2 V) := Sym2.other_spec hu
        have hx : ¬ inner x := by
          rw [ZigzagSlab.mem_compShore] at he
          obtain ⟨y, hy, hny⟩ := he
          rw [← hz] at hy
          rcases Sym2.mem_iff.mp hy with rfl | rfl
          · exact absurd hin hny
          · exact hny
        have hx' : S.inner' x := by
          by_contra hn
          exact htouch ⟨e, by
            rw [ZigzagSlab.mem_compShore]
            exact ⟨x, by rw [← hz]; exact Sym2.mem_mk_right _ _, hn⟩, hu⟩
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
            apply S.slab_not_inner (Sum.inl (T.interiorAlpha y))
            show inner (rotation.toRotationSystem.vertOf (S.ι (Sum.inl (T.interiorAlpha y))))
            rw [← S.alpha_interior]
            show inner (S.ι (Sum.inl y)).snd
            rw [hsnd]; exact hin
          · have : S.inVertex i = u := hsnd
            rw [← this]
            have hstep := ShoreWalk.step _ (S.inEdge_mem_comp i)
            rw [S.fst_ι] at hstep
            exact (cwalk _).trans hstep
          · exfalso
            apply S.out_not_inner i
            show inner (S.ι (Sum.inr (Sum.inr i))).snd
            rw [hsnd]; exact hin
      · exact cwalk w
  intro u v hu hv
  exact (key u hu).symm.trans (key v hv)

theorem sideShore_ssubset_inner' (hT : SlabShape T) [Nonempty Vt] :
    sideShore (G := G) inner ⊂ sideShore S.inner' := by
  rw [Finset.ssubset_iff_of_subset (sideShore_mono (fun _ => S.inner'_of_inner))]
  obtain ⟨x, x', hx, hx', hnx, hnx', hd⟩ := hT.two_darts (Classical.arbitrary Vt)
  refine ⟨dartEdge (S.ι x), ?_, ?_⟩
  · rw [mem_sideShore]
    intro w hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact S.slab_inner' _
    · exact S.snd_inner'_of_notOut x hnx
  · intro h
    rw [mem_sideShore] at h
    exact S.slab_not_inner _ (h _ (Sym2.mem_mk_left _ _))

end SlabOf

/-! ## Along the chain, and the tube theorem -/

section TubeTheorem

open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24MajorityShoreStateDescent

namespace TubeOf

variable (hT : SlabShape T)
include hT

theorem goodSide_side : {inner : V → Prop} → {n : Nat} →
    (t : TubeOf rotation.toRotationSystem T inner n) → GoodSide (G := G) inner →
    ∀ r, r ≤ n → GoodSide (G := G) (t.side r)
  | _, _, nil _ _, h, _, _ => h
  | _, _, cons _ _, h, 0, _ => h
  | _, _, cons S rest, h, r + 1, hr => goodSide_side rest (S.goodSide_slab hT h) r (by omega)

theorem conn_side : {inner : V → Prop} → {n : Nat} →
    (t : TubeOf rotation.toRotationSystem T inner n) → GoodSide (G := G) inner →
    EdgeShoreConnected G (sideShore inner) →
    ∀ r, r ≤ n → EdgeShoreConnected G (sideShore (t.side r))
  | _, _, nil _ _, _, hc, _, _ => hc
  | _, _, cons _ _, _, hc, 0, _ => hc
  | _, _, cons S rest, hg, hc, r + 1, hr =>
    conn_side rest (S.goodSide_slab hT hg) (S.edgeShoreConnected_slab hT hg hc) r (by omega)

theorem cconn_side : {inner : V → Prop} → {n : Nat} →
    (t : TubeOf rotation.toRotationSystem T inner n) →
    EdgeShoreConnected G (ZigzagSlab.compShore (t.side n)) →
    ∀ r, r ≤ n → EdgeShoreConnected G (ZigzagSlab.compShore (t.side r))
  | _, _, nil _ _, hc, _, _ => hc
  | _, _, cons S rest, hc, r + 1, hr => cconn_side rest hc r (by omega)
  | _, _, cons S rest, hc, 0, _ => by
    have h0 := cconn_side rest hc 0 (by omega)
    cases rest <;> exact S.edgeShoreConnected_comp_slab hT h0

theorem sideShore_ssubset_succ [Nonempty Vt] : {inner : V → Prop} → {n : Nat} →
    (t : TubeOf rotation.toRotationSystem T inner n) → ∀ r, r < n →
    sideShore (G := G) (t.side r) ⊂ sideShore (t.side (r + 1))
  | _, _, nil _ _, _, hr => absurd hr (Nat.not_lt_zero _)
  | _, _, cons S rest, 0, _ => by
    cases rest <;> exact S.sideShore_ssubset_inner' hT
  | _, _, cons _ rest, r + 1, hr => sideShore_ssubset_succ rest r (by omega)

theorem sideShore_ssubset_of_lt [Nonempty Vt] {inner : V → Prop} {n : Nat}
    (t : TubeOf rotation.toRotationSystem T inner n) (r : Nat) :
    ∀ r', r < r' → r' ≤ n → sideShore (G := G) (t.side r) ⊂ sideShore (t.side r')
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | r' + 1, h, hr' => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact (sideShore_ssubset_of_lt t r r' h (by omega)).trans
        (t.sideShore_ssubset_succ hT r' (by omega))
    · exact t.sideShore_ssubset_succ hT r (by omega)

/-- **No long periodic corridor of any shape, from base hypotheses.**  A coherent chain of
`n` copies of a slab shape `T` whose relation stabilises at index `m`, whose innermost side
is good with connected shore and whose outermost complement is connected, satisfies
`n + 1 - m ≤ k!·k!·(6k+1)`. -/
theorem le_of_tubeOf [Nonempty Vt] (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {m : Nat} (hstab : ∀ W : Set (Fin k → Color), (relImage T)^[m + 1] W = (relImage T)^[m] W)
    (hk2 : 2 ≤ k) {inner : V → Prop} {n : Nat}
    (t : TubeOf rotation.toRotationSystem T inner n) (hc : t.Coherent)
    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))
    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n + 1 - m ≤ Nat.factorial k * (Nat.factorial k * (6 * k + 1)) := by
  let nodes : Fin (n + 1) → LiteralShoreNode rotation k k := fun r =>
    mkNode ⟨t.goodSide_side hT hgood r (by omega), t.conn_side hT hgood hconn r (by omega),
      t.cconn_side hT hcconn r (by omega)⟩ (t.sideEquiv r) hk2
  exact le_of_tubeOf_nodes minimal hstab t hc nodes (fun r => mkNode_keep _ _ _)
    (fun r r' hrr' => t.sideShore_ssubset_of_lt hT r r' hrr' (by omega))

end TubeOf

end TubeTheorem

end TubeSlab
end Mettapedia.GraphTheory.FourColor
