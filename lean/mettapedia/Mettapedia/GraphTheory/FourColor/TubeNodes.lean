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

end TubeSlab
end Mettapedia.GraphTheory.FourColor
