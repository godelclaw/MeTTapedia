import Mettapedia.GraphTheory.FourColor.GoertzelV24BranchQuartetConnected

/-!
# Width-preserving connectedization of branch decompositions

The finite simple-graph form of the connectedization theorem: a branch
decomposition of width `w` of a 2-edge-connected graph can be replaced by
a connected branch decomposition of width at most `w`.  The rooted tree with
its root leaf as up-set is made quartet-free by rotations that never
increase the width, and a quartet-free tree has both shores of every cut
connected.  This discharges `WidthPreservingConnectedization`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WidthPreservingConnectedization

open GoertzelV24BranchQuartetCalculus
open GoertzelV24BranchQuartetTree
open GoertzelV24BranchQuartetConnected
open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedBranchDecompositionAdapter
open GoertzelV24ConnectedEdgeShoreMajority
open EdgeLeafTree

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## The up-set form agrees with the standard predicates -/

theorem cutWidthLe_iff (w : ℕ) :
    ∀ (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet), Genuine (G := G) t up →
      (CutWidthLe (G := G) w t up ↔ EveryCutWidthAtMost (G := G) w t)
  | .leaf edge, up, hg => by
      rw [hg.up_eq, shore_leaf]
      simp only [CutWidthLe, EveryCutWidthAtMost, edgeShoreMiddleVertices_eq_bd]
  | .fork a b, up, hg => by
      have hup := hg.up_eq
      rw [shore_fork] at hup
      simp only [CutWidthLe, EveryCutWidthAtMost, edgeShoreMiddleVertices_eq_bd, shore_fork]
      rw [cutWidthLe_iff w a _ hg.left, cutWidthLe_iff w b _ hg.right, hup]

theorem cutConnected_iff :
    ∀ (t : EdgeLeafTree G.edgeSet) (up : Finset G.edgeSet), Genuine (G := G) t up →
      (CutConnected (G := G) t up ↔ EveryCutShoreConnected (G := G) t)
  | .leaf edge, up, hg => by
      rw [hg.up_eq, shore_leaf]
      simp only [CutConnected, EveryCutShoreConnected]
  | .fork a b, up, hg => by
      have hup := hg.up_eq
      rw [shore_fork] at hup
      simp only [CutConnected, EveryCutShoreConnected, shore_fork]
      rw [cutConnected_iff a _ hg.left, cutConnected_iff b _ hg.right, hup]

theorem exists_fork_of_perm {t a b : EdgeLeafTree G.edgeSet}
    (hperm : t.leafList.Perm (fork a b).leafList) :
    ∃ p q : EdgeLeafTree G.edgeSet, t = fork p q := by
  cases t with
  | leaf edge =>
      exfalso
      have hlen := hperm.length_eq
      simp only [leafList_leaf, leafList_fork, List.length_singleton,
        List.length_append] at hlen
      have ha := List.length_pos_of_ne_nil (leafList_ne_nil a)
      have hb := List.length_pos_of_ne_nil (leafList_ne_nil b)
      omega
  | fork p q => exact ⟨p, q, rfl⟩

/-! ## The theorem -/

/-- A width-`w` rooted branch decomposition of a 2-edge-connected graph is
replaced by a connected one of width at most `w`. -/
theorem exists_connected_rootedBranchDecomposition (h₂ : G.IsEdgeConnected 2)
    (w : ℕ) (d : RootedBranchDecomposition (G := G)) (hw : d.WidthAtMost w) :
    ∃ c : RootedBranchDecomposition (G := G), c.Connected ∧ c.WidthAtMost w := by
  obtain ⟨r, L, R, hnodup, hcover⟩ := d
  obtain ⟨hwr, hwL, hwR⟩ := hw
  have hnodup' := List.nodup_cons.1 hnodup
  have hg : Genuine (G := G) (fork L R) {r} :=
    { nodup := hnodup'.2
      disjoint := by
        rw [Finset.disjoint_singleton_right, shore_fork, Finset.mem_union,
          mem_shore_iff, mem_shore_iff, ← List.mem_append]
        exact hnodup'.1
      cover := by
        rw [List.toFinset_cons, List.toFinset_append] at hcover
        rw [shore_fork, Finset.union_comm, ← Finset.insert_eq]
        exact hcover
      upNonempty := Finset.singleton_nonempty r }
  have hwt : CutWidthLe (G := G) w (fork L R) {r} := by
    refine ⟨?_, (cutWidthLe_iff w L _ hg.left).2 hwL, (cutWidthLe_iff w R _ hg.right).2 hwR⟩
    have hwr' := hwr
    rw [edgeShoreMiddleVertices_eq_bd, ← hg.shore_eq, shore_fork, bd_comm] at hwr'
    exact hwr'
  obtain ⟨t', hperm, hw', hqf⟩ := exists_quartetFree (fork L R) {r} hg hwt
  obtain ⟨a', b', rfl⟩ := exists_fork_of_perm hperm
  have hg' : Genuine (G := G) (fork a' b') {r} := hg.of_perm hperm
  have hcc : CutConnected (G := G) (fork a' b') {r} :=
    cutConnected_of_quartetFree h₂ _ _ hg' hqf (Finset.card_singleton r)
      (edgeShoreConnected_singleton r)
  obtain ⟨-, -, hca, hcb⟩ := hcc
  obtain ⟨-, hwa, hwb⟩ := hw'
  have hperm' : (a'.leafList ++ b'.leafList).Perm (L.leafList ++ R.leafList) := hperm
  refine ⟨⟨r, a', b', ?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_cons]
    exact ⟨fun h => hnodup'.1 (hperm'.mem_iff.1 h), hperm'.nodup_iff.2 hnodup'.2⟩
  · rw [List.toFinset_cons, List.toFinset_eq_of_perm _ _ hperm']
    rw [List.toFinset_cons] at hcover
    exact hcover
  · unfold RootedBranchDecomposition.Connected
    exact ⟨edgeShoreConnected_singleton r, edgeShoreConnected_compl_singleton h₂ r,
      (cutConnected_iff a' _ hg'.left).1 hca, (cutConnected_iff b' _ hg'.right).1 hcb⟩
  · unfold RootedBranchDecomposition.WidthAtMost
    exact ⟨hwr, (cutWidthLe_iff w a' _ hg'.left).1 hwa, (cutWidthLe_iff w b' _ hg'.right).1 hwb⟩

/-- The width-preserving connectedization proposition holds. -/
theorem widthPreservingConnectedization : WidthPreservingConnectedization.{u} :=
  fun h₂ w d hw => exists_connected_rootedBranchDecomposition h₂ w d hw

end

end GoertzelV24WidthPreservingConnectedization

end Mettapedia.GraphTheory.FourColor
