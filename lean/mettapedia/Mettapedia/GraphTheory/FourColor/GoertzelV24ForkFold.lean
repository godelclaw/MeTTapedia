import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkProjection
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionForest
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionAdapter

/-!
# The colour coordinate folded over an actual edge-leaf tree

The children at a fork carry states on their own middle vertices. The exact
fork transition checks clashes at their shared middle vertices and projects
their zero-extended union to the parent middle vertices. A duplicate-free leaf
labelling makes the child edge shores disjoint, allowing the literal colouring
theorem to be used at every fork. This file proves the colour coordinate of the
fold against the physical edge shore represented by each subtree.

The fold does not assert planarity, structural-state adequacy, or the finite
base audit. Those require their own coordinates and coverage arguments.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFold

open GoertzelV24ForkInterfaceSupport
open GoertzelV24ForkProjection
open GoertzelV24ForkLocality
open GoertzelV24ConnectedBranchDecompositionForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The same physical edge shore as `EdgeLeafTree.shore`, computed by fork
union so that the type of the fork transition reduces definitionally. -/
def computedShore : EdgeLeafTree E → Finset E
  | .leaf e => {e}
  | .fork left right => computedShore left ∪ computedShore right

omit [Fintype E] in
theorem computedShore_eq_shore : ∀ tree : EdgeLeafTree E,
    computedShore tree = tree.shore := by
  intro tree
  induction tree with
  | leaf edge => simp [computedShore]
  | fork left right ihLeft ihRight =>
      simp [computedShore, ihLeft, ihRight, EdgeLeafTree.shore_fork]

/-- Evaluate boundary colour support from leaves up. This evaluator is defined
for any labelled tree; exactness needs duplicate-free leaves. -/
def fold (inc : E → Finset V) :
    (tree : EdgeLeafTree E) → Finset (Boundary inc (computedShore tree))
  | .leaf e => leafSupport inc e
  | .fork left right =>
      localForkTransition inc (computedShore left) (computedShore right)
        (fold inc left) (fold inc right)

/-- The recursively computed state at every node is its literal colour
support on that node's actual edge shore. -/
theorem fold_exact (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3) :
    ∀ (tree : EdgeLeafTree E), tree.leafList.Nodup →
      fold inc tree = boundarySupport inc (computedShore tree) := by
  intro tree
  induction tree with
  | leaf edge =>
      intro _
      exact leafSupport_eq_boundarySupport inc edge
  | fork left right ihLeft ihRight =>
      intro hnodup
      have hLeft : left.leafList.Nodup := List.Nodup.of_append_left hnodup
      have hRight : right.leafList.Nodup := List.Nodup.of_append_right hnodup
      have hlist : List.Disjoint left.leafList right.leafList :=
        List.disjoint_of_nodup_append hnodup
      have hdisj : Disjoint (computedShore left) (computedShore right) := by
        rw [computedShore_eq_shore, computedShore_eq_shore]
        apply Finset.disjoint_left.mpr
        intro edge heLeft heRight
        exact hlist (by simpa [EdgeLeafTree.shore] using heLeft)
          (by simpa [EdgeLeafTree.shore] using heRight)
      have hstep := localForkTransition_exact inc hcubic
        (computedShore left) (computedShore right) hdisj
      simpa only [fold, computedShore, ihLeft hLeft, ihRight hRight]
        using hstep.symm

/-- Any complete duplicate-free tree presents exactly the colourings of its
whole ambient edge set. -/
theorem fold_root_nonempty_iff (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (tree : EdgeLeafTree E) (hnodup : tree.leafList.Nodup)
    (hcover : tree.shore = Finset.univ) :
    (fold inc tree).Nonempty ↔
      ∃ c : E → Fin 3, Proper inc Finset.univ c := by
  rw [fold_exact inc hcubic tree hnodup, computedShore_eq_shore, hcover]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc, -⟩ := (mem_boundarySupport inc Finset.univ).mp hb
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨restrict inc Finset.univ (profile inc Finset.univ c),
      (mem_boundarySupport inc Finset.univ).mpr ⟨c, hc, rfl⟩⟩

section BranchAdapter

open GoertzelV24ConnectedBranchDecompositionAdapter

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Restore the root edge to the two child trees of a supplied rooted branch
decomposition. This is the actual complete edge-leaf tree used by the colour
fold. -/
def wholeTree (decomposition : RootedBranchDecomposition (G := G)) :
    EdgeLeafTree G.edgeSet :=
  .fork (.leaf decomposition.rootEdge)
    (.fork decomposition.left decomposition.right)

theorem wholeTree_nodup (decomposition : RootedBranchDecomposition (G := G)) :
    (wholeTree decomposition).leafList.Nodup := by
  change (decomposition.rootEdge ::
    (decomposition.left.leafList ++ decomposition.right.leafList)).Nodup
  exact decomposition.leavesNodup

theorem wholeTree_cover (decomposition : RootedBranchDecomposition (G := G)) :
    (wholeTree decomposition).shore = Finset.univ := by
  change (decomposition.rootEdge ::
    (decomposition.left.leafList ++ decomposition.right.leafList)).toFinset = Finset.univ
  exact decomposition.leavesCover

/-- A branch decomposition's evaluated root state has precisely the literal
closed colouring semantics. The decomposition provides every edge once; the
fold theorem checks every fork. -/
theorem fold_rooted_nonempty_iff (inc : G.edgeSet → Finset W)
    (hcubic : ∀ v : W, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (decomposition : RootedBranchDecomposition (G := G)) :
    (fold inc (wholeTree decomposition)).Nonempty ↔
      ∃ c : G.edgeSet → Fin 3, Proper inc Finset.univ c :=
  fold_root_nonempty_iff inc hcubic (wholeTree decomposition)
    (wholeTree_nodup decomposition) (wholeTree_cover decomposition)

end BranchAdapter

section K4Control

open GoertzelV24ForkInterfaceSupport

/-- A complete, nontrivial fork tree for the six edges of `K4`. -/
def K4Tree : EdgeLeafTree (Fin 6) :=
  .fork (.fork (.leaf 0) (.fork (.leaf 1) (.leaf 2)))
    (.fork (.leaf 3) (.fork (.leaf 4) (.leaf 5)))

theorem K4Tree_nodup : K4Tree.leafList.Nodup := by decide +kernel

theorem K4Tree_cover : K4Tree.shore = Finset.univ := by decide +kernel

/-- A closed fold result has its literal Tait-colouring meaning. -/
theorem K4_fold_nonempty_iff :
    (fold K4 K4Tree).Nonempty ↔
      ∃ c : Fin 6 → Fin 3, Proper K4 Finset.univ c :=
  fold_root_nonempty_iff K4 K4_cubic K4Tree K4Tree_nodup K4Tree_cover

theorem K4_fold_audit : (fold K4 K4Tree).Nonempty := by decide +kernel

theorem K4_from_fold : ∃ c : Fin 6 → Fin 3, Proper K4 Finset.univ c :=
  K4_fold_nonempty_iff.mp K4_fold_audit

end K4Control

end Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFold
