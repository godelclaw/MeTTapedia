import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedBranchDecompositionForest

/-!
# The standard connected branch-decomposition interface

The external theorem of Fomin--Fraigniaud--Thilikos is stated for an
unrooted ternary tree whose leaves biject with the graph edges.  After
choosing one leaf as root, such a tree is represented by one distinguished
edge and the two binary edge-leaf trees adjacent to its first internal
vertex.  This file separates the two standard properties of that rooted
encoding:

* every cut has two connected edge-induced shores;
* every middle set has bounded cardinality.

It then proves that these properties imply the exact consumer structure in
`GoertzelV24ConnectedBranchDecompositionForest`.  Thus the external
connectedization theorem and the route's branchwidth/wall input can be kept
as two different propositions; neither is hidden in the literal-shore
consumer.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedBranchDecompositionAdapter

open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedEdgeShoreMajority

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## A rooted encoding of the standard ternary tree -/

/-- A standard branch-decomposition tree after choosing one edge leaf as
root.  Deleting that leaf and its incident internal vertex leaves the two
binary trees `left` and `right`.  The fields say exactly that the leaves
biject with the ambient graph edges. -/
structure RootedBranchDecomposition where
  rootEdge : G.edgeSet
  left : EdgeLeafTree G.edgeSet
  right : EdgeLeafTree G.edgeSet
  leavesNodup :
    (rootEdge :: (left.leafList ++ right.leafList)).Nodup
  leavesCover :
    (rootEdge :: (left.leafList ++ right.leafList)).toFinset = Finset.univ

/-! ## The two independent standard predicates -/

/-- At every tree cut below `tree`, both edge-induced shores are connected.
This is the literal rooted form of the connectedness condition in a standard
connected branch decomposition, including its leaf cuts. -/
def EveryCutShoreConnected : EdgeLeafTree G.edgeSet → Prop
  | .leaf edge =>
      EdgeShoreConnected G {edge} ∧
      EdgeShoreConnected G (Finset.univ \ {edge})
  | .fork left right =>
      EdgeShoreConnected G (EdgeLeafTree.fork left right).shore ∧
      EdgeShoreConnected G
        (Finset.univ \ (EdgeLeafTree.fork left right).shore) ∧
      EveryCutShoreConnected left ∧
      EveryCutShoreConnected right

/-- Every tree cut below `tree`, including a leaf cut, has middle-set size at
most `bound`. -/
def EveryCutWidthAtMost (bound : Nat) : EdgeLeafTree G.edgeSet → Prop
  | .leaf edge =>
      (edgeShoreMiddleVertices G {edge}).card ≤ bound
  | .fork left right =>
      (edgeShoreMiddleVertices G
        (EdgeLeafTree.fork left right).shore).card ≤ bound ∧
      EveryCutWidthAtMost bound left ∧
      EveryCutWidthAtMost bound right

/-- At every non-leaf cut below `tree`, both edge-induced shores are
connected.  Leaf cuts are omitted because the literal descent never consumes
them; the full external connected decomposition supplies this restriction
automatically. -/
def EveryForkShoreConnected : EdgeLeafTree G.edgeSet → Prop
  | .leaf _ => True
  | .fork left right =>
      EdgeShoreConnected G (EdgeLeafTree.fork left right).shore ∧
      EdgeShoreConnected G
        (Finset.univ \ (EdgeLeafTree.fork left right).shore) ∧
      EveryForkShoreConnected left ∧
      EveryForkShoreConnected right

/-- Every non-leaf cut below `tree` has middle-set size at most `bound`. -/
def EveryForkWidthAtMost (bound : Nat) : EdgeLeafTree G.edgeSet → Prop
  | .leaf _ => True
  | .fork left right =>
      (edgeShoreMiddleVertices G
        (EdgeLeafTree.fork left right).shore).card ≤ bound ∧
      EveryForkWidthAtMost bound left ∧
      EveryForkWidthAtMost bound right

namespace RootedBranchDecomposition

/-- The rooted encoding is connected when both shores of every tree cut are
connected, including the distinguished root-leaf cut and all cuts in the two
surviving binary trees. -/
def Connected (decomposition : RootedBranchDecomposition (G := G)) : Prop :=
  EdgeShoreConnected G {decomposition.rootEdge} ∧
  EdgeShoreConnected G (Finset.univ \ {decomposition.rootEdge}) ∧
  EveryCutShoreConnected (G := G) decomposition.left ∧
  EveryCutShoreConnected (G := G) decomposition.right

/-- The rooted encoding has width at most `bound` when every tree cut,
including the distinguished root-leaf cut, has middle-set size at most
`bound`. -/
def WidthAtMost (decomposition : RootedBranchDecomposition (G := G))
    (bound : Nat) : Prop :=
  (edgeShoreMiddleVertices G {decomposition.rootEdge}).card ≤ bound ∧
  EveryCutWidthAtMost (G := G) bound decomposition.left ∧
  EveryCutWidthAtMost (G := G) bound decomposition.right

end RootedBranchDecomposition

/-! ## Conversion to the literal-shore consumer -/

/-- Forgetting leaf cuts from the full connectedness predicate leaves the
internal-fork predicate consumed by the checked descent. -/
theorem everyForkShoreConnected_of_everyCut :
    (tree : EdgeLeafTree G.edgeSet) →
      EveryCutShoreConnected (G := G) tree →
      EveryForkShoreConnected (G := G) tree
  | .leaf _, _ => by trivial
  | .fork left right, hconnected => by
      exact ⟨hconnected.1, hconnected.2.1,
        everyForkShoreConnected_of_everyCut left hconnected.2.2.1,
        everyForkShoreConnected_of_everyCut right hconnected.2.2.2⟩

/-- Forgetting leaf cuts from the full width predicate leaves the
internal-fork predicate consumed by the checked descent. -/
theorem everyForkWidthAtMost_of_everyCut (bound : Nat) :
    (tree : EdgeLeafTree G.edgeSet) →
      EveryCutWidthAtMost (G := G) bound tree →
      EveryForkWidthAtMost (G := G) bound tree
  | .leaf _, _ => by trivial
  | .fork left right, hwidth => by
      exact ⟨hwidth.1,
        everyForkWidthAtMost_of_everyCut bound left hwidth.2.1,
        everyForkWidthAtMost_of_everyCut bound right hwidth.2.2⟩

/-- Connectedness and the two numerical width bounds combine to the
nodewise geometry consumed by the checked literal-shore forest. -/
theorem everyForkGeometry_of_connected_width
    (k w : Nat) :
    (tree : EdgeLeafTree G.edgeSet) →
      EveryForkShoreConnected (G := G) tree →
      EveryForkWidthAtMost (G := G) k tree →
      EveryForkWidthAtMost (G := G) w tree →
      EveryForkGeometry (G := G) k w tree
  | .leaf edge, _, _, _ => by trivial
  | .fork left right, hconnected, hk, hw => by
      refine ⟨?_, ?_, ?_⟩
      · exact
          { shoreConnected := hconnected.1
            complementConnected := hconnected.2.1
            widthMiddle := hk.1
            middleBound := hw.1 }
      · exact everyForkGeometry_of_connected_width k w left
          hconnected.2.2.1 hk.2.1 hw.2.1
      · exact everyForkGeometry_of_connected_width k w right
          hconnected.2.2.2 hk.2.2 hw.2.2

/-- A rooted standard connected branch decomposition with the stated width
bounds supplies exactly the consumer structure used by the descent. -/
def RootedBranchDecomposition.toConsumer
    (decomposition : RootedBranchDecomposition (G := G))
    (k w : Nat)
    (hconnected : decomposition.Connected)
    (hk : decomposition.WidthAtMost k)
    (hw : decomposition.WidthAtMost w) :
    RootedConnectedBranchDecomposition (G := G) k w where
  rootEdge := decomposition.rootEdge
  left := decomposition.left
  right := decomposition.right
  leavesNodup := decomposition.leavesNodup
  leavesCover := decomposition.leavesCover
  leftGeometry := everyForkGeometry_of_connected_width k w
    decomposition.left
      (everyForkShoreConnected_of_everyCut decomposition.left hconnected.2.2.1)
      (everyForkWidthAtMost_of_everyCut k decomposition.left hk.2.1)
      (everyForkWidthAtMost_of_everyCut w decomposition.left hw.2.1)
  rightGeometry := everyForkGeometry_of_connected_width k w
    decomposition.right
      (everyForkShoreConnected_of_everyCut decomposition.right hconnected.2.2.2)
      (everyForkWidthAtMost_of_everyCut k decomposition.right hk.2.2)
      (everyForkWidthAtMost_of_everyCut w decomposition.right hw.2.2)

/-- A connected rooted branch decomposition at one width supplies the
common `k = w` consumer used by the final bounded-width assembly. -/
def RootedBranchDecomposition.toConsumerAtWidth
    (decomposition : RootedBranchDecomposition (G := G))
    (w : Nat)
    (hconnected : decomposition.Connected)
    (hwidth : decomposition.WidthAtMost w) :
    RootedConnectedBranchDecomposition (G := G) w w :=
  decomposition.toConsumer w w hconnected hwidth hwidth

/-- Top-level citation form of `RootedBranchDecomposition.toConsumerAtWidth`.
It exposes the complete standard-to-literal adapter under a declaration name
that prose status tools can resolve without interpreting dotted namespace
extensions. -/
def rootedBranchDecompositionToConsumerAtWidth
    (decomposition : RootedBranchDecomposition (G := G))
    (w : Nat)
    (hconnected : decomposition.Connected)
    (hwidth : decomposition.WidthAtMost w) :
    RootedConnectedBranchDecomposition (G := G) w w :=
  decomposition.toConsumerAtWidth w hconnected hwidth

/-! ## The exact external connectedization proposition -/

/-- A connected finite graph with no bridge is 2-edge-connected in
mathlib's edge-connectivity sense.  This is the exact graph hypothesis used
by the external connectedization theorem. -/
theorem isEdgeConnected_two_of_connected_no_bridges
    (hconnected : G.Connected)
    (hnoBridge : ∀ edge ∈ G.edgeSet, ¬ G.IsBridge edge) :
    G.IsEdgeConnected 2 := by
  rw [SimpleGraph.isEdgeConnected_two]
  intro edge
  by_cases hedge : edge ∈ G.edgeSet
  · induction edge using Sym2.inductionOn with
    | _ left right =>
        exact (hconnected.connected_delete_edge_of_not_isBridge
          (hnoBridge s(left, right) hedge)).preconnected
  · rw [SimpleGraph.deleteEdges_eq_self.mpr
      (Set.disjoint_singleton_right.mpr hedge)]
    exact hconnected.preconnected

/-- The width-preserving connectedization theorem, stated independently of
the Four-Colour route.  This is the finite simple-graph specialization of
Fomin--Fraigniaud--Thilikos Theorem 1: a width-`w` branch decomposition of a
2-edge-connected graph can be replaced by a connected one without increasing
the width.

This definition is a proposition, not an axiom.  Callers that rely on the
external theorem must provide it explicitly. -/
def WidthPreservingConnectedization : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite],
    G.IsEdgeConnected 2 →
    ∀ (w : Nat) (decomposition : RootedBranchDecomposition (G := G)),
      decomposition.WidthAtMost w →
      ∃ connected : RootedBranchDecomposition (G := G),
        connected.Connected ∧ connected.WidthAtMost w

end

end GoertzelV24ConnectedBranchDecompositionAdapter

end Mettapedia.GraphTheory.FourColor
