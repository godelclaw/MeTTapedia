import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedShoreLiteralNode
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge

/-!
# A rooted connected branch decomposition gives two pumpable shore trees

A branch decomposition is leaf-labelled by graph edges.  Rooting at one
leaf leaves a binary fork.  The cut above that fork has a one-edge
complement, so it is not a literal two-sided open tangle and must not be
inserted as a fake root node.  Its two children instead give two genuine
rooted shore trees.  Every internal descendant is labelled by the set of
edge leaves below it.

This file carries out that tree bookkeeping.  It derives strict nesting and
the edge/vertex accounting from a duplicate-free complete leaf labelling.
The only nodewise input left visible is the connected-cut geometry supplied
by a connected branch decomposition: both edge shores are connected and the
middle set has bounded size.  Cubicity and the complete distinct edge-leaf
labelling derive nonemptiness of both majority vertex sides internally.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedBranchDecompositionForest

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

/-! ## Edge-labelled binary trees -/

/-- A full binary tree whose leaves, rather than its internal vertices, carry
the graph edges of a rooted branch decomposition. -/
inductive EdgeLeafTree (E : Type u) where
  | leaf : E → EdgeLeafTree E
  | fork : EdgeLeafTree E → EdgeLeafTree E → EdgeLeafTree E
  deriving Inhabited

namespace EdgeLeafTree

variable {E : Type u}

/-- Edge labels in left-to-right leaf order. -/
def leafList : EdgeLeafTree E → List E
  | leaf edge => [edge]
  | fork left right => left.leafList ++ right.leafList

/-- The edge shore below a rooted subtree. -/
def shore [DecidableEq E] (tree : EdgeLeafTree E) : Finset E :=
  tree.leafList.toFinset

/-- Number of internal forks. -/
def forkCount : EdgeLeafTree E → Nat
  | leaf _ => 0
  | fork left right => 1 + left.forkCount + right.forkCount

@[simp] theorem leafList_leaf (edge : E) :
    (leaf edge).leafList = [edge] := rfl

@[simp] theorem leafList_fork (left right : EdgeLeafTree E) :
    (fork left right).leafList = left.leafList ++ right.leafList := rfl

@[simp] theorem forkCount_leaf (edge : E) :
    (leaf edge).forkCount = 0 := rfl

@[simp] theorem forkCount_fork (left right : EdgeLeafTree E) :
    (fork left right).forkCount =
      1 + left.forkCount + right.forkCount := rfl

theorem leafList_ne_nil (tree : EdgeLeafTree E) : tree.leafList ≠ [] := by
  induction tree with
  | leaf edge => simp
  | fork left right ihleft ihright => simp [leafList, ihleft]

theorem leafList_length_eq_forkCount_add_one (tree : EdgeLeafTree E) :
    tree.leafList.length = tree.forkCount + 1 := by
  induction tree with
  | leaf edge => simp [leafList, forkCount]
  | fork left right ihleft ihright =>
      simp only [leafList, List.length_append, forkCount]
      omega

variable [DecidableEq E]

@[simp] theorem shore_leaf (edge : E) :
    (leaf edge).shore = {edge} := by simp [shore]

@[simp] theorem shore_fork (left right : EdgeLeafTree E) :
    (fork left right).shore = left.shore ∪ right.shore := by
  simp [shore, leafList, List.toFinset_append]

theorem shore_nonempty (tree : EdgeLeafTree E) : tree.shore.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hlist : tree.leafList = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro edge hedge
    have : edge ∈ tree.shore := by simpa [shore] using hedge
    simpa [hempty] using this
  exact tree.leafList_ne_nil hlist

theorem shore_left_subset (left right : EdgeLeafTree E) :
    left.shore ⊆ (fork left right).shore := by
  simp

theorem shore_right_subset (left right : EdgeLeafTree E) :
    right.shore ⊆ (fork left right).shore := by
  simp

theorem shore_left_ssubset (left right : EdgeLeafTree E)
    (hnodup : (left.leafList ++ right.leafList).Nodup) :
    left.shore ⊂ (fork left right).shore := by
  have hdisjoint : List.Disjoint left.leafList right.leafList :=
    List.disjoint_of_nodup_append hnodup
  obtain ⟨edge, hedgeRight⟩ := right.shore_nonempty
  have hedgeNotLeft : edge ∉ left.shore := by
    intro hedgeLeft
    exact hdisjoint (by simpa [shore] using hedgeLeft)
      (by simpa [shore] using hedgeRight)
  refine Finset.ssubset_iff_subset_ne.mpr ⟨shore_left_subset left right, ?_⟩
  intro heq
  have : edge ∈ left.shore := by
    rw [heq, shore_fork]
    exact Finset.mem_union_right _ hedgeRight
  exact hedgeNotLeft this

theorem shore_right_ssubset (left right : EdgeLeafTree E)
    (hnodup : (left.leafList ++ right.leafList).Nodup) :
    right.shore ⊂ (fork left right).shore := by
  have hdisjoint : List.Disjoint left.leafList right.leafList :=
    List.disjoint_of_nodup_append hnodup
  obtain ⟨edge, hedgeLeft⟩ := left.shore_nonempty
  have hedgeNotRight : edge ∉ right.shore := by
    intro hedgeRight
    exact hdisjoint (by simpa [shore] using hedgeLeft)
      (by simpa [shore] using hedgeRight)
  refine Finset.ssubset_iff_subset_ne.mpr ⟨shore_right_subset left right, ?_⟩
  intro heq
  have : edge ∈ right.shore := by
    rw [heq, shore_fork]
    exact Finset.mem_union_left _ hedgeLeft
  exact hedgeNotRight this

/-- The shore of an internal fork contains at least one edge from each
child, hence at least two edges when the leaf labels are distinct. -/
theorem two_le_card_shore_fork (left right : EdgeLeafTree E)
    (hnodup : (left.leafList ++ right.leafList).Nodup) :
    2 ≤ (fork left right).shore.card := by
  have hcard := List.toFinset_card_of_nodup hnodup
  have hleft : 0 < left.leafList.length :=
    List.length_pos_of_ne_nil left.leafList_ne_nil
  have hright : 0 < right.leafList.length :=
    List.length_pos_of_ne_nil right.leafList_ne_nil
  change 2 ≤ (left.leafList ++ right.leafList).toFinset.card
  rw [hcard, List.length_append]
  omega

end EdgeLeafTree

/-! ## Nodewise connected-cut data and the conversion -/

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Nonempty majority sides from nontrivial connected edge shores -/

/-- Two distinct shore edges incident with one vertex put that vertex on the
majority side.  This is the local endpoint of the connected-shore argument. -/
theorem majorityVertexSide_of_two_incident_edges
    {shore : Finset G.edgeSet} {vertex : V} {first second : G.edgeSet}
    (hfirstShore : first ∈ shore) (hsecondShore : second ∈ shore)
    (hfirstIncident : vertex ∈ (first : Sym2 V))
    (hsecondIncident : vertex ∈ (second : Sym2 V))
    (hne : first ≠ second) :
    majorityVertexSide G shore vertex := by
  have hfirst : first ∈ shoreIncidentEdges G shore vertex := by
    rw [mem_shoreIncidentEdges_iff]
    exact ⟨hfirstIncident, hfirstShore⟩
  have hsecond : second ∈ shoreIncidentEdges G shore vertex := by
    rw [mem_shoreIncidentEdges_iff]
    exact ⟨hsecondIncident, hsecondShore⟩
  have hsubset : ({first, second} : Finset G.edgeSet) ⊆
      shoreIncidentEdges G shore vertex := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact hfirst
    · exact hsecond
  have hcard : ({first, second} : Finset G.edgeSet).card = 2 := by
    simp [hne]
  unfold majorityVertexSide
  rw [← hcard]
  exact Finset.card_le_card hsubset

/-- A walk in one edge shore, bracketed by distinct shore edges at its two
ends, contains a vertex incident with two distinct shore edges. -/
theorem exists_majorityVertexSide_of_walk_between_distinct_edges
    (shore : Finset G.edgeSet) {start finish : V}
    (walk : G.Walk start finish) :
    ∀ (first last : G.edgeSet), first ∈ shore → last ∈ shore →
      start ∈ (first : Sym2 V) → finish ∈ (last : Sym2 V) →
      first ≠ last →
      (∀ edge : G.edgeSet,
        (edge : Sym2 V) ∈ walk.edges → edge ∈ shore) →
      ∃ vertex, majorityVertexSide G shore vertex := by
  induction walk with
  | nil =>
      intro first last hfirstShore hlastShore hfirstIncident
        hlastIncident hne hwalk
      exact ⟨_, majorityVertexSide_of_two_incident_edges
        hfirstShore hlastShore hfirstIncident hlastIncident hne⟩
  | @cons start next finish hadj tail ih =>
      intro first last hfirstShore hlastShore hfirstIncident
        hlastIncident hne hwalk
      let step : G.edgeSet :=
        ⟨s(start, next), (G.mem_edgeSet).2 hadj⟩
      have hstepShore : step ∈ shore := by
        apply hwalk step
        simp [step]
      by_cases hfirstStep : first = step
      · apply ih step last hstepShore hlastShore
          (by simp [step]) hlastIncident
        · exact fun heq => hne (hfirstStep.trans heq)
        · intro edge hedge
          apply hwalk edge
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr hedge
      · exact ⟨start, majorityVertexSide_of_two_incident_edges
          hfirstShore hstepShore hfirstIncident (by simp [step])
          hfirstStep⟩

/-- A connected edge shore with at least two edges has a nonempty majority
vertex side. -/
theorem exists_majorityVertexSide_of_connected_of_two_le_card
    (shore : Finset G.edgeSet)
    (hconnected : EdgeShoreConnected G shore)
    (htwo : 2 ≤ shore.card) :
    ∃ vertex, majorityVertexSide G shore vertex := by
  obtain ⟨first, hfirstShore, last, hlastShore, hne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < shore.card)
  obtain ⟨start, hstartIncident⟩ :=
    GoertzelV24MajorityShoreStateDescent.exists_incident_vertex first
  obtain ⟨finish, hfinishIncident⟩ :=
    GoertzelV24MajorityShoreStateDescent.exists_incident_vertex last
  obtain ⟨walk, hwalk⟩ := hconnected
    ⟨first, hfirstShore, hstartIncident⟩
    ⟨last, hlastShore, hfinishIncident⟩
  exact exists_majorityVertexSide_of_walk_between_distinct_edges shore walk
    first last hfirstShore hlastShore hstartIncident hfinishIncident hne hwalk

/-- Two distinct ambient edges outside a shore witness that its complement
contains at least two edges. -/
theorem two_le_card_complement_of_two_outside
    (shore : Finset G.edgeSet) {first second : G.edgeSet}
    (hne : first ≠ second) (hfirst : first ∉ shore)
    (hsecond : second ∉ shore) :
    2 ≤ (Finset.univ \ shore).card := by
  have hsubset : ({first, second} : Finset G.edgeSet) ⊆
      Finset.univ \ shore := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hfirst⟩
    · exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hsecond⟩
  have hcard : ({first, second} : Finset G.edgeSet).card = 2 := by
    simp [hne]
  rw [← hcard]
  exact Finset.card_le_card hsubset

/-- The exact graph-theoretic condition needed at an internal branch cut.
It deliberately contains no roots, ports, coordinates, or profile state. -/
structure ConnectedCutCondition (k w : Nat) (shore : Finset G.edgeSet) : Prop where
  shoreConnected : EdgeShoreConnected G shore
  complementConnected : EdgeShoreConnected G (Finset.univ \ shore)
  majorityNonempty : ∃ vertex, majorityVertexSide G shore vertex
  complementNonempty : ∃ vertex, ¬ majorityVertexSide G shore vertex
  widthMiddle : (edgeShoreMiddleVertices G shore).card ≤ k
  middleBound : (edgeShoreMiddleVertices G shore).card ≤ w

namespace ConnectedCutCondition

/-- Construct the exact cut condition from connected complementary shores
that each contain at least two edges.  Cubicity converts a majority vertex
of the complementary edge shore into a non-majority vertex of `shore`. -/
def ofConnectedTwo {k w : Nat} (shore : Finset G.edgeSet)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hshoreConnected : EdgeShoreConnected G shore)
    (hcomplementConnected : EdgeShoreConnected G (Finset.univ \ shore))
    (hshoreTwo : 2 ≤ shore.card)
    (hcomplementTwo : 2 ≤ (Finset.univ \ shore).card)
    (hwidthMiddle : (edgeShoreMiddleVertices G shore).card ≤ k)
    (hmiddleBound : (edgeShoreMiddleVertices G shore).card ≤ w) :
    ConnectedCutCondition (G := G) k w shore where
  shoreConnected := hshoreConnected
  complementConnected := hcomplementConnected
  majorityNonempty :=
    exists_majorityVertexSide_of_connected_of_two_le_card shore
      hshoreConnected hshoreTwo
  complementNonempty := by
    obtain ⟨vertex, hvertex⟩ :=
      exists_majorityVertexSide_of_connected_of_two_le_card
        (Finset.univ \ shore) hcomplementConnected hcomplementTwo
    exact ⟨vertex,
      (majorityVertexSide_complement_iff hcubic shore vertex).1 hvertex⟩
  widthMiddle := hwidthMiddle
  middleBound := hmiddleBound

/-- Package a connected branch cut as the already-verified shore node. -/
def toNode {k w : Nat} {shore : Finset G.edgeSet}
    (condition : ConnectedCutCondition (G := G) k w shore) :
    ConnectedShoreNode (G := G) k w where
  shore := shore
  shoreConnected := condition.shoreConnected
  complementConnected := condition.complementConnected
  majorityNonempty := condition.majorityNonempty
  complementNonempty := condition.complementNonempty
  widthMiddle := condition.widthMiddle
  middleBound := condition.middleBound

@[simp] theorem toNode_shore {k w : Nat} {shore : Finset G.edgeSet}
    (condition : ConnectedCutCondition (G := G) k w shore) :
    condition.toNode.shore = shore := rfl

end ConnectedCutCondition

/-- Every internal fork of a leaf tree satisfies the connected-cut
condition, recursively.  Leaves produce no cut node. -/
def EveryForkConnected (k w : Nat) :
    EdgeLeafTree G.edgeSet → Prop
  | .leaf _ => True
  | .fork left right =>
      ConnectedCutCondition (G := G) k w
        (EdgeLeafTree.fork left right).shore ∧
      EveryForkConnected k w left ∧ EveryForkConnected k w right

/-- The data supplied directly by a connected branch decomposition at one
internal fork.  Nonemptiness of the majority sides is intentionally absent:
it will be derived from the complete distinct leaf labelling. -/
structure ConnectedCutGeometry (k w : Nat)
    (shore : Finset G.edgeSet) : Prop where
  shoreConnected : EdgeShoreConnected G shore
  complementConnected : EdgeShoreConnected G (Finset.univ \ shore)
  widthMiddle : (edgeShoreMiddleVertices G shore).card ≤ k
  middleBound : (edgeShoreMiddleVertices G shore).card ≤ w

/-- Every internal fork carries only the connected-cut geometry supplied by
the decomposition. -/
def EveryForkGeometry (k w : Nat) : EdgeLeafTree G.edgeSet → Prop
  | .leaf _ => True
  | .fork left right =>
      ConnectedCutGeometry (G := G) k w
        (EdgeLeafTree.fork left right).shore ∧
      EveryForkGeometry k w left ∧ EveryForkGeometry k w right

/-- Complete nodewise connected-cut geometry to the exact condition consumed
by the literal shore tree.  Two fixed outside edges work recursively for
every descendant shore. -/
noncomputable def everyForkConnected_of_geometry
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (k w : Nat) :
    (tree : EdgeLeafTree G.edgeSet) →
      EveryForkGeometry (G := G) k w tree →
      tree.leafList.Nodup →
      (first second : G.edgeSet) → first ≠ second →
      first ∉ tree.shore → second ∉ tree.shore →
      EveryForkConnected (G := G) k w tree
  | .leaf edge, _, _, first, second, hne, hfirst, hsecond => by
      trivial
  | .fork left right, geometry, hnodup, first, second, hne,
      hfirst, hsecond => by
      have hparts := List.nodup_append'.mp hnodup
      refine ⟨ConnectedCutCondition.ofConnectedTwo
          (EdgeLeafTree.fork left right).shore hcubic
          geometry.1.shoreConnected geometry.1.complementConnected
          (EdgeLeafTree.two_le_card_shore_fork left right hnodup)
          (two_le_card_complement_of_two_outside
            (EdgeLeafTree.fork left right).shore hne hfirst hsecond)
          geometry.1.widthMiddle geometry.1.middleBound,
        ?_, ?_⟩
      · exact everyForkConnected_of_geometry hcubic k w left geometry.2.1
          hparts.1 first second hne
          (fun hedge => hfirst (EdgeLeafTree.shore_left_subset left right hedge))
          (fun hedge => hsecond (EdgeLeafTree.shore_left_subset left right hedge))
      · exact everyForkConnected_of_geometry hcubic k w right geometry.2.2
          hparts.2.1 first second hne
          (fun hedge => hfirst (EdgeLeafTree.shore_right_subset left right hedge))
          (fun hedge => hsecond (EdgeLeafTree.shore_right_subset left right hedge))

/-- Forget the edge leaves and retain one connected-shore label at every
internal fork. -/
noncomputable def toConnectedShoreTree (k w : Nat) :
    (tree : EdgeLeafTree G.edgeSet) → EveryForkConnected (G := G) k w tree →
      DecompTree (ConnectedShoreNode (G := G) k w)
  | .leaf _, _ => .tip
  | .fork left right, condition =>
      .node condition.1.toNode
        (toConnectedShoreTree k w left condition.2.1)
        (toConnectedShoreTree k w right condition.2.2)

@[simp] theorem nodeCount_toConnectedShoreTree (k w : Nat)
    (tree : EdgeLeafTree G.edgeSet)
    (condition : EveryForkConnected (G := G) k w tree) :
    nodeCount (toConnectedShoreTree k w tree condition) = tree.forkCount := by
  induction tree with
  | leaf edge => rfl
  | fork left right ihleft ihright =>
      simp only [toConnectedShoreTree, nodeCount,
        EdgeLeafTree.forkCount]
      rw [ihleft condition.2.1, ihright condition.2.2]

/-! ## Strict nesting is forced by distinct edge leaves -/

/-- The root label of a nontrivial child is strictly below its parent label.
A tip has no root label and satisfies the condition vacuously. -/
def RootShoreStrict {k w : Nat}
    (parent : ConnectedShoreNode (G := G) k w) :
    DecompTree (ConnectedShoreNode (G := G) k w) → Prop
  | .tip => True
  | .node child _ _ => child.shore ⊂ parent.shore

/-- Strictness on every parent--child link of a shore tree. -/
def LocallyStrictShoreTree {k w : Nat} :
    DecompTree (ConnectedShoreNode (G := G) k w) → Prop
  | .tip => True
  | .node parent left right =>
      RootShoreStrict parent left ∧ RootShoreStrict parent right ∧
      LocallyStrictShoreTree left ∧ LocallyStrictShoreTree right

theorem rootShoreStrict_of_onPath_head
    {k w : Nat} {parent head : ConnectedShoreNode (G := G) k w}
    {tree : DecompTree (ConnectedShoreNode (G := G) k w)}
    {tail : List (ConnectedShoreNode (G := G) k w)}
    (hroot : RootShoreStrict parent tree)
    (hpath : OnPath tree (head :: tail)) :
    head.shore ⊂ parent.shore := by
  cases tree with
  | tip => cases hpath
  | node child left right =>
      cases hpath <;> exact hroot

/-- A duplicate-free leaf labelling makes each converted parent--child shore
inclusion strict. -/
theorem locallyStrict_toConnectedShoreTree (k w : Nat)
    (tree : EdgeLeafTree G.edgeSet)
    (condition : EveryForkConnected (G := G) k w tree)
    (hnodup : tree.leafList.Nodup) :
    LocallyStrictShoreTree
      (toConnectedShoreTree k w tree condition) := by
  induction tree with
  | leaf edge => trivial
  | fork left right ihleft ihright =>
      have hparts := List.nodup_append'.mp hnodup
      refine ⟨?_, ?_, ihleft condition.2.1 hparts.1,
        ihright condition.2.2 hparts.2.1⟩
      · cases left with
        | leaf edge => trivial
        | fork first second =>
            simpa [RootShoreStrict, toConnectedShoreTree,
              ConnectedCutCondition.toNode] using
              EdgeLeafTree.shore_left_ssubset
                (EdgeLeafTree.fork first second) right hnodup
      · cases right with
        | leaf edge => trivial
        | fork first second =>
            simpa [RootShoreStrict, toConnectedShoreTree,
              ConnectedCutCondition.toNode] using
              EdgeLeafTree.shore_right_ssubset left
                (EdgeLeafTree.fork first second) hnodup

/-- Adjacent strict inclusions along a path imply all earlier/later strict
inclusions. -/
theorem pairwise_of_isChain_of_trans {A : Type*} {relation : A → A → Prop}
    (htrans : ∀ {a b c}, relation a b → relation b c → relation a c) :
    ∀ {items : List A}, items.IsChain relation → items.Pairwise relation := by
  intro items hchain
  induction items with
  | nil => simp
  | cons first tail ih =>
      cases tail with
      | nil => simp
      | cons second rest =>
          have hsplit : relation first second ∧
              (second :: rest).IsChain relation :=
            ⟨hchain.rel_head, hchain.tail⟩
          have hpairTail : (second :: rest).Pairwise relation :=
            ih hsplit.2
          apply List.pairwise_cons.mpr
          refine ⟨?_, hpairTail⟩
          intro item hitem
          simp only [List.mem_cons] at hitem
          rcases hitem with rfl | hitem
          · exact hsplit.1
          · exact htrans hsplit.1
              ((List.pairwise_cons.mp hpairTail).1 item hitem)

/-- Local parent--child strictness gives the all-comparable-pairs form used
by finite-interface pumping. -/
theorem strictConnectedShoreTree_of_locallyStrict
    {k w : Nat}
    {tree : DecompTree (ConnectedShoreNode (G := G) k w)}
    (hlocal : LocallyStrictShoreTree tree) :
    StrictConnectedShoreTree tree := by
  intro path hpath
  have hchain : path.IsChain
      (fun outer inner => inner.shore ⊂ outer.shore) := by
    induction hpath with
    | tip => exact List.isChain_nil
    | @left parent left right tail htail ih =>
        have htailChain := ih hlocal.2.2.1
        cases tail with
        | nil => exact List.isChain_singleton _
        | cons head rest =>
            have hstep := rootShoreStrict_of_onPath_head
              hlocal.1 htail
            exact htailChain.cons (by simpa using hstep)
    | @right parent left right tail htail ih =>
        have htailChain := ih hlocal.2.2.2
        cases tail with
        | nil => exact List.isChain_singleton _
        | cons head rest =>
            have hstep := rootShoreStrict_of_onPath_head
              hlocal.2.1 htail
            exact htailChain.cons (by simpa using hstep)
  have hpair := pairwise_of_isChain_of_trans
    (relation := fun outer inner : ConnectedShoreNode (G := G) k w =>
      inner.shore ⊂ outer.shore)
    (fun hab hbc => hbc.trans hab) hchain
  intro i j hij
  exact List.pairwise_iff_get.mp hpair i j hij

/-- The converted shore tree is strictly nested without an extra geometric
hypothesis. -/
theorem strict_toConnectedShoreTree (k w : Nat)
    (tree : EdgeLeafTree G.edgeSet)
    (condition : EveryForkConnected (G := G) k w tree)
    (hnodup : tree.leafList.Nodup) :
    StrictConnectedShoreTree
      (toConnectedShoreTree k w tree condition) :=
  strictConnectedShoreTree_of_locallyStrict
    (locallyStrict_toConnectedShoreTree k w tree condition hnodup)

/-! ## Rooting at one edge and the finite bound -/

/-- A connected branch decomposition after rooting at one distinguished edge
leaf.  Removing the degenerate top cut leaves the two binary subtrees below
`left` and `right`.  The complete duplicate-free leaf list is exactly the
ambient graph edge set. -/
structure RootedConnectedBranchDecomposition (k w : Nat) where
  rootEdge : G.edgeSet
  left : EdgeLeafTree G.edgeSet
  right : EdgeLeafTree G.edgeSet
  leavesNodup :
    (rootEdge :: (left.leafList ++ right.leafList)).Nodup
  leavesCover :
    (rootEdge :: (left.leafList ++ right.leafList)).toFinset = Finset.univ
  leftGeometry : EveryForkGeometry (G := G) k w left
  rightGeometry : EveryForkGeometry (G := G) k w right

namespace RootedConnectedBranchDecomposition

theorem left_leafList_nodup {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.left.leafList.Nodup :=
  (decomposition.leavesNodup.tail.of_append_left)

theorem right_leafList_nodup {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.right.leafList.Nodup :=
  (decomposition.leavesNodup.tail.of_append_right)

/-- The root edge lies outside the first nondegenerate rooted shore. -/
theorem rootEdge_not_mem_left_shore {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.rootEdge ∉ decomposition.left.shore := by
  intro hedge
  exact (List.nodup_cons.mp decomposition.leavesNodup).1
    (List.mem_append_left decomposition.right.leafList
      (by simpa [EdgeLeafTree.shore] using hedge))

/-- The root edge lies outside the second nondegenerate rooted shore. -/
theorem rootEdge_not_mem_right_shore {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.rootEdge ∉ decomposition.right.shore := by
  intro hedge
  exact (List.nodup_cons.mp decomposition.leavesNodup).1
    (List.mem_append_right decomposition.left.leafList
      (by simpa [EdgeLeafTree.shore] using hedge))

/-- Choose one edge from the opposite rooted subtree. -/
noncomputable def leftOutsideEdge {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    G.edgeSet :=
  Classical.choose decomposition.right.shore_nonempty

theorem leftOutsideEdge_mem_right_shore {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.leftOutsideEdge ∈ decomposition.right.shore :=
  Classical.choose_spec decomposition.right.shore_nonempty

/-- Choose one edge from the other opposite rooted subtree. -/
noncomputable def rightOutsideEdge {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    G.edgeSet :=
  Classical.choose decomposition.left.shore_nonempty

theorem rightOutsideEdge_mem_left_shore {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.rightOutsideEdge ∈ decomposition.left.shore :=
  Classical.choose_spec decomposition.left.shore_nonempty

theorem leftOutsideEdge_not_mem_left_shore {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.leftOutsideEdge ∉ decomposition.left.shore := by
  have hdisjoint : List.Disjoint decomposition.left.leafList
      decomposition.right.leafList :=
    List.disjoint_of_nodup_append decomposition.leavesNodup.tail
  intro hedge
  exact hdisjoint (by simpa [EdgeLeafTree.shore] using hedge)
    (by simpa [EdgeLeafTree.shore] using
      decomposition.leftOutsideEdge_mem_right_shore)

theorem rightOutsideEdge_not_mem_right_shore {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.rightOutsideEdge ∉ decomposition.right.shore := by
  have hdisjoint : List.Disjoint decomposition.left.leafList
      decomposition.right.leafList :=
    List.disjoint_of_nodup_append decomposition.leavesNodup.tail
  intro hedge
  exact hdisjoint
    (by simpa [EdgeLeafTree.shore] using
      decomposition.rightOutsideEdge_mem_left_shore)
    (by simpa [EdgeLeafTree.shore] using hedge)

theorem rootEdge_ne_leftOutsideEdge {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.rootEdge ≠ decomposition.leftOutsideEdge := by
  intro heq
  exact decomposition.rootEdge_not_mem_right_shore
    (heq ▸ decomposition.leftOutsideEdge_mem_right_shore)

theorem rootEdge_ne_rightOutsideEdge {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    decomposition.rootEdge ≠ decomposition.rightOutsideEdge := by
  intro heq
  exact decomposition.rootEdge_not_mem_left_shore
    (heq ▸ decomposition.rightOutsideEdge_mem_left_shore)

/-- The full connected-cut condition on the first tree is generated from
the supplied geometry, rather than assumed. -/
noncomputable def leftConnected {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    EveryForkConnected (G := G) k w decomposition.left :=
  everyForkConnected_of_geometry hcubic k w decomposition.left
    decomposition.leftGeometry decomposition.left_leafList_nodup
    decomposition.rootEdge decomposition.leftOutsideEdge
    decomposition.rootEdge_ne_leftOutsideEdge
    decomposition.rootEdge_not_mem_left_shore
    decomposition.leftOutsideEdge_not_mem_left_shore

/-- The full connected-cut condition on the second tree is generated from
the supplied geometry, rather than assumed. -/
noncomputable def rightConnected {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    EveryForkConnected (G := G) k w decomposition.right :=
  everyForkConnected_of_geometry hcubic k w decomposition.right
    decomposition.rightGeometry decomposition.right_leafList_nodup
    decomposition.rootEdge decomposition.rightOutsideEdge
    decomposition.rootEdge_ne_rightOutsideEdge
    decomposition.rootEdge_not_mem_right_shore
    decomposition.rightOutsideEdge_not_mem_right_shore

/-- The first nondegenerate rooted shore tree. -/
noncomputable def leftTree {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    DecompTree (ConnectedShoreNode (G := G) k w) :=
  toConnectedShoreTree k w decomposition.left
    (decomposition.leftConnected hcubic)

/-- The second nondegenerate rooted shore tree. -/
noncomputable def rightTree {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    DecompTree (ConnectedShoreNode (G := G) k w) :=
  toConnectedShoreTree k w decomposition.right
    (decomposition.rightConnected hcubic)

theorem strict_leftTree {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    StrictConnectedShoreTree (decomposition.leftTree hcubic) :=
  strict_toConnectedShoreTree k w decomposition.left
    (decomposition.leftConnected hcubic) decomposition.left_leafList_nodup

theorem strict_rightTree {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    StrictConnectedShoreTree (decomposition.rightTree hcubic) :=
  strict_toConnectedShoreTree k w decomposition.right
    (decomposition.rightConnected hcubic) decomposition.right_leafList_nodup

@[simp] theorem nodeCount_leftTree {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    nodeCount (decomposition.leftTree hcubic) = decomposition.left.forkCount :=
  nodeCount_toConnectedShoreTree k w decomposition.left
    (decomposition.leftConnected hcubic)

@[simp] theorem nodeCount_rightTree {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3) :
    nodeCount (decomposition.rightTree hcubic) = decomposition.right.forkCount :=
  nodeCount_toConnectedShoreTree k w decomposition.right
    (decomposition.rightConnected hcubic)

/-- A full duplicate-free edge-leaf labelling has exactly three more leaves
than the total number of retained internal nodes: one distinguished root
leaf and one terminal leaf in each of the two rooted trees. -/
theorem card_edges_eq_forkCounts_add_three {k w : Nat}
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    Fintype.card G.edgeSet =
      decomposition.left.forkCount + decomposition.right.forkCount + 3 := by
  have hcard := List.toFinset_card_of_nodup decomposition.leavesNodup
  rw [decomposition.leavesCover, Finset.card_univ] at hcard
  have hlength :
      Fintype.card G.edgeSet =
        (decomposition.rootEdge ::
          (decomposition.left.leafList ++
            decomposition.right.leafList)).length := hcard
  rw [List.length_cons, List.length_append,
    decomposition.left.leafList_length_eq_forkCount_add_one,
    decomposition.right.leafList_length_eq_forkCount_add_one] at hlength
  omega

end RootedConnectedBranchDecomposition

/-- **Bounded-width descent from a genuine edge-leaf decomposition.**
The one-edge top cut is discarded, its two children are pumped separately,
and cubic incidence converts their complete edge-leaf accounting into the
vertex bound.  If `B` is the raw one-tree bound, the honest two-tree bound is
`4B+6`; no invalid root interface is inserted to obtain a prettier constant. -/
theorem vertexCount_le_of_rootedConnectedBranchDecomposition
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (k w : Nat)
    (decomposition : RootedConnectedBranchDecomposition (G := G) k w) :
    Fintype.card V ≤
      4 * (2 ^ ((6 * w + 1) *
        (∑ j : Fin (k + 1),
          Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))) - 1) + 6 := by
  let bound : Nat :=
    2 ^ ((6 * w + 1) *
      (∑ j : Fin (k + 1),
        Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))) - 1
  let hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation minimal.spherical.cubic
  have hleft : decomposition.left.forkCount ≤ bound := by
    rw [← decomposition.nodeCount_leftTree hcubic]
    simpa [bound] using nodeCount_le_of_connectedShoreTree
      rotation minimal k w (decomposition.leftTree hcubic)
      (decomposition.strict_leftTree hcubic)
  have hright : decomposition.right.forkCount ≤ bound := by
    rw [← decomposition.nodeCount_rightTree hcubic]
    simpa [bound] using nodeCount_le_of_connectedShoreTree
      rotation minimal k w (decomposition.rightTree hcubic)
      (decomposition.strict_rightTree hcubic)
  have hthree :=
    rotation.toRotationSystem.card_darts_eq_three_times_card_vertices
      minimal.spherical.cubic
  have htwo := rotation.toRotationSystem.card_darts_eq_twice_card_edges
  have hcubic : 3 * Fintype.card V = 2 * Fintype.card G.edgeSet :=
    hthree.symm.trans htwo
  have hedges := decomposition.card_edges_eq_forkCounts_add_three
  change Fintype.card V ≤ 4 * bound + 6
  omega

end

end GoertzelV24ConnectedBranchDecompositionForest

end Mettapedia.GraphTheory.FourColor
