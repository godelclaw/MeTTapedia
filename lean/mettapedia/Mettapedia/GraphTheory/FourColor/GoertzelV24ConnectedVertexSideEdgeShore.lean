import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedEdgeShoreMajority

/-!
# Edge shores from connected vertex sides

A literal separator first produces connected vertex sides, whereas the
finite-state descent is indexed by a partition of the ambient edge set.  This
file gives the canonical monotone conversion used by corridor prefixes: put
every edge meeting the chosen vertex side into its edge shore.  The
complementary edge shore then consists exactly of the edges internal to the
opposite vertex side.

No planarity or colouring hypothesis is used.  The proof constructs the
required shore walks explicitly from a walk in the relevant induced graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedVertexSideEdgeShore

open SimpleGraph
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24SphereCutMaterial

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every edge with at least one endpoint on `side`.  Assigning boundary
edges to `side` in this way is monotone in the vertex predicate. -/
def incidentEdgeShore (G : SimpleGraph V) [Fintype G.edgeSet]
    (side : V → Prop) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun edge => ∃ vertex, vertex ∈ (edge : Sym2 V) ∧ side vertex

@[simp]
theorem mem_incidentEdgeShore_iff
    (side : V → Prop) (edge : G.edgeSet) :
    edge ∈ incidentEdgeShore G side ↔
      ∃ vertex, vertex ∈ (edge : Sym2 V) ∧ side vertex := by
  simp [incidentEdgeShore]

/-! ## Boundary width of an incident-edge shore -/

/-- For the monotone incident-edge shore of a vertex side, a middle vertex
lies outside the side and is the outer endpoint of a canonically chosen
crossing dart. -/
private noncomputable def middleVertexCrossingDart
    (side : V → Prop)
    (vertex : {vertex // vertex ∈
      edgeShoreMiddleVertices G (incidentEdgeShore G side)}) :
    GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side := by
  classical
  have hmiddle :=
    (mem_middleVertices_iff
      (fun vertex (edge : G.edgeSet) => vertex ∈ (edge : Sym2 V))
      (incidentEdgeShore G side) vertex.1).1 vertex.2
  let shoreEdge : G.edgeSet := Classical.choose hmiddle.1
  have hshoreEdge : shoreEdge ∈ incidentEdgeShore G side :=
    (Classical.choose_spec hmiddle.1).1
  have hvertexEdge : vertex.1 ∈ (shoreEdge : Sym2 V) :=
    (Classical.choose_spec hmiddle.1).2
  let outsideEdge : G.edgeSet := Classical.choose hmiddle.2
  have houtsideEdge : outsideEdge ∉ incidentEdgeShore G side :=
    (Classical.choose_spec hmiddle.2).1
  have hvertexOutsideEdge : vertex.1 ∈ (outsideEdge : Sym2 V) :=
    (Classical.choose_spec hmiddle.2).2
  have hvertexOutside : ¬ side vertex.1 := by
    intro hvertexSide
    exact houtsideEdge ((mem_incidentEdgeShore_iff side outsideEdge).2
      ⟨vertex.1, hvertexOutsideEdge, hvertexSide⟩)
  let inside : V := Classical.choose
    ((mem_incidentEdgeShore_iff side shoreEdge).1 hshoreEdge)
  have hinsideSpec := Classical.choose_spec
    ((mem_incidentEdgeShore_iff side shoreEdge).1 hshoreEdge)
  have hinsideEdge : inside ∈ (shoreEdge : Sym2 V) := hinsideSpec.1
  have hinside : side inside := hinsideSpec.2
  have hne : inside ≠ vertex.1 := by
    intro heq
    exact hvertexOutside (heq ▸ hinside)
  have hedge : (shoreEdge : Sym2 V) = s(inside, vertex.1) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge hvertexEdge hne
  have hadj : G.Adj inside vertex.1 :=
    (SimpleGraph.mem_edgeSet G).1 (by simpa [hedge] using shoreEdge.property)
  exact ⟨⟨⟨inside, vertex.1⟩, hadj⟩, hinside, hvertexOutside⟩

/-- Distinct middle vertices give distinct chosen crossing darts because the
terminal endpoint of the chosen dart is the original middle vertex. -/
private theorem middleVertexCrossingDart_injective (side : V → Prop) :
    Function.Injective (middleVertexCrossingDart (G := G) side) := by
  intro left right heq
  apply Subtype.ext
  have hsnd := congrArg
    (fun dart : GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side =>
      dart.1.snd) heq
  simpa [middleVertexCrossingDart] using hsnd

/-- The middle set of the monotone edge shore associated to a vertex side
has at most one vertex per outgoing crossing dart.  This is graph-theoretic:
it uses neither an embedding nor a chosen noose. -/
theorem card_middle_incidentEdgeShore_le_crossingSideDart
    [G.LocallyFinite] (side : V → Prop) :
    (edgeShoreMiddleVertices G (incidentEdgeShore G side)).card ≤
      Fintype.card
        (GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side) := by
  calc
    (edgeShoreMiddleVertices G (incidentEdgeShore G side)).card =
        Fintype.card {vertex // vertex ∈
          edgeShoreMiddleVertices G (incidentEdgeShore G side)} := by
      symm
      exact Fintype.card_coe _
    _ ≤ Fintype.card
        (GoertzelV24CubicSmallBoundaryCycle.CrossingSideDart G side) :=
      Fintype.card_le_of_injective
        (middleVertexCrossingDart (G := G) side)
        (middleVertexCrossingDart_injective (G := G) side)

/-- Enlarging the vertex side enlarges its incident-edge shore. -/
theorem incidentEdgeShore_mono {first second : V → Prop}
    (hsubset : ∀ vertex, first vertex → second vertex) :
    incidentEdgeShore G first ⊆ incidentEdgeShore G second := by
  intro edge hedge
  rcases (mem_incidentEdgeShore_iff first edge).1 hedge with
    ⟨vertex, hvertexEdge, hvertex⟩
  exact (mem_incidentEdgeShore_iff second edge).2
    ⟨vertex, hvertexEdge, hsubset vertex hvertex⟩

/-- Every vertex on the chosen side is a majority vertex of its incident-edge
shore in a cubic graph: all three of its incident edges were assigned to that
shore. -/
theorem majorityVertexSide_incidentEdgeShore_of_side
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : V → Prop) {vertex : V} (hvertex : side vertex) :
    majorityVertexSide G (incidentEdgeShore G side) vertex := by
  have hincident :
      shoreIncidentEdges G (incidentEdgeShore G side) vertex =
        incidentEdgeFinset G vertex := by
    ext edge
    rw [mem_shoreIncidentEdges_iff]
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · exact fun hedge => hedge.1
    · intro hedge
      exact ⟨hedge,
        (mem_incidentEdgeShore_iff side edge).2
          ⟨vertex, hedge, hvertex⟩⟩
  unfold majorityVertexSide
  rw [hincident, hcubic vertex]
  omega

/-- Global cubicity is unnecessary for the chosen-side direction: a vertex
on the chosen side is a majority vertex as soon as it has at least two
ambient incident edges, because all of those edges enter the incident-edge
shore. -/
theorem majorityVertexSide_incidentEdgeShore_of_side_of_two_le_degree
    (side : V → Prop) {vertex : V} (hvertex : side vertex)
    (hdegree : 2 ≤ (incidentEdgeFinset G vertex).card) :
    majorityVertexSide G (incidentEdgeShore G side) vertex := by
  have hincident :
      shoreIncidentEdges G (incidentEdgeShore G side) vertex =
        incidentEdgeFinset G vertex := by
    ext edge
    rw [mem_shoreIncidentEdges_iff]
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · exact fun hedge => hedge.1
    · intro hedge
      exact ⟨hedge,
        (mem_incidentEdgeShore_iff side edge).2
          ⟨vertex, hedge, hvertex⟩⟩
  unfold majorityVertexSide
  rw [hincident]
  exact hdegree

/-- Two distinct crossing edges of a connected vertex side force some
vertex on that side to have ambient degree at least two.  If the two edges
share their side endpoint they already witness the claim; otherwise the
first edge of a path inside the connected side supplements one crossing
edge. -/
theorem exists_two_le_degree_of_connected_side_of_two_crossing_edges
    (side : V → Prop) (hconnected : (G.induce side).Connected)
    {first second : G.edgeSet} (hne : first ≠ second)
    (hfirst : EdgeCrossesVertexSide G side first)
    (hsecond : EdgeCrossesVertexSide G side second) :
    ∃ vertex, side vertex ∧ 2 ≤ (incidentEdgeFinset G vertex).card := by
  rcases hfirst with ⟨firstIn, firstOut, hfirstInEdge, _hfirstOutEdge,
    hfirstIn, hfirstOut⟩
  rcases hsecond with ⟨secondIn, secondOut, hsecondInEdge, _hsecondOutEdge,
    hsecondIn, hsecondOut⟩
  by_cases hsame : firstIn = secondIn
  · subst secondIn
    refine ⟨firstIn, hfirstIn, ?_⟩
    have hpairCard : ({first, second} : Finset G.edgeSet).card = 2 := by
      simp [hne]
    rw [← hpairCard]
    apply Finset.card_le_card
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · simpa [incidentEdgeFinset] using hfirstInEdge
    · simpa [incidentEdgeFinset] using hsecondInEdge
  · rcases hconnected ⟨firstIn, hfirstIn⟩ ⟨secondIn, hsecondIn⟩ with
      ⟨walk⟩
    have hends : (⟨firstIn, hfirstIn⟩ : {vertex // side vertex}) ≠
        ⟨secondIn, hsecondIn⟩ := by
      intro heq
      exact hsame (congrArg Subtype.val heq)
    have hnotNil : ¬ walk.Nil := walk.not_nil_of_ne hends
    let internalEdge : G.edgeSet :=
      ⟨s(firstIn, walk.snd.1), walk.adj_snd hnotNil⟩
    have hinternalIncident :
        internalEdge ∈ incidentEdgeFinset G firstIn := by
      simp [incidentEdgeFinset, internalEdge]
    have hinternalNe : internalEdge ≠ first := by
      intro heq
      have hfirstOutInternal :
          firstOut ∈ (internalEdge : Sym2 V) := by
        rw [heq]
        exact _hfirstOutEdge
      have hcases : firstOut = firstIn ∨ firstOut = walk.snd.1 := by
        simpa [internalEdge, Sym2.mem_iff] using hfirstOutInternal
      rcases hcases with hroot | hnext
      · exact hfirstOut (hroot ▸ hfirstIn)
      · exact hfirstOut (hnext ▸ walk.snd.2)
    refine ⟨firstIn, hfirstIn, ?_⟩
    have hpairCard : ({first, internalEdge} : Finset G.edgeSet).card = 2 := by
      simp [Ne.symm hinternalNe]
    rw [← hpairCard]
    apply Finset.card_le_card
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · simpa [incidentEdgeFinset] using hfirstInEdge
    · exact hinternalIncident

/-- In a cubic graph, any nonempty chosen vertex side supplies a nonempty
majority core for its incident-edge shore. -/
theorem exists_majorityVertexSide_incidentEdgeShore
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : V → Prop) (hnonempty : ∃ vertex, side vertex) :
    ∃ vertex, majorityVertexSide G (incidentEdgeShore G side) vertex := by
  rcases hnonempty with ⟨vertex, hvertex⟩
  exact ⟨vertex,
    majorityVertexSide_incidentEdgeShore_of_side hcubic side hvertex⟩

/-- If two vertices lie on one graph edge, then they coincide or are
adjacent. -/
private theorem eq_or_adj_of_mem_edge
    (edge : G.edgeSet) {left right : V}
    (hleft : left ∈ (edge : Sym2 V))
    (hright : right ∈ (edge : Sym2 V)) :
    left = right ∨ G.Adj left right := by
  by_cases heq : left = right
  · exact Or.inl heq
  · right
    have hedgeValue : (edge : Sym2 V) = s(left, right) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hleft hright heq
    exact (SimpleGraph.mem_edgeSet G).1 (by
      simpa [hedgeValue] using edge.property)

/-- Every edge of a walk supported on `side` belongs to the incident-edge
shore of `side`. -/
private theorem walk_edge_mem_incidentEdgeShore
    (side : V → Prop) {left right : V} (walk : G.Walk left right)
    (hsupport : ∀ vertex, vertex ∈ walk.support → side vertex)
    (edge : G.edgeSet) (hedge : (edge : Sym2 V) ∈ walk.edges) :
    edge ∈ incidentEdgeShore G side := by
  rcases Sym2.mk_surjective (edge : Sym2 V) with ⟨⟨first, second⟩, hvalue⟩
  have hvalue' : s(first, second) = (edge : Sym2 V) := by
    simpa using hvalue
  have hedge' : s(first, second) ∈ walk.edges := by
    rw [hvalue']
    exact hedge
  have hfirstSupport := walk.fst_mem_support_of_mem_edges hedge'
  apply (mem_incidentEdgeShore_iff side edge).2
  refine ⟨first, ?_, hsupport first hfirstSupport⟩
  rw [← hvalue']
  simp

/-- A connected induced vertex side yields a connected incident-edge shore.
Vertices just outside the side that support a boundary edge are joined to the
connected core by that edge. -/
theorem edgeShoreConnected_incidentEdgeShore
    (side : V → Prop)
    (hconnected : (G.induce side).Connected) :
    EdgeShoreConnected G (incidentEdgeShore G side) := by
  intro left right hleftIncident hrightIncident
  rcases hleftIncident with ⟨leftEdge, hleftShore, hleftEdge⟩
  rcases hrightIncident with ⟨rightEdge, hrightShore, hrightEdge⟩
  rcases (mem_incidentEdgeShore_iff side leftEdge).1 hleftShore with
    ⟨leftCore, hleftCoreEdge, hleftCore⟩
  rcases (mem_incidentEdgeShore_iff side rightEdge).1 hrightShore with
    ⟨rightCore, hrightCoreEdge, hrightCore⟩
  rcases hconnected ⟨leftCore, hleftCore⟩ ⟨rightCore, hrightCore⟩ with
    ⟨coreWalk⟩
  let inclusion : G.induce side →g G :=
    { toFun := Subtype.val
      map_rel' := fun {_ _} hadj => hadj }
  let ambientCoreWalk : G.Walk leftCore rightCore := coreWalk.map inclusion
  have hambientCoreSupport : ∀ vertex,
      vertex ∈ ambientCoreWalk.support → side vertex := by
    intro vertex hvertex
    simp only [ambientCoreWalk, SimpleGraph.Walk.support_map] at hvertex
    rcases List.mem_map.mp hvertex with ⟨sourceVertex, _hsource, hvalue⟩
    simpa [inclusion] using hvalue ▸ sourceVertex.2
  have hleftEqOrAdj :=
    eq_or_adj_of_mem_edge leftEdge hleftEdge hleftCoreEdge
  have hrightEqOrAdj :=
    eq_or_adj_of_mem_edge rightEdge hrightCoreEdge hrightEdge
  rcases hleftEqOrAdj with hleftEq | hleftAdj
  · subst leftCore
    rcases hrightEqOrAdj with hrightEq | hrightAdj
    · subst right
      refine ⟨ambientCoreWalk, ?_⟩
      intro edge hedge
      exact walk_edge_mem_incidentEdgeShore
        side ambientCoreWalk hambientCoreSupport edge hedge
    · let rightWalk : G.Walk rightCore right :=
        SimpleGraph.Walk.cons hrightAdj SimpleGraph.Walk.nil
      let joined := ambientCoreWalk.append rightWalk
      refine ⟨joined, ?_⟩
      intro edge hedge
      simp only [joined, SimpleGraph.Walk.edges_append, List.mem_append] at hedge
      rcases hedge with hcore | hright
      · exact walk_edge_mem_incidentEdgeShore
          side ambientCoreWalk hambientCoreSupport edge hcore
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨rightCore, ?_, hrightCore⟩
        have hedgeValue : (edge : Sym2 V) = s(rightCore, right) := by
          simpa [rightWalk] using hright
        rw [hedgeValue]
        simp
  · rcases hrightEqOrAdj with hrightEq | hrightAdj
    · subst right
      let leftWalk : G.Walk left leftCore :=
        SimpleGraph.Walk.cons hleftAdj SimpleGraph.Walk.nil
      let joined := leftWalk.append ambientCoreWalk
      refine ⟨joined, ?_⟩
      intro edge hedge
      simp only [joined, SimpleGraph.Walk.edges_append, List.mem_append] at hedge
      rcases hedge with hleft | hcore
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨leftCore, ?_, hleftCore⟩
        have hedgeValue : (edge : Sym2 V) = s(left, leftCore) := by
          simpa [leftWalk] using hleft
        rw [hedgeValue]
        simp
      · exact walk_edge_mem_incidentEdgeShore
          side ambientCoreWalk hambientCoreSupport edge hcore
    · let leftWalk : G.Walk left leftCore :=
        SimpleGraph.Walk.cons hleftAdj SimpleGraph.Walk.nil
      let rightWalk : G.Walk rightCore right :=
        SimpleGraph.Walk.cons hrightAdj SimpleGraph.Walk.nil
      let joined := leftWalk.append (ambientCoreWalk.append rightWalk)
      refine ⟨joined, ?_⟩
      intro edge hedge
      simp only [joined, SimpleGraph.Walk.edges_append, List.mem_append] at hedge
      rcases hedge with hleft | hcore | hright
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨leftCore, ?_, hleftCore⟩
        have hedgeValue : (edge : Sym2 V) = s(left, leftCore) := by
          simpa [leftWalk] using hleft
        rw [hedgeValue]
        simp
      · exact walk_edge_mem_incidentEdgeShore
          side ambientCoreWalk hambientCoreSupport edge hcore
      · apply (mem_incidentEdgeShore_iff side edge).2
        refine ⟨rightCore, ?_, hrightCore⟩
        have hedgeValue : (edge : Sym2 V) = s(rightCore, right) := by
          simpa [rightWalk] using hright
        rw [hedgeValue]
        simp

/-- An edge is outside the incident shore precisely when neither endpoint is
on the chosen side. -/
theorem mem_complement_incidentEdgeShore_iff
    (side : V → Prop) (edge : G.edgeSet) :
    edge ∈ Finset.univ \ incidentEdgeShore G side ↔
      ∀ vertex, vertex ∈ (edge : Sym2 V) → ¬ side vertex := by
  rw [Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and, mem_incidentEdgeShore_iff]
  push Not
  rfl

/-- A cycle wholly in the opposite vertex side supplies a majority vertex
for the complementary edge shore.  At the root of the cycle, its first and
last edges are distinct internal opposite-side edges. -/
theorem exists_majorityVertexSide_complement_incidentEdgeShore_of_cycle
    (side : V → Prop)
    (hcycle : HasCycleOnSide G (fun vertex => ¬ side vertex)) :
    ∃ vertex,
      majorityVertexSide G
        (Finset.univ \ incidentEdgeShore G side) vertex := by
  rcases hcycle with ⟨root, hroot, walk, hwalkCycle, hwalkSide⟩
  cases walk with
  | nil => exact (hwalkCycle.not_nil SimpleGraph.Walk.nil_nil).elim
  | cons hadj tail =>
      have htailNotNil : ¬ tail.Nil :=
        SimpleGraph.Walk.not_nil_of_isCycle_cons hwalkCycle
      have hfirstNotTail : s(root, tail.getVert 0) ∉ tail.edges := by
        simpa using
          ((SimpleGraph.Walk.cons_isCycle_iff tail hadj).1 hwalkCycle).2
      have hlastMem : s(tail.penultimate, root) ∈ tail.edges :=
        tail.mk_penultimate_end_mem_edges htailNotNil
      let firstEdge : G.edgeSet :=
        ⟨s(root, tail.getVert 0), (G.mem_edgeSet).2 (by simpa using hadj)⟩
      let lastEdge : G.edgeSet :=
        ⟨s(tail.penultimate, root),
          (G.mem_edgeSet).2 (tail.adj_penultimate htailNotNil)⟩
      have hnext : ¬ side (tail.getVert 0) := by
        apply hwalkSide (tail.getVert 0)
        simp
      have hpenultimate : ¬ side tail.penultimate := by
        apply hwalkSide tail.penultimate
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr
          (List.mem_of_mem_dropLast
            (tail.penultimate_mem_dropLast_support htailNotNil))
      have hfirstComplement :
          firstEdge ∈ Finset.univ \ incidentEdgeShore G side := by
        apply (mem_complement_incidentEdgeShore_iff side firstEdge).2
        intro vertex hvertex
        simp only [firstEdge, Sym2.mem_iff] at hvertex
        rcases hvertex with rfl | rfl
        · exact hroot
        · exact hnext
      have hlastComplement :
          lastEdge ∈ Finset.univ \ incidentEdgeShore G side := by
        apply (mem_complement_incidentEdgeShore_iff side lastEdge).2
        intro vertex hvertex
        simp only [lastEdge, Sym2.mem_iff] at hvertex
        rcases hvertex with rfl | rfl
        · exact hpenultimate
        · exact hroot
      have hedgesNe : firstEdge ≠ lastEdge := by
        intro heq
        have hvalue : s(root, tail.getVert 0) =
            s(tail.penultimate, root) :=
          congrArg Subtype.val heq
        rw [← hvalue] at hlastMem
        exact hfirstNotTail hlastMem
      have hfirstIncident :
          firstEdge ∈ shoreIncidentEdges G
            (Finset.univ \ incidentEdgeShore G side) root := by
        rw [mem_shoreIncidentEdges_iff]
        exact ⟨by simp [firstEdge], hfirstComplement⟩
      have hlastIncident :
          lastEdge ∈ shoreIncidentEdges G
            (Finset.univ \ incidentEdgeShore G side) root := by
        rw [mem_shoreIncidentEdges_iff]
        exact ⟨by simp [lastEdge], hlastComplement⟩
      have hpairSubset : ({firstEdge, lastEdge} : Finset G.edgeSet) ⊆
          shoreIncidentEdges G
            (Finset.univ \ incidentEdgeShore G side) root := by
        intro edge hedge
        simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
        rcases hedge with rfl | rfl
        · exact hfirstIncident
        · exact hlastIncident
      refine ⟨root, ?_⟩
      unfold majorityVertexSide
      have hpairCard : ({firstEdge, lastEdge} : Finset G.edgeSet).card = 2 := by
        simp [hedgesNe]
      rw [← hpairCard]
      exact Finset.card_le_card hpairSubset

/-- In a cubic graph, an opposite-side cycle therefore supplies a vertex
outside the majority core of the incident-edge shore. -/
theorem exists_not_majorityVertexSide_incidentEdgeShore_of_complement_cycle
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : V → Prop)
    (hcycle : HasCycleOnSide G (fun vertex => ¬ side vertex)) :
    ∃ vertex, ¬ majorityVertexSide G (incidentEdgeShore G side) vertex := by
  rcases
      exists_majorityVertexSide_complement_incidentEdgeShore_of_cycle
        (G := G) side hcycle with
    ⟨vertex, hvertex⟩
  exact ⟨vertex,
    (majorityVertexSide_complement_iff hcubic
      (incidentEdgeShore G side) vertex).1 hvertex⟩

/-- The opposite-cycle conclusion needs only subcubicity.  The cycle gives
two distinct incident edges in the complementary shore; if the ambient
degree is at most three, at most one incident edge remains in the chosen
shore.  This is the form appropriate to a source trail, whose two defects
have degree two and whose frozen stubs have degree one. -/
theorem exists_not_majorityVertexSide_incidentEdgeShore_of_complement_cycle_of_subcubic
    (hsubcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card ≤ 3)
    (side : V → Prop)
    (hcycle : HasCycleOnSide G (fun vertex => ¬ side vertex)) :
    ∃ vertex, ¬ majorityVertexSide G (incidentEdgeShore G side) vertex := by
  rcases
      exists_majorityVertexSide_complement_incidentEdgeShore_of_cycle
        (G := G) side hcycle with
    ⟨vertex, hcomplementMajority⟩
  refine ⟨vertex, ?_⟩
  have hsum := card_shoreIncidentEdges_add_complement
    (G := G) (incidentEdgeShore G side) vertex
  have hdegree := hsubcubic vertex
  simp only [majorityVertexSide] at hcomplementMajority ⊢
  omega

/-- If the complementary induced vertex side is connected, then the
complement of the incident-edge shore is connected.  Every edge in this
complement has both endpoints on the complementary side. -/
theorem edgeShoreConnected_complement_incidentEdgeShore
    (side : V → Prop)
    (hconnected : (G.induce (fun vertex => ¬ side vertex)).Connected) :
    EdgeShoreConnected G (Finset.univ \ incidentEdgeShore G side) := by
  intro left right hleftIncident hrightIncident
  rcases hleftIncident with ⟨leftEdge, hleftShore, hleftEdge⟩
  rcases hrightIncident with ⟨rightEdge, hrightShore, hrightEdge⟩
  have hleft : ¬ side left :=
    (mem_complement_incidentEdgeShore_iff side leftEdge).1
      hleftShore left hleftEdge
  have hright : ¬ side right :=
    (mem_complement_incidentEdgeShore_iff side rightEdge).1
      hrightShore right hrightEdge
  rcases hconnected ⟨left, hleft⟩ ⟨right, hright⟩ with ⟨insideWalk⟩
  let inclusion : G.induce (fun vertex => ¬ side vertex) →g G :=
    { toFun := Subtype.val
      map_rel' := fun {_ _} hadj => hadj }
  let walk : G.Walk left right := insideWalk.map inclusion
  refine ⟨walk, ?_⟩
  intro edge hedge
  apply (mem_complement_incidentEdgeShore_iff side edge).2
  intro vertex hvertexEdge hvertexSide
  have hvertexSupport : vertex ∈ walk.support :=
    walk.mem_support_of_mem_edges hedge hvertexEdge
  simp only [walk, SimpleGraph.Walk.support_map] at hvertexSupport
  rcases List.mem_map.mp hvertexSupport with
    ⟨sourceVertex, _hsource, hvalue⟩
  have hvalue' : sourceVertex.1 = vertex := by
    simpa [inclusion] using hvalue
  rw [← hvalue'] at hvertexSide
  exact sourceVertex.2 hvertexSide

/-- A connected vertex bipartition canonically supplies the two connected
edge shores consumed by the majority-shore splice. -/
theorem connected_edgeShores_of_connected_vertexSides
    (side : V → Prop)
    (hside : (G.induce side).Connected)
    (hcomplement : (G.induce (fun vertex => ¬ side vertex)).Connected) :
    EdgeShoreConnected G (incidentEdgeShore G side) ∧
      EdgeShoreConnected G (Finset.univ \ incidentEdgeShore G side) :=
  ⟨edgeShoreConnected_incidentEdgeShore side hside,
    edgeShoreConnected_complement_incidentEdgeShore side hcomplement⟩

/-- A connected vertex bipartition with a cycle on each side supplies every
non-root field of the literal majority-shore node: complementary connected
edge shores and nonempty majority vertex shores.  The chosen-side cycle is
used only for nonemptiness; the opposite-side cycle contributes two distinct
opposite-shore edges at its root. -/
theorem connected_edgeShores_and_nonempty_majoritySides_of_cycles
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (side : V → Prop)
    (hside : (G.induce side).Connected)
    (hcomplement : (G.induce (fun vertex => ¬ side vertex)).Connected)
    (hsideCycle : HasCycleOnSide G side)
    (hcomplementCycle : HasCycleOnSide G (fun vertex => ¬ side vertex)) :
    EdgeShoreConnected G (incidentEdgeShore G side) ∧
      EdgeShoreConnected G (Finset.univ \ incidentEdgeShore G side) ∧
      (∃ vertex, majorityVertexSide G
        (incidentEdgeShore G side) vertex) ∧
      (∃ vertex, ¬ majorityVertexSide G
        (incidentEdgeShore G side) vertex) := by
  rcases hsideCycle with ⟨root, hroot, _walk, _hcycle, _hsupport⟩
  exact ⟨edgeShoreConnected_incidentEdgeShore side hside,
    edgeShoreConnected_complement_incidentEdgeShore side hcomplement,
    exists_majorityVertexSide_incidentEdgeShore
      hcubic side ⟨root, hroot⟩,
    exists_not_majorityVertexSide_incidentEdgeShore_of_complement_cycle
      hcubic side hcomplementCycle⟩

end

end GoertzelV24ConnectedVertexSideEdgeShore

end Mettapedia.GraphTheory.FourColor
