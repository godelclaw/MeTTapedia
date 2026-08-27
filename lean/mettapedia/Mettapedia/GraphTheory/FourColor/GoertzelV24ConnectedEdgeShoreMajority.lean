import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphereCutMaterial
import Mettapedia.GraphTheory.FourColor.IncidentEdgeFinset

/-!
# Majority vertex shores from connected edge shores

A branch decomposition partitions edges, while the literal open-tangle
constructor cuts vertices.  In a cubic graph there is a canonical conversion:
retain a vertex on the `A` side exactly when at least two of its three incident
edges lie in `A`.

This file proves the finite local facts behind that conversion.  The
construction is complementary and monotone, its vertex cut is no wider than
the branch-decomposition middle set, and strict edge material becomes strict
vertex material.  Connectivity of majority shores is proved below from an
explicit connected-edge-shore witness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedEdgeShoreMajority

open SimpleGraph
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24SphereCutMaterial

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  [Fintype G.edgeSet]

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- Edges of one shore incident with a vertex. -/
def shoreIncidentEdges (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) (vertex : V) : Finset G.edgeSet :=
  (incidentEdgeFinset G vertex).filter fun edge => edge ∈ shore

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
@[simp]
theorem mem_shoreIncidentEdges_iff (shore : Finset G.edgeSet)
    (vertex : V) (edge : G.edgeSet) :
    edge ∈ shoreIncidentEdges G shore vertex ↔
      vertex ∈ (edge : Sym2 V) ∧ edge ∈ shore := by
  simp [shoreIncidentEdges, incidentEdgeFinset]

/-- The canonical vertex shore associated with an edge shore in a cubic
graph: a vertex follows the majority of its three incident edges. -/
def majorityVertexSide (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) (vertex : V) : Prop :=
  2 ≤ (shoreIncidentEdges G shore vertex).card

/-- The usual middle set of an edge shore: vertices seeing an edge on both
sides of the edge partition. -/
abbrev edgeShoreMiddleVertices (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) : Finset V :=
  middleVertices
    (fun vertex (edge : G.edgeSet) => vertex ∈ (edge : Sym2 V)) shore

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- The incident edge counts on complementary shores add to the degree. -/
theorem card_shoreIncidentEdges_add_complement
    (shore : Finset G.edgeSet) (vertex : V) :
    (shoreIncidentEdges G shore vertex).card +
        (shoreIncidentEdges G (Finset.univ \ shore) vertex).card =
      (incidentEdgeFinset G vertex).card := by
  classical
  simpa [shoreIncidentEdges] using
    (Finset.card_filter_add_card_filter_not
      (s := incidentEdgeFinset G vertex) (p := fun edge => edge ∈ shore))

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- In degree three, taking the complementary edge shore negates the
majority vertex side. -/
theorem majorityVertexSide_complement_iff
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (shore : Finset G.edgeSet) (vertex : V) :
    majorityVertexSide G (Finset.univ \ shore) vertex ↔
      ¬ majorityVertexSide G shore vertex := by
  have hsum := card_shoreIncidentEdges_add_complement
    (G := G) shore vertex
  rw [hcubic vertex] at hsum
  simp only [majorityVertexSide]
  omega

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- Enlarging an edge shore can only enlarge its majority vertex shore. -/
theorem majorityVertexSide_mono {A B : Finset G.edgeSet}
    (hAB : A ⊆ B) {vertex : V}
    (hvertex : majorityVertexSide G A vertex) :
    majorityVertexSide G B vertex := by
  apply le_trans hvertex
  apply Finset.card_le_card
  intro edge hedge
  rw [mem_shoreIncidentEdges_iff] at hedge ⊢
  exact ⟨hedge.1, hAB hedge.2⟩

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- A vertex all of whose incident edges lie in a nested edge slab is
strictly between the two associated majority shores. -/
theorem strict_majority_material_of_incident_sdiff
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    {A B : Finset G.edgeSet} {vertex : V}
    (hall : ∀ edge ∈ incidentEdgeFinset G vertex, edge ∈ B \ A) :
    majorityVertexSide G B vertex ∧ ¬ majorityVertexSide G A vertex := by
  have hB : shoreIncidentEdges G B vertex = incidentEdgeFinset G vertex := by
    apply Finset.filter_eq_self.2
    intro edge hedge
    exact (Finset.mem_sdiff.1 (hall edge hedge)).1
  have hA : shoreIncidentEdges G A vertex = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro edge hedgeInc hedgeA
    exact (Finset.mem_sdiff.1 (hall edge hedgeInc)).2 hedgeA
  constructor
  · simp [majorityVertexSide, hB, hcubic vertex]
  · simp [majorityVertexSide, hA]

/-- Every crossing edge of the majority vertex shore can be charged
injectively to one middle vertex of the original edge shore. -/
theorem card_crossingSideDart_majority_le_middle
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (shore : Finset G.edgeSet) :
    Fintype.card (CrossingSideDart G (majorityVertexSide G shore)) ≤
      (edgeShoreMiddleVertices G shore).card := by
  classical
  let side : V → Prop := majorityVertexSide G shore
  let edgeOf : CrossingSideDart G side → G.edgeSet := fun dart =>
    ⟨dart.1.edge, dart.1.edge_mem⟩
  let chargedVertex : CrossingSideDart G side → V := fun dart =>
    if edgeOf dart ∈ shore then dart.1.snd else dart.1.fst
  have hedge_vertex_fst (dart : CrossingSideDart G side) :
      dart.1.fst ∈ (edgeOf dart : Sym2 V) := by
    simp [edgeOf, SimpleGraph.Dart.edge]
  have hedge_vertex_snd (dart : CrossingSideDart G side) :
      dart.1.snd ∈ (edgeOf dart : Sym2 V) := by
    simp [edgeOf, SimpleGraph.Dart.edge]
  have hcharged (dart : CrossingSideDart G side) :
      chargedVertex dart ∈ edgeShoreMiddleVertices G shore := by
    by_cases hedge : edgeOf dart ∈ shore
    · have hout : ¬ majorityVertexSide G shore dart.1.snd := dart.2.2
      have hsmall : (shoreIncidentEdges G shore dart.1.snd).card ≤ 1 := by
        simp only [majorityVertexSide] at hout
        omega
      have hsum := card_shoreIncidentEdges_add_complement
        (G := G) shore dart.1.snd
      rw [hcubic dart.1.snd] at hsum
      have hcompPos : 0 <
          (shoreIncidentEdges G (Finset.univ \ shore) dart.1.snd).card := by
        omega
      obtain ⟨other, hother⟩ := Finset.card_pos.mp hcompPos
      rw [mem_middleVertices_iff]
      refine ⟨⟨edgeOf dart, hedge, ?_⟩, ⟨other, ?_, ?_⟩⟩
      · simpa [chargedVertex, hedge] using hedge_vertex_snd dart
      · rw [mem_shoreIncidentEdges_iff] at hother
        exact (Finset.mem_sdiff.1 hother.2).2
      · rw [mem_shoreIncidentEdges_iff] at hother
        simpa [chargedVertex, hedge, incidentEdgeFinset] using hother.1
    · have hin : majorityVertexSide G shore dart.1.fst := dart.2.1
      have hpos : 0 < (shoreIncidentEdges G shore dart.1.fst).card :=
        lt_of_lt_of_le (by decide) hin
      obtain ⟨other, hother⟩ := Finset.card_pos.mp hpos
      rw [mem_middleVertices_iff]
      refine ⟨⟨other, ?_, ?_⟩, ⟨edgeOf dart, hedge, ?_⟩⟩
      · rw [mem_shoreIncidentEdges_iff] at hother
        exact hother.2
      · rw [mem_shoreIncidentEdges_iff] at hother
        simpa [chargedVertex, hedge, incidentEdgeFinset] using hother.1
      · simpa [chargedVertex, hedge] using hedge_vertex_fst dart
  let toMiddle : CrossingSideDart G side →
      {vertex // vertex ∈ edgeShoreMiddleVertices G shore} :=
    fun dart => ⟨chargedVertex dart, hcharged dart⟩
  have hinjective : Function.Injective toMiddle := by
    intro left right heq
    have hvertex : chargedVertex left = chargedVertex right :=
      congrArg Subtype.val heq
    by_cases hleft : edgeOf left ∈ shore <;>
      by_cases hright : edgeOf right ∈ shore
    · have houtside : ¬ majorityVertexSide G shore left.1.snd := left.2.2
      have hcard : (shoreIncidentEdges G shore left.1.snd).card ≤ 1 := by
        simp only [majorityVertexSide] at houtside
        omega
      apply crossingSideDart_edge_injective side
      apply Finset.card_le_one_iff.mp hcard
      · rw [mem_shoreIncidentEdges_iff]
        exact ⟨by simpa [chargedVertex, hleft, hright] using hedge_vertex_snd left,
          hleft⟩
      · rw [mem_shoreIncidentEdges_iff]
        exact ⟨by
          have : left.1.snd = right.1.snd := by
            simpa [chargedVertex, hleft, hright] using hvertex
          simpa [this] using hedge_vertex_snd right,
          hright⟩
    · exfalso
      have : left.1.snd = right.1.fst := by
        simpa [chargedVertex, hleft, hright] using hvertex
      exact left.2.2 (this ▸ right.2.1)
    · exfalso
      have : left.1.fst = right.1.snd := by
        simpa [chargedVertex, hleft, hright] using hvertex
      exact right.2.2 (this ▸ left.2.1)
    · have hin : majorityVertexSide G shore left.1.fst := left.2.1
      have hsum := card_shoreIncidentEdges_add_complement
        (G := G) shore left.1.fst
      rw [hcubic left.1.fst] at hsum
      have hcard :
          (shoreIncidentEdges G (Finset.univ \ shore) left.1.fst).card ≤ 1 := by
        simp only [majorityVertexSide] at hin
        omega
      apply crossingSideDart_edge_injective side
      apply Finset.card_le_one_iff.mp hcard
      · rw [mem_shoreIncidentEdges_iff]
        exact ⟨hedge_vertex_fst left,
          Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hleft⟩⟩
      · rw [mem_shoreIncidentEdges_iff]
        have hfst : left.1.fst = right.1.fst := by
          simpa [chargedVertex, hleft, hright] using hvertex
        exact ⟨by simpa [hfst] using hedge_vertex_fst right,
          Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hright⟩⟩
  calc
    Fintype.card (CrossingSideDart G (majorityVertexSide G shore)) =
        Fintype.card (CrossingSideDart G side) := by rfl
    _ ≤ Fintype.card
        {vertex // vertex ∈ edgeShoreMiddleVertices G shore} :=
      Fintype.card_le_of_injective toMiddle hinjective
    _ = (edgeShoreMiddleVertices G shore).card :=
      Fintype.card_coe _

/-- Connectivity of an edge shore after isolated vertices are discarded,
stated directly in the walk form consumed by the majority-shore proof. -/
def EdgeShoreConnected (G : SimpleGraph V) [Fintype G.edgeSet]
    (shore : Finset G.edgeSet) : Prop :=
  ∀ ⦃u v : V⦄,
    (∃ edge ∈ shore, u ∈ (edge : Sym2 V)) →
    (∃ edge ∈ shore, v ∈ (edge : Sym2 V)) →
    ∃ walk : G.Walk u v,
      ∀ edge : G.edgeSet, (edge : Sym2 V) ∈ walk.edges → edge ∈ shore

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- A majority vertex is in the endpoint support of its edge shore. -/
theorem exists_shore_edge_incident_of_majority
    {shore : Finset G.edgeSet} {vertex : V}
    (hvertex : majorityVertexSide G shore vertex) :
    ∃ edge ∈ shore, vertex ∈ (edge : Sym2 V) := by
  have hpos : 0 < (shoreIncidentEdges G shore vertex).card :=
    lt_of_lt_of_le (by decide) hvertex
  obtain ⟨edge, hedge⟩ := Finset.card_pos.mp hpos
  rw [mem_shoreIncidentEdges_iff] at hedge
  exact ⟨edge, hedge.2, hedge.1⟩

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- Every vertex of a simple path between majority vertices, all of whose
edges lie in the shore, is again a majority vertex. -/
theorem majority_of_mem_path_support
    {shore : Finset G.edgeSet} {u v x : V}
    (path : G.Path u v)
    (hedges : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ (path : G.Walk u v).edges → edge ∈ shore)
    (hu : majorityVertexSide G shore u)
    (hv : majorityVertexSide G shore v)
    (hx : x ∈ (path : G.Walk u v).support) :
    majorityVertexSide G shore x := by
  let walk : G.Walk u v := path
  obtain ⟨index, hindex, hindexLe⟩ :=
    Walk.mem_support_iff_exists_getVert.mp hx
  subst x
  change majorityVertexSide G shore (walk.getVert index)
  by_cases hzero : index = 0
  · simpa [walk, hzero] using hu
  by_cases hend : index = walk.length
  · simpa [hend] using hv
  have hindexPos : 0 < index := Nat.pos_of_ne_zero hzero
  have hindexLt : index < walk.length := lt_of_le_of_ne hindexLe hend
  have hprevIndex : index - 1 < walk.length := by omega
  have hprevSucc : index - 1 + 1 = index := by omega
  have hprevAdj : G.Adj (walk.getVert (index - 1)) (walk.getVert index) := by
    simpa [hprevSucc] using walk.adj_getVert_succ hprevIndex
  have hnextAdj : G.Adj (walk.getVert index) (walk.getVert (index + 1)) :=
    walk.adj_getVert_succ hindexLt
  let previousEdge : G.edgeSet :=
    ⟨s(walk.getVert (index - 1), walk.getVert index),
      (G.mem_edgeSet).2 hprevAdj⟩
  let nextEdge : G.edgeSet :=
    ⟨s(walk.getVert index, walk.getVert (index + 1)),
      (G.mem_edgeSet).2 hnextAdj⟩
  have hpreviousPath : (previousEdge : Sym2 V) ∈ walk.edges := by
    rw [← Walk.adj_toSubgraph_iff_mem_edges]
    simpa [previousEdge, hprevSucc] using
      walk.toSubgraph_adj_getVert hprevIndex
  have hnextPath : (nextEdge : Sym2 V) ∈ walk.edges := by
    rw [← Walk.adj_toSubgraph_iff_mem_edges]
    simpa [nextEdge] using walk.toSubgraph_adj_getVert hindexLt
  have hpreviousShore : previousEdge ∈ shore := hedges previousEdge hpreviousPath
  have hnextShore : nextEdge ∈ shore := hedges nextEdge hnextPath
  have hpreviousIncident :
      previousEdge ∈ shoreIncidentEdges G shore (walk.getVert index) := by
    rw [mem_shoreIncidentEdges_iff]
    exact ⟨by simp [previousEdge], hpreviousShore⟩
  have hnextIncident :
      nextEdge ∈ shoreIncidentEdges G shore (walk.getVert index) := by
    rw [mem_shoreIncidentEdges_iff]
    exact ⟨by simp [nextEdge], hnextShore⟩
  have hedgesNe : previousEdge ≠ nextEdge := by
    intro heq
    have hsymm :
        s(walk.getVert (index - 1), walk.getVert index) =
          s(walk.getVert index, walk.getVert (index + 1)) :=
      congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp hsymm with hstraight | hswap
    · exact hprevAdj.ne hstraight.1
    · have hvertices :
          walk.getVert (index - 1) = walk.getVert (index + 1) := hswap.1
      have hindices := path.2.getVert_injOn
        (show index - 1 ≤ walk.length by omega)
        (show index + 1 ≤ walk.length by omega) hvertices
      omega
  have hpairSubset : ({previousEdge, nextEdge} : Finset G.edgeSet) ⊆
      shoreIncidentEdges G shore (walk.getVert index) := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact hpreviousIncident
    · exact hnextIncident
  have hpairCard : ({previousEdge, nextEdge} : Finset G.edgeSet).card = 2 := by
    simp [hedgesNe]
  unfold majorityVertexSide
  rw [← hpairCard]
  exact Finset.card_le_card hpairSubset

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- A connected edge shore with a nonempty majority core induces a connected
literal vertex shore. -/
theorem connected_induce_majorityVertexSide
    (shore : Finset G.edgeSet)
    (hconnected : EdgeShoreConnected G shore)
    (hnonempty : ∃ vertex, majorityVertexSide G shore vertex) :
    (G.induce {vertex | majorityVertexSide G shore vertex}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨root, hroot⟩ := hnonempty
  refine ⟨⟨root, hroot⟩, ?_⟩
  rintro ⟨vertex, hvertex⟩
  obtain ⟨walk, hwalkEdges⟩ := hconnected
    (exists_shore_edge_incident_of_majority hroot)
    (exists_shore_edge_incident_of_majority hvertex)
  let path : G.Path root vertex := walk.toPath
  have hpathEdges : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ (path : G.Walk root vertex).edges → edge ∈ shore := by
    intro edge hedge
    apply hwalkEdges edge
    exact walk.edges_toPath_subset_edges hedge
  have hsupport : ∀ x ∈ (path : G.Walk root vertex).support,
      majorityVertexSide G shore x := by
    intro x hx
    exact majority_of_mem_path_support path hpathEdges hroot hvertex hx
  exact ⟨(path : G.Walk root vertex).induce
    {vertex | majorityVertexSide G shore vertex} hsupport⟩

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- Connectedness of the complementary edge shore gives connectedness of
the literal complement of the majority vertex shore. -/
theorem connected_induce_not_majorityVertexSide
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (shore : Finset G.edgeSet)
    (hconnected : EdgeShoreConnected G (Finset.univ \ shore))
    (hnonempty : ∃ vertex, ¬ majorityVertexSide G shore vertex) :
    (G.induce {vertex | ¬ majorityVertexSide G shore vertex}).Connected := by
  have hnonemptyComplement :
      ∃ vertex, majorityVertexSide G (Finset.univ \ shore) vertex := by
    obtain ⟨vertex, hvertex⟩ := hnonempty
    exact ⟨vertex,
      (majorityVertexSide_complement_iff hcubic shore vertex).2 hvertex⟩
  have hconnectedComplement := connected_induce_majorityVertexSide
    (G := G) (Finset.univ \ shore) hconnected hnonemptyComplement
  have hset :
      {vertex | majorityVertexSide G (Finset.univ \ shore) vertex} =
        {vertex | ¬ majorityVertexSide G shore vertex} := by
    ext vertex
    exact majorityVertexSide_complement_iff hcubic shore vertex
  rw [hset] at hconnectedComplement
  exact hconnectedComplement

/-- The complete graph-local adapter consumed by the planar-bond seam
construction: connected complementary vertex shores and the original
branch-width bound on their literal edge interface. -/
theorem connected_majority_shores_and_width
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (shore : Finset G.edgeSet)
    (hconnected : EdgeShoreConnected G shore)
    (hconnectedComplement : EdgeShoreConnected G (Finset.univ \ shore))
    (hnonempty : ∃ vertex, majorityVertexSide G shore vertex)
    (hnonemptyComplement : ∃ vertex, ¬ majorityVertexSide G shore vertex) :
    (G.induce {vertex | majorityVertexSide G shore vertex}).Connected ∧
      (G.induce {vertex | ¬ majorityVertexSide G shore vertex}).Connected ∧
      Fintype.card
          (CrossingSideDart G (majorityVertexSide G shore)) ≤
        (edgeShoreMiddleVertices G shore).card := by
  exact ⟨connected_induce_majorityVertexSide shore hconnected hnonempty,
    connected_induce_not_majorityVertexSide hcubic shore
      hconnectedComplement hnonemptyComplement,
    card_crossingSideDart_majority_le_middle hcubic shore⟩

end

end GoertzelV24ConnectedEdgeShoreMajority

end Mettapedia.GraphTheory.FourColor
