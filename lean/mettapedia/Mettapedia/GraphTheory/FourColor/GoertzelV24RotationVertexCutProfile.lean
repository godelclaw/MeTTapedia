import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorSpliceObservables
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem
import Mettapedia.GraphTheory.FourColor.CyclicEdgeCut

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationVertexCutProfile

open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- An edge meets a finite vertex side when at least one of its two
rotation-system endpoints belongs to that side. -/
def edgeMeetsVertexSet (RS : RotationSystem V E)
    (inside : Finset V) (edge : E) : Prop :=
  ∃ vertex ∈ RS.endpoints edge, vertex ∈ inside

/-- An edge crosses a finite vertex side when it has a named endpoint inside
and a named endpoint outside. This is computed from rotation-system endpoints. -/
def edgeCrossesVertexSet (RS : RotationSystem V E)
    (inside : Finset V) (edge : E) : Prop :=
  ∃ inner ∈ RS.endpoints edge, inner ∈ inside ∧
    ∃ outer ∈ RS.endpoints edge, outer ∉ inside

/-- The regional edge set induced by a finite vertex side consists of all
edges that meet the side, including its crossing edges. -/
def vertexSetRegionEdges (RS : RotationSystem V E)
    (inside : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (edgeMeetsVertexSet RS inside)

/-- The boundary edge set induced by a finite vertex side, computed by
filtering all ambient edges through the endpoint-crossing predicate. -/
def vertexSetCrossingEdges (RS : RotationSystem V E)
    (inside : Finset V) : Finset E := by
  classical
  exact Finset.univ.filter (edgeCrossesVertexSet RS inside)

@[simp]
theorem mem_vertexSetRegionEdges_iff
    (RS : RotationSystem V E) (inside : Finset V) (edge : E) :
    edge ∈ vertexSetRegionEdges RS inside ↔ edgeMeetsVertexSet RS inside edge := by
  simp [vertexSetRegionEdges]

@[simp]
theorem mem_vertexSetCrossingEdges_iff
    (RS : RotationSystem V E) (inside : Finset V) (edge : E) :
    edge ∈ vertexSetCrossingEdges RS inside ↔
      edgeCrossesVertexSet RS inside edge := by
  simp [vertexSetCrossingEdges]

/-- Every computed crossing edge belongs to the computed regional edge set. -/
theorem vertexSetCrossingEdges_subset_regionEdges
    (RS : RotationSystem V E) (inside : Finset V) :
    vertexSetCrossingEdges RS inside ⊆ vertexSetRegionEdges RS inside := by
  intro edge hedge
  rw [mem_vertexSetCrossingEdges_iff RS] at hedge
  rw [mem_vertexSetRegionEdges_iff RS]
  rcases hedge with ⟨inner, hinnerEndpoint, hinnerInside, _⟩
  exact ⟨inner, hinnerEndpoint, hinnerInside⟩

/-- A regional edge that is not a crossing edge has both endpoints inside. -/
theorem endpoints_subset_of_mem_region_not_mem_crossing
    (RS : RotationSystem V E) (inside : Finset V) {edge : E}
    (hregion : edge ∈ vertexSetRegionEdges RS inside)
    (hnotcrossing : edge ∉ vertexSetCrossingEdges RS inside) :
    RS.endpoints edge ⊆ inside := by
  rw [mem_vertexSetRegionEdges_iff RS] at hregion
  rw [mem_vertexSetCrossingEdges_iff RS] at hnotcrossing
  rcases hregion with ⟨inner, hinnerEndpoint, hinnerInside⟩
  intro vertex hvertexEndpoint
  by_contra hvertexOutside
  exact hnotcrossing
    ⟨inner, hinnerEndpoint, hinnerInside,
      vertex, hvertexEndpoint, hvertexOutside⟩

/-- An edge outside the computed regional edge set has both endpoints outside
the chosen vertex side. -/
theorem endpoints_disjoint_of_not_mem_region
    (RS : RotationSystem V E) (inside : Finset V) {edge : E}
    (houtside : edge ∉ vertexSetRegionEdges RS inside) :
    Disjoint (RS.endpoints edge) inside := by
  rw [mem_vertexSetRegionEdges_iff RS] at houtside
  rw [Finset.disjoint_left]
  intro vertex hvertexEndpoint hvertexInside
  exact houtside ⟨vertex, hvertexEndpoint, hvertexInside⟩

/-- Crossing the chosen side is invariant under replacing it by its finite
complement. -/
theorem edgeCrossesVertexSet_compl
    (RS : RotationSystem V E) (inside : Finset V) (edge : E) :
    edgeCrossesVertexSet RS insideᶜ edge ↔
      edgeCrossesVertexSet RS inside edge := by
  constructor
  · rintro ⟨outer, houterEndpoint, houterCompl,
      inner, hinnerEndpoint, hinnerNotCompl⟩
    refine ⟨inner, hinnerEndpoint, ?_, outer, houterEndpoint, ?_⟩
    · simpa using hinnerNotCompl
    · simpa using houterCompl
  · rintro ⟨inner, hinnerEndpoint, hinnerInside,
      outer, houterEndpoint, houterOutside⟩
    refine ⟨outer, houterEndpoint, ?_, inner, hinnerEndpoint, ?_⟩
    · simpa using houterOutside
    · simpa using hinnerInside

/-- Because every rotation-system edge has exactly two distinct endpoints,
crossing a finite vertex side is equivalent to having exactly one endpoint in
that side. -/
theorem edgeCrossesVertexSet_iff_card_inter_eq_one
    (RS : RotationSystem V E) (inside : Finset V) (edge : E) :
    edgeCrossesVertexSet RS inside edge ↔
      ((RS.endpoints edge) ∩ inside).card = 1 := by
  constructor
  · rintro ⟨inner, hinnerEndpoint, hinnerInside,
      outer, houterEndpoint, houterOutside⟩
    have hnonempty : ((RS.endpoints edge) ∩ inside).Nonempty :=
      ⟨inner, Finset.mem_inter.2 ⟨hinnerEndpoint, hinnerInside⟩⟩
    have hproper : (RS.endpoints edge ∩ inside) ⊂ RS.endpoints edge := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have houterInter : outer ∈ RS.endpoints edge ∩ inside := by
        rw [heq]
        exact houterEndpoint
      exact houterOutside (Finset.mem_inter.1 houterInter).2
    have hpositive : 0 < (RS.endpoints edge ∩ inside).card :=
      Finset.card_pos.2 hnonempty
    have hlt := Finset.card_lt_card hproper
    rw [RS.endpoints_card_two edge] at hlt
    omega
  · intro hcard
    have hpositive : 0 < (RS.endpoints edge ∩ inside).card := by omega
    rcases Finset.card_pos.1 hpositive with ⟨inner, hinnerInter⟩
    have hnotSubset : ¬ RS.endpoints edge ⊆ inside := by
      intro hsubset
      have hinter : RS.endpoints edge ∩ inside = RS.endpoints edge :=
        Finset.inter_eq_left.2 hsubset
      rw [hinter, RS.endpoints_card_two edge] at hcard
      omega
    rw [Finset.not_subset] at hnotSubset
    rcases hnotSubset with ⟨outer, houterEndpoint, houterOutside⟩
    exact ⟨inner, (Finset.mem_inter.1 hinnerInter).1,
      (Finset.mem_inter.1 hinnerInter).2,
      outer, houterEndpoint, houterOutside⟩

/-- The finite type of actual crossing edges of a rotation-system vertex cut. -/
abbrev VertexSetCrossingEdge
    (RS : RotationSystem V E) (inside : Finset V) :=
  ↥(vertexSetCrossingEdges RS inside)

/-- Canonical finite enumeration of every actual crossing edge. -/
def vertexSetCrossingEdgeAt
    (RS : RotationSystem V E) (inside : Finset V)
    (index : Fin (Fintype.card (VertexSetCrossingEdge RS inside))) : E :=
  ((Fintype.equivFin (VertexSetCrossingEdge RS inside)).symm index).1

theorem vertexSetCrossingEdgeAt_mem_crossing
    (RS : RotationSystem V E) (inside : Finset V)
    (index : Fin (Fintype.card (VertexSetCrossingEdge RS inside))) :
    vertexSetCrossingEdgeAt RS inside index ∈
      vertexSetCrossingEdges RS inside :=
  ((Fintype.equivFin (VertexSetCrossingEdge RS inside)).symm index).2

theorem vertexSetCrossingEdgeAt_injective
    (RS : RotationSystem V E) (inside : Finset V) :
    Function.Injective (vertexSetCrossingEdgeAt RS inside) := by
  intro first second heq
  apply (Fintype.equivFin (VertexSetCrossingEdge RS inside)).symm.injective
  exact Subtype.ext heq

/-- The canonical enumeration is onto the computed crossing-edge set. -/
theorem exists_vertexSetCrossingEdgeAt_eq
    (RS : RotationSystem V E) (inside : Finset V) {edge : E}
    (hedge : edge ∈ vertexSetCrossingEdges RS inside) :
    ∃ index : Fin (Fintype.card (VertexSetCrossingEdge RS inside)),
      vertexSetCrossingEdgeAt RS inside index = edge := by
  let crossing : VertexSetCrossingEdge RS inside := ⟨edge, hedge⟩
  refine ⟨Fintype.equivFin (VertexSetCrossingEdge RS inside) crossing, ?_⟩
  exact congrArg Subtype.val
    ((Fintype.equivFin (VertexSetCrossingEdge RS inside)).symm_apply_apply
      crossing)

/-- The canonical crossing-port count is exactly the cardinality of the
computed crossing-edge finset. -/
theorem card_vertexSetCrossingEdge
    (RS : RotationSystem V E) (inside : Finset V) :
    Fintype.card (VertexSetCrossingEdge RS inside) =
      (vertexSetCrossingEdges RS inside).card :=
  Fintype.card_coe _

/-- The graph-derived cut data canonically extracted from a finite vertex
side. It has one crossing port for every actual crossing edge and no terminal
or face-fragment ports yet; all edge sets are computed from endpoints. -/
def vertexSetGraphCutData
    (RS : RotationSystem V E) (inside : Finset V) :
    GraphCorridorCutData RS
      (Fintype.card (VertexSetCrossingEdge RS inside)) 0 0 where
  regionEdges := vertexSetRegionEdges RS inside
  crossingEdge := vertexSetCrossingEdgeAt RS inside
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment => Fin.elim0 fragment
  fragmentEdges := fun fragment => Fin.elim0 fragment

theorem vertexSetGraphCutData_portsInRegion
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetGraphCutData RS inside).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · exact vertexSetCrossingEdges_subset_regionEdges RS inside
      (vertexSetCrossingEdgeAt_mem_crossing RS inside crossing)
  · exact Fin.elim0 terminal

theorem vertexSetGraphCutData_portsInjective
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetGraphCutData RS inside).PortsInjective := by
  intro first second heq
  rcases first with first | first
  · rcases second with second | second
    · congr 1
      exact vertexSetCrossingEdgeAt_injective RS inside heq
    · exact Fin.elim0 second
  · exact Fin.elim0 first

theorem vertexSetGraphCutData_fragmentsOnFaceInRegion
    (RS : RotationSystem V E) (inside : Finset V) :
    (vertexSetGraphCutData RS inside).FragmentsOnFaceInRegion := by
  intro fragment
  exact Fin.elim0 fragment

/-- Every computed boundary edge occurs as exactly one crossing port of the
canonically extracted graph cut. -/
theorem exists_unique_vertexSetGraphCutData_crossingEdge_eq
    (RS : RotationSystem V E) (inside : Finset V) {edge : E}
    (hedge : edge ∈ vertexSetCrossingEdges RS inside) :
    ∃! index : Fin (Fintype.card (VertexSetCrossingEdge RS inside)),
      (vertexSetGraphCutData RS inside).crossingEdge index = edge := by
  rcases exists_vertexSetCrossingEdgeAt_eq RS inside hedge with ⟨index, hindex⟩
  refine ⟨index, hindex, ?_⟩
  intro other hother
  exact vertexSetCrossingEdgeAt_injective RS inside (hother.trans hindex.symm)

section SimpleGraphBridge

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Rotation-system endpoints for a finite simple graph are exactly membership
in the underlying unordered graph edge. -/
theorem mem_simpleGraphRotationSystem_endpoints_iff
    (data : SimpleGraphDartRotation.Data G)
    (edge : G.edgeSet) (vertex : V) :
    vertex ∈ data.toRotationSystem.endpoints edge ↔
      vertex ∈ (edge : Sym2 V) := by
  rw [RotationSystem.mem_endpoints_iff]
  constructor
  · rintro ⟨dart, hdart, hvert⟩
    have hedgeSubtype :
        data.toRotationSystem.edgeOf dart = edge :=
      (data.toRotationSystem.mem_dartsOn).1 hdart
    have hedge : dart.edge = (edge : Sym2 V) :=
      congrArg Subtype.val hedgeSubtype
    change dart.fst = vertex at hvert
    have hfst : dart.fst ∈ dart.edge := by
      simp [SimpleGraph.Dart.edge]
    rw [hedge] at hfst
    simpa [hvert] using hfst
  · intro hvertex
    let other := Sym2.Mem.other' hvertex
    have hadj : G.Adj vertex other := by
      rw [← SimpleGraph.mem_edgeSet]
      rw [Sym2.other_spec' hvertex]
      exact edge.property
    let dart : G.Dart := ⟨(vertex, other), hadj⟩
    refine ⟨dart, ?_, rfl⟩
    rw [data.toRotationSystem.mem_dartsOn]
    apply Subtype.ext
    change s(vertex, other) = (edge : Sym2 V)
    exact Sym2.other_spec' hvertex

/-- The endpoint-derived crossing predicate agrees exactly with the existing
simple-graph side-cut predicate. -/
theorem simpleGraph_edgeCrossesVertexSet_iff_edgeCrossesVertexSide
    (data : SimpleGraphDartRotation.Data G)
    (inside : Finset V) (edge : G.edgeSet) :
    edgeCrossesVertexSet data.toRotationSystem inside edge ↔
      EdgeCrossesVertexSide G (fun vertex => vertex ∈ inside) edge := by
  constructor
  · rintro ⟨inner, hinnerEndpoint, hinnerInside,
      outer, houterEndpoint, houterOutside⟩
    exact ⟨inner, outer,
      (mem_simpleGraphRotationSystem_endpoints_iff data edge inner).1
        hinnerEndpoint,
      (mem_simpleGraphRotationSystem_endpoints_iff data edge outer).1
        houterEndpoint,
      hinnerInside, houterOutside⟩
  · rintro ⟨inner, outer, hinnerEndpoint, houterEndpoint,
      hinnerInside, houterOutside⟩
    exact ⟨inner,
      (mem_simpleGraphRotationSystem_endpoints_iff data edge inner).2
        hinnerEndpoint,
      hinnerInside, outer,
      (mem_simpleGraphRotationSystem_endpoints_iff data edge outer).2
        houterEndpoint,
      houterOutside⟩

/-- The computed rotation-system crossing finset is an exact simple-graph
edge-cut support, without a separately supplied boundary classification. -/
theorem mem_simpleGraph_vertexSetCrossingEdges_iff
    (data : SimpleGraphDartRotation.Data G)
    (inside : Finset V) (edge : G.edgeSet) :
    edge ∈ vertexSetCrossingEdges data.toRotationSystem inside ↔
      EdgeCrossesVertexSide G (fun vertex => vertex ∈ inside) edge := by
  rw [mem_vertexSetCrossingEdges_iff,
    simpleGraph_edgeCrossesVertexSet_iff_edgeCrossesVertexSide]

/-- If both vertex sides contain cycles, the exact computed crossing support
is cyclic-cut realization data. -/
def simpleGraph_vertexSetCyclicCutRealization
    (data : SimpleGraphDartRotation.Data G) (inside : Finset V)
    (hinsideCycle : HasCycleOnSide G (fun vertex => vertex ∈ inside))
    (houtsideCycle : HasCycleOnSide G (fun vertex => vertex ∉ inside)) :
    CyclicEdgeCutRealization G
      (vertexSetCrossingEdges data.toRotationSystem inside) where
  side := fun vertex => vertex ∈ inside
  hcut_eq := mem_simpleGraph_vertexSetCrossingEdges_iff data inside
  hinside_cycle := hinsideCycle
  houtside_cycle := houtsideCycle

/-- In cyclically five-edge-connected normal form, every finite vertex side
that contains a cycle on both sides has at least five actual crossing edges. -/
theorem five_le_card_vertexSetCrossingEdges_of_cycles
    (data : SimpleGraphDartRotation.Data G) (inside : Finset V)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hinsideCycle : HasCycleOnSide G (fun vertex => vertex ∈ inside))
    (houtsideCycle : HasCycleOnSide G (fun vertex => vertex ∉ inside)) :
    5 ≤ (vertexSetCrossingEdges data.toRotationSystem inside).card := by
  by_contra hnot
  have hcard :
      (vertexSetCrossingEdges data.toRotationSystem inside).card ≤ 4 := by
    omega
  let realization := simpleGraph_vertexSetCyclicCutRealization data inside
    hinsideCycle houtsideCycle
  exact hcyclic.noCyclicEdgeCutOfSizeAtMostFour
    ⟨realization.toSmallCyclicEdgeCut hcard, hcard⟩

/-- The same normal-form lower bound stated as the crossing-port count of the
canonically extracted graph profile. -/
theorem five_le_vertexSetGraphCutData_crossingPortCount_of_cycles
    (data : SimpleGraphDartRotation.Data G) (inside : Finset V)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hinsideCycle : HasCycleOnSide G (fun vertex => vertex ∈ inside))
    (houtsideCycle : HasCycleOnSide G (fun vertex => vertex ∉ inside)) :
    5 ≤ Fintype.card
      (VertexSetCrossingEdge data.toRotationSystem inside) := by
  rw [card_vertexSetCrossingEdge]
  exact five_le_card_vertexSetCrossingEdges_of_cycles data inside hcyclic
    hinsideCycle houtsideCycle

end SimpleGraphBridge

end

end GoertzelV24RotationVertexCutProfile

end Mettapedia.GraphTheory.FourColor
