import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairBoundary

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AdjacentPairInsertion

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace AdjacentPairData

/-- The edge joining the two vertices that will be restored. -/
def centralEdgeValue (data : AdjacentPairData G) : Sym2 V :=
  s(data.firstVertex, data.secondVertex)

/-- The four edges joining the restored pair to the retained graph, in the
same order as the four-defect boundary word. -/
def boundaryEdgeValue (data : AdjacentPairData G) (port : Fin 4) : Sym2 V :=
  if port = 0 then s(data.firstVertex, data.portVertex 0)
  else if port = 1 then s(data.firstVertex, data.portVertex 1)
  else if port = 2 then s(data.secondVertex, data.portVertex 2)
  else s(data.secondVertex, data.portVertex 3)

/-- The deleted endpoint of a boundary edge. -/
def boundaryDeletedVertex (data : AdjacentPairData G) (port : Fin 4) : V :=
  if port = 0 ∨ port = 1 then data.firstVertex else data.secondVertex

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryEdgeValue_eq
    (data : AdjacentPairData G) (port : Fin 4) :
    boundaryEdgeValue data port =
      s(boundaryDeletedVertex data port, data.portVertex port) := by
  fin_cases port <;> simp [boundaryEdgeValue, boundaryDeletedVertex]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryDeletedVertex_ne_portVertex
    (data : AdjacentPairData G) (boundaryPort otherPort : Fin 4) :
    boundaryDeletedVertex data boundaryPort ≠ data.portVertex otherPort := by
  fin_cases boundaryPort
  · simpa [boundaryDeletedVertex] using (data.portNeFirst otherPort).symm
  · simpa [boundaryDeletedVertex] using (data.portNeFirst otherPort).symm
  · simpa [boundaryDeletedVertex] using (data.portNeSecond otherPort).symm
  · simpa [boundaryDeletedVertex] using (data.portNeSecond otherPort).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem boundaryEdgeValue_zero (data : AdjacentPairData G) :
    boundaryEdgeValue data 0 =
      s(data.firstVertex, data.portVertex 0) := by
  simp [boundaryEdgeValue]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem boundaryEdgeValue_one (data : AdjacentPairData G) :
    boundaryEdgeValue data 1 =
      s(data.firstVertex, data.portVertex 1) := by
  simp [boundaryEdgeValue]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem boundaryEdgeValue_two (data : AdjacentPairData G) :
    boundaryEdgeValue data 2 =
      s(data.secondVertex, data.portVertex 2) := by
  simp [boundaryEdgeValue]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem boundaryEdgeValue_three (data : AdjacentPairData G) :
    boundaryEdgeValue data 3 =
      s(data.secondVertex, data.portVertex 3) := by
  simp [boundaryEdgeValue]

/-- The central edge as an ambient edge-set element. -/
def centralEdge (data : AdjacentPairData G) : G.edgeSet :=
  ⟨centralEdgeValue data, by
    simpa [centralEdgeValue, SimpleGraph.mem_edgeSet] using
      data.centralAdjacent⟩

/-- A boundary edge as an ambient edge-set element. -/
def boundaryEdge (data : AdjacentPairData G) (port : Fin 4) : G.edgeSet :=
  ⟨boundaryEdgeValue data port, by
    fin_cases port
    · simpa [SimpleGraph.mem_edgeSet] using data.first_adj_port_zero
    · simpa [SimpleGraph.mem_edgeSet] using data.first_adj_port_one
    · simpa [SimpleGraph.mem_edgeSet] using data.second_adj_port_two
    · simpa [SimpleGraph.mem_edgeSet] using data.second_adj_port_three⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem centralEdge_val (data : AdjacentPairData G) :
    (centralEdge data).1 = centralEdgeValue data := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem boundaryEdge_val (data : AdjacentPairData G) (port : Fin 4) :
    (boundaryEdge data port).1 = boundaryEdgeValue data port := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem portVertex_ne (data : AdjacentPairData G) {first second : Fin 4}
    (hne : first ≠ second) :
    data.portVertex first ≠ data.portVertex second := by
  intro heq
  exact hne (data.portInjective heq)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem portVertex_mem_boundaryEdgeValue
    (data : AdjacentPairData G) (port : Fin 4) :
    data.portVertex port ∈ (boundaryEdgeValue data port : Sym2 V) := by
  fin_cases port <;> simp [boundaryEdgeValue]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem centralEdgeValue_ne_boundaryEdgeValue
    (data : AdjacentPairData G) (port : Fin 4) :
    centralEdgeValue data ≠ boundaryEdgeValue data port := by
  intro heq
  fin_cases port
  · rcases Sym2.eq_iff.mp heq with hstraight | hswapped
    · exact data.portNeSecond 0 hstraight.2.symm
    · exact data.portNeFirst 0 hswapped.1.symm
  · rcases Sym2.eq_iff.mp heq with hstraight | hswapped
    · exact data.portNeSecond 1 hstraight.2.symm
    · exact data.portNeFirst 1 hswapped.1.symm
  · rcases Sym2.eq_iff.mp heq with hstraight | hswapped
    · exact data.centralAdjacent.ne hstraight.1
    · exact data.portNeFirst 2 hswapped.1.symm
  · rcases Sym2.eq_iff.mp heq with hstraight | hswapped
    · exact data.centralAdjacent.ne hstraight.1
    · exact data.portNeFirst 3 hswapped.1.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryEdgeValue_injective (data : AdjacentPairData G) :
    Function.Injective (boundaryEdgeValue data) := by
  intro first second heq
  have hmem : data.portVertex first ∈
      (boundaryEdgeValue data second : Sym2 V) := by
    rw [← heq]
    exact portVertex_mem_boundaryEdgeValue data first
  have hp : data.portVertex first = data.portVertex second := by
    fin_cases second <;>
      simpa [boundaryEdgeValue, data.portNeFirst first,
        data.portNeSecond first] using hmem
  exact data.portInjective hp

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem boundaryEdgeValue_ne (data : AdjacentPairData G)
    {first second : Fin 4} (hne : first ≠ second) :
    boundaryEdgeValue data first ≠ boundaryEdgeValue data second := by
  intro hedge
  exact hne (boundaryEdgeValue_injective data hedge)

/-- The graph embedding of the retained induced deletion into the ambient
graph. -/
def retainedGraphEmbedding (data : AdjacentPairData G) :
    DeletedAdjacentPairGraph G data.firstVertex data.secondVertex ↪g G :=
  SimpleGraph.Embedding.induce
    (retainedVertexSet data.firstVertex data.secondVertex)

/-- A retained edge of the induced deletion, regarded as an ambient edge. -/
def retainedEdgeToAmbientEdge (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) : G.edgeSet :=
  (retainedGraphEmbedding data).toHom.mapEdgeSet edge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem retainedEdgeToAmbientEdge_val (data : AdjacentPairData G)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    (retainedEdgeToAmbientEdge data edge).1 =
      edge.1.map Subtype.val := rfl

/-- An ambient edge is retained exactly when it is not one of the five edges
incident with the deleted adjacent pair. -/
def IsRetainedAmbientEdge (data : AdjacentPairData G)
    (edge : G.edgeSet) : Prop :=
  edge.1 ≠ centralEdgeValue data ∧
  edge.1 ≠ boundaryEdgeValue data 0 ∧
  edge.1 ≠ boundaryEdgeValue data 1 ∧
  edge.1 ≠ boundaryEdgeValue data 2 ∧
  edge.1 ≠ boundaryEdgeValue data 3

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isRetainedAmbientEdge_of_ne
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hcentral : edge.1 ≠ centralEdgeValue data)
    (hzero : edge.1 ≠ boundaryEdgeValue data 0)
    (hone : edge.1 ≠ boundaryEdgeValue data 1)
    (htwo : edge.1 ≠ boundaryEdgeValue data 2)
    (hthree : edge.1 ≠ boundaryEdgeValue data 3) :
    IsRetainedAmbientEdge data edge :=
  ⟨hcentral, hzero, hone, htwo, hthree⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem not_isRetainedAmbientEdge_iff
    (data : AdjacentPairData G) (edge : G.edgeSet) :
    ¬ IsRetainedAmbientEdge data edge ↔
      edge.1 = centralEdgeValue data ∨
        ∃ port : Fin 4, edge.1 = boundaryEdgeValue data port := by
  constructor
  · intro hnot
    by_cases hcentral : edge.1 = centralEdgeValue data
    · exact Or.inl hcentral
    · by_cases hzero : edge.1 = boundaryEdgeValue data 0
      · exact Or.inr ⟨0, hzero⟩
      · by_cases hone : edge.1 = boundaryEdgeValue data 1
        · exact Or.inr ⟨1, hone⟩
        · by_cases htwo : edge.1 = boundaryEdgeValue data 2
          · exact Or.inr ⟨2, htwo⟩
          · by_cases hthree : edge.1 = boundaryEdgeValue data 3
            · exact Or.inr ⟨3, hthree⟩
            · exfalso
              apply hnot
              exact ⟨hcentral, hzero, hone, htwo, hthree⟩
  · rintro (hcentral | ⟨port, hport⟩) hretained
    · exact hretained.1 hcentral
    · fin_cases port
      · exact hretained.2.1 hport
      · exact hretained.2.2.1 hport
      · exact hretained.2.2.2.1 hport
      · exact hretained.2.2.2.2 hport

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_eq_central_or_firstPort_of_mem
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hfirst : data.firstVertex ∈ (edge.1 : Sym2 V)) :
    edge.1 = s(data.firstVertex, data.secondVertex) ∨
      edge.1 = s(data.firstVertex, data.portVertex 0) ∨
      edge.1 = s(data.firstVertex, data.portVertex 1) := by
  rcases Sym2.mem_iff_exists.1 hfirst with ⟨other, hedge⟩
  have hadj : G.Adj data.firstVertex other := by
    rw [← SimpleGraph.mem_edgeSet G, ← hedge]
    exact edge.2
  have hmem : other ∈ G.neighborSet data.firstVertex := hadj
  rw [data.firstNeighbors] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact Or.inl hedge
  · exact Or.inr (Or.inl hedge)
  · exact Or.inr (Or.inr hedge)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_eq_central_or_secondPort_of_mem
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hsecond : data.secondVertex ∈ (edge.1 : Sym2 V)) :
    edge.1 = s(data.firstVertex, data.secondVertex) ∨
      edge.1 = s(data.secondVertex, data.portVertex 2) ∨
      edge.1 = s(data.secondVertex, data.portVertex 3) := by
  rcases Sym2.mem_iff_exists.1 hsecond with ⟨other, hedge⟩
  have hadj : G.Adj data.secondVertex other := by
    rw [← SimpleGraph.mem_edgeSet G, ← hedge]
    exact edge.2
  have hmem : other ∈ G.neighborSet data.secondVertex := hadj
  rw [data.secondNeighbors] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact Or.inl (hedge.trans Sym2.eq_swap)
  · exact Or.inr (Or.inl hedge)
  · exact Or.inr (Or.inr hedge)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every endpoint of a retained ambient edge lies in the retained vertex
set. -/
theorem endpoints_mem_retainedVertexSet
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge data edge) :
    ∀ vertex ∈ (edge.1 : Sym2 V),
      vertex ∈ retainedVertexSet data.firstVertex data.secondVertex := by
  intro vertex hvertex
  constructor
  · intro hfirst
    subst vertex
    rcases edge_eq_central_or_firstPort_of_mem data edge hvertex with
      hedge | hedge | hedge
    · exact hretained.1 hedge
    · exact hretained.2.1 hedge
    · exact hretained.2.2.1 hedge
  · intro hsecond
    subst vertex
    rcases edge_eq_central_or_secondPort_of_mem data edge hvertex with
      hedge | hedge | hedge
    · exact hretained.1 hedge
    · exact hretained.2.2.2.1 hedge
    · exact hretained.2.2.2.2 hedge

/-- A retained ambient edge, regarded as an edge of the induced deletion. -/
def ambientEdgeToRetainedEdge (data : AdjacentPairData G)
    (edge : G.edgeSet) (hretained : IsRetainedAmbientEdge data edge) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  let hendpoints := endpoints_mem_retainedVertexSet data edge hretained
  ⟨edge.1.attachWith hendpoints, by
    apply ((retainedGraphEmbedding data).map_mem_edgeSet_iff).1
    rw [show (edge.1.attachWith hendpoints).map
        (retainedGraphEmbedding data) = edge.1 by
      change (edge.1.attachWith hendpoints).map Subtype.val = edge.1
      exact Sym2.attachWith_map_subtypeVal hendpoints]
    exact edge.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem retainedEdgeToAmbientEdge_ambientEdgeToRetainedEdge
    (data : AdjacentPairData G)
    (edge : G.edgeSet) (hretained : IsRetainedAmbientEdge data edge) :
    retainedEdgeToAmbientEdge data
        (ambientEdgeToRetainedEdge data edge hretained) = edge := by
  apply Subtype.ext
  change (edge.1.attachWith
      (endpoints_mem_retainedVertexSet data edge hretained)).map
        Subtype.val = edge.1
  exact Sym2.attachWith_map_subtypeVal
    (endpoints_mem_retainedVertexSet data edge hretained)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem mem_ambientEdgeToRetainedEdge_iff
    (data : AdjacentPairData G)
    (edge : G.edgeSet) (hretained : IsRetainedAmbientEdge data edge)
    (vertex : V)
    (hvertex : vertex ∈
      retainedVertexSet data.firstVertex data.secondVertex) :
    (⟨vertex, hvertex⟩ : retainedVertexSet data.firstVertex
        data.secondVertex) ∈
        (ambientEdgeToRetainedEdge data edge hretained).1 ↔
      vertex ∈ (edge.1 : Sym2 V) := by
  change (⟨vertex, hvertex⟩ ∈ edge.1.attachWith
      (endpoints_mem_retainedVertexSet data edge hretained)) ↔ _
  constructor
  · intro hmem
    rw [Sym2.attachWith] at hmem
    rcases (Sym2.mem_pmap_iff Subtype.mk edge.1
        (endpoints_mem_retainedVertexSet data edge hretained)
        ⟨vertex, hvertex⟩).1 hmem with
      ⟨other, hother, heq⟩
    have hvalue : vertex = other := congrArg Subtype.val heq
    simpa [hvalue] using hother
  · intro hmem
    rw [Sym2.attachWith]
    apply (Sym2.mem_pmap_iff Subtype.mk edge.1
      (endpoints_mem_retainedVertexSet data edge hretained)
      ⟨vertex, hvertex⟩).2
    exact ⟨vertex, hmem, Subtype.ext rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Adjacency between retained ambient edges is exactly visible in the
induced deletion. -/
theorem ambientEdgeToRetainedEdge_adj
    (data : AdjacentPairData G)
    (first second : G.edgeSet)
    (hfirst : IsRetainedAmbientEdge data first)
    (hsecond : IsRetainedAmbientEdge data second)
    (hadj : G.lineGraph.Adj first second) :
    (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).lineGraph.Adj
        (ambientEdgeToRetainedEdge data first hfirst)
        (ambientEdgeToRetainedEdge data second hsecond) := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
    ⟨hne, vertex, hvertexFirst, hvertexSecond⟩
  have hvertexRetained :=
    endpoints_mem_retainedVertexSet data first hfirst vertex hvertexFirst
  apply (SimpleGraph.lineGraph_adj_iff_exists).2
  refine ⟨?_, ⟨vertex, hvertexRetained⟩, ?_, ?_⟩
  · intro heq
    apply hne
    calc
      first = retainedEdgeToAmbientEdge data
          (ambientEdgeToRetainedEdge data first hfirst) := by simp
      _ = retainedEdgeToAmbientEdge data
          (ambientEdgeToRetainedEdge data second hsecond) := by rw [heq]
      _ = second := by simp
  · exact (mem_ambientEdgeToRetainedEdge_iff data first hfirst
      vertex hvertexRetained).2 hvertexFirst
  · have hvertexRetainedSecond :=
      endpoints_mem_retainedVertexSet data second hsecond vertex
        hvertexSecond
    exact (mem_ambientEdgeToRetainedEdge_iff data second hsecond
      vertex hvertexRetainedSecond).2 hvertexSecond

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The restored central edge has no line-graph adjacency to a retained
edge, since all endpoints of a retained edge survive the deletion. -/
theorem not_centralEdge_adj_retained
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge data edge) :
    ¬ G.lineGraph.Adj (centralEdge data) edge := by
  intro hadj
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
    ⟨_hne, vertex, hvertexCentral, hvertexEdge⟩
  have hsurvives := endpoints_mem_retainedVertexSet data edge hretained
    vertex hvertexEdge
  have hdeleted : vertex = data.firstVertex ∨
      vertex = data.secondVertex := by
    simpa [centralEdge, centralEdgeValue] using hvertexCentral
  rcases hdeleted with rfl | rfl
  · exact hsurvives.1 rfl
  · exact hsurvives.2 rfl

/-- If a retained edge meets one of the four restored boundary edges, its
induced copy is incident with the corresponding degree-two port. -/
theorem ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
    (data : AdjacentPairData G) (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge data edge) (port : Fin 4)
    (hadj : G.lineGraph.Adj edge (boundaryEdge data port)) :
    ambientEdgeToRetainedEdge data edge hretained ∈
      incidentEdgeFinset
        (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
        (data.retainedPort port) := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
    ⟨_hne, vertex, hvertexEdge, hvertexBoundary⟩
  have hsurvives := endpoints_mem_retainedVertexSet data edge hretained
    vertex hvertexEdge
  have hvertexPort : vertex = data.portVertex port := by
    fin_cases port <;>
      simpa [boundaryEdge, boundaryEdgeValue, hsurvives.1,
        hsurvives.2] using hvertexBoundary
  subst vertex
  have hmem := (mem_ambientEdgeToRetainedEdge_iff data edge hretained
    (data.portVertex port) hsurvives).2 hvertexEdge
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact hmem

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two distinct restored boundary edges can meet only on the first or the
second deleted vertex. -/
theorem boundaryEdge_adj_implies_sameSide
    (data : AdjacentPairData G) (first second : Fin 4)
    (hadj : G.lineGraph.Adj
      (boundaryEdge data first) (boundaryEdge data second)) :
    (first = 0 ∧ second = 1) ∨
      (first = 1 ∧ second = 0) ∨
      (first = 2 ∧ second = 3) ∨
      (first = 3 ∧ second = 2) := by
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hadj with
    ⟨hne, vertex, hvertexFirst, hvertexSecond⟩
  have hvertexFirst' :
      vertex = boundaryDeletedVertex data first ∨
        vertex = data.portVertex first := by
    simpa [boundaryEdge, boundaryEdgeValue_eq data first] using hvertexFirst
  have hvertexSecond' :
      vertex = boundaryDeletedVertex data second ∨
        vertex = data.portVertex second := by
    simpa [boundaryEdge, boundaryEdgeValue_eq data second] using hvertexSecond
  have hdeletedEndpoints :
      boundaryDeletedVertex data first =
        boundaryDeletedVertex data second := by
    rcases hvertexFirst' with hfirstDeleted | hfirstPort <;>
      rcases hvertexSecond' with hsecondDeleted | hsecondPort
    · exact hfirstDeleted.symm.trans hsecondDeleted
    · exfalso
      exact boundaryDeletedVertex_ne_portVertex data first second
        (hfirstDeleted.symm.trans hsecondPort)
    · exfalso
      exact boundaryDeletedVertex_ne_portVertex data second first
        (hsecondDeleted.symm.trans hfirstPort)
    · exfalso
      have hports : first = second :=
        data.portInjective (hfirstPort.symm.trans hsecondPort)
      subst second
      exact hne rfl
  have hportsNe : first ≠ second := by
    intro hports
    subst second
    exact hne rfl
  have hsecondFirst : data.secondVertex ≠ data.firstVertex :=
    data.centralAdjacent.ne.symm
  fin_cases first <;> fin_cases second <;>
    simp_all [boundaryDeletedVertex, data.centralAdjacent.ne]

/-- The edge-color function obtained by restoring the adjacent pair, its
central edge, and its four boundary edges. -/
def insertAdjacentPairColorFunction
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (bridge : Color) (edge : G.edgeSet) : Color :=
  if hcentral : edge.1 = centralEdgeValue data then bridge
  else if hzero : edge.1 = boundaryEdgeValue data 0 then
    data.degreeTwoBoundaryData.colorWord C 0
  else if hone : edge.1 = boundaryEdgeValue data 1 then
    data.degreeTwoBoundaryData.colorWord C 1
  else if htwo : edge.1 = boundaryEdgeValue data 2 then
    data.degreeTwoBoundaryData.colorWord C 2
  else if hthree : edge.1 = boundaryEdgeValue data 3 then
    data.degreeTwoBoundaryData.colorWord C 3
  else C (ambientEdgeToRetainedEdge data edge
    (isRetainedAmbientEdge_of_ne data edge hcentral hzero hone htwo hthree))

@[simp]
theorem insertAdjacentPairColorFunction_central
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (bridge : Color) :
    insertAdjacentPairColorFunction data C bridge (centralEdge data) =
      bridge := by
  simp [insertAdjacentPairColorFunction, centralEdge]

@[simp]
theorem insertAdjacentPairColorFunction_boundary
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (bridge : Color) (port : Fin 4) :
    insertAdjacentPairColorFunction data C bridge
        (boundaryEdge data port) =
      data.degreeTwoBoundaryData.colorWord C port := by
  have hcentral : (boundaryEdge data port).1 ≠ centralEdgeValue data :=
    (centralEdgeValue_ne_boundaryEdgeValue data port).symm
  rw [insertAdjacentPairColorFunction, dif_neg hcentral]
  by_cases hzero : port = 0
  · subst port
    rw [dif_pos (boundaryEdge_val data 0)]
  · have hzeroValue : (boundaryEdge data port).1 ≠
        boundaryEdgeValue data 0 := boundaryEdgeValue_ne data hzero
    rw [dif_neg hzeroValue]
    by_cases hone : port = 1
    · subst port
      rw [dif_pos (boundaryEdge_val data 1)]
    · have honeValue : (boundaryEdge data port).1 ≠
          boundaryEdgeValue data 1 := boundaryEdgeValue_ne data hone
      rw [dif_neg honeValue]
      by_cases htwo : port = 2
      · subst port
        rw [dif_pos (boundaryEdge_val data 2)]
      · have htwoValue : (boundaryEdge data port).1 ≠
            boundaryEdgeValue data 2 := boundaryEdgeValue_ne data htwo
        rw [dif_neg htwoValue]
        have hthree : port = 3 := by omega
        subst port
        rw [dif_pos (boundaryEdge_val data 3)]

@[simp]
theorem insertAdjacentPairColorFunction_retained
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (bridge : Color) (edge : G.edgeSet)
    (hretained : IsRetainedAmbientEdge data edge) :
    insertAdjacentPairColorFunction data C bridge edge =
      C (ambientEdgeToRetainedEdge data edge hretained) := by
  have hcentral : edge.1 ≠ centralEdgeValue data := hretained.1
  have hzero : edge.1 ≠ boundaryEdgeValue data 0 := hretained.2.1
  have hone : edge.1 ≠ boundaryEdgeValue data 1 := hretained.2.2.1
  have htwo : edge.1 ≠ boundaryEdgeValue data 2 := hretained.2.2.2.1
  have hthree : edge.1 ≠ boundaryEdgeValue data 3 :=
    hretained.2.2.2.2
  simp only [insertAdjacentPairColorFunction, dif_neg hcentral,
    dif_neg hzero, dif_neg hone, dif_neg htwo, dif_neg hthree]

/-- The bridge color differs from every boundary color whenever the local
two-vertex extension table accepts it. -/
theorem bridge_ne_colorWord
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge)
    (port : Fin 4) :
    bridge ≠ data.degreeTwoBoundaryData.colorWord C port := by
  rcases hbridge with
    ⟨⟨_hzero, _hone, _hbridgeZero, _hzeroOne, hzeroBridge,
        honeBridge⟩,
      ⟨_htwo, _hthree, _hbridgeOne, _htwoThree, htwoBridge,
        hthreeBridge⟩⟩
  fin_cases port
  · exact hzeroBridge.symm
  · exact honeBridge.symm
  · exact htwoBridge.symm
  · exact hthreeBridge.symm

/-- Adjacent restored boundary edges receive distinct colors from an
accepted bridge-extension word. -/
theorem colorWord_ne_of_boundaryEdge_adj
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge)
    (first second : Fin 4)
    (hadj : G.lineGraph.Adj
      (boundaryEdge data first) (boundaryEdge data second)) :
    data.degreeTwoBoundaryData.colorWord C first ≠
      data.degreeTwoBoundaryData.colorWord C second := by
  rcases hbridge with
    ⟨⟨_hzero, _hone, _hbridgeZero, hzeroOne, _hzeroBridge,
        _honeBridge⟩,
      ⟨_htwo, _hthree, _hbridgeOne, htwoThree, _htwoBridge,
        _hthreeBridge⟩⟩
  rcases boundaryEdge_adj_implies_sameSide data first second hadj with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hzeroOne
  · exact hzeroOne.symm
  · exact htwoThree
  · exact htwoThree.symm

/-- Properness of the restored edge-color function. The proof separates
retained-retained adjacency, retained-port adjacency, and the two local
cubic triples. -/
theorem insertAdjacentPairColorFunction_valid
    (data : AdjacentPairData G)
    (hboundary : data.degreeTwoBoundaryData.WellFormed)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge) :
    ∀ {first second : G.edgeSet}, G.lineGraph.Adj first second →
      insertAdjacentPairColorFunction data C bridge first ≠
        insertAdjacentPairColorFunction data C bridge second := by
  intro first second hadj
  by_cases hfirst : IsRetainedAmbientEdge data first
  · by_cases hsecond : IsRetainedAmbientEdge data second
    · rw [insertAdjacentPairColorFunction_retained data C bridge first hfirst,
        insertAdjacentPairColorFunction_retained data C bridge second hsecond]
      exact C.valid
        (ambientEdgeToRetainedEdge_adj data first second hfirst hsecond hadj)
    · rcases (not_isRetainedAmbientEdge_iff data second).1 hsecond with
        hcentral | ⟨port, hport⟩
      · have hsecondEq : second = centralEdge data :=
          Subtype.ext hcentral
        subst second
        exact False.elim ((not_centralEdge_adj_retained data first hfirst)
          hadj.symm)
      · have hsecondEq : second = boundaryEdge data port :=
          Subtype.ext hport
        subst second
        have hincident :=
          ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
            data first hfirst port hadj
        have hadmissible :=
          DegreeTwoBoundaryData.colorWord_ne_incidentColor
            data.degreeTwoBoundaryData hboundary C hC port
            (ambientEdgeToRetainedEdge data first hfirst) hincident
        rw [insertAdjacentPairColorFunction_retained data C bridge first hfirst,
          insertAdjacentPairColorFunction_boundary]
        exact hadmissible.symm
  · by_cases hsecond : IsRetainedAmbientEdge data second
    · rcases (not_isRetainedAmbientEdge_iff data first).1 hfirst with
        hcentral | ⟨port, hport⟩
      · have hfirstEq : first = centralEdge data :=
          Subtype.ext hcentral
        subst first
        exact False.elim
          ((not_centralEdge_adj_retained data second hsecond) hadj)
      · have hfirstEq : first = boundaryEdge data port :=
          Subtype.ext hport
        subst first
        have hincident :=
          ambientEdgeToRetainedEdge_mem_incident_of_adj_boundaryEdge
            data second hsecond port hadj.symm
        have hadmissible :=
          DegreeTwoBoundaryData.colorWord_ne_incidentColor
            data.degreeTwoBoundaryData hboundary C hC port
            (ambientEdgeToRetainedEdge data second hsecond) hincident
        rw [insertAdjacentPairColorFunction_boundary,
          insertAdjacentPairColorFunction_retained data C bridge second hsecond]
        exact hadmissible
    · rcases (not_isRetainedAmbientEdge_iff data first).1 hfirst with
          hfirstCentral | ⟨firstPort, hfirstPort⟩ <;>
        rcases (not_isRetainedAmbientEdge_iff data second).1 hsecond with
          hsecondCentral | ⟨secondPort, hsecondPort⟩
      · have hfirstEq : first = centralEdge data :=
          Subtype.ext hfirstCentral
        have hsecondEq : second = centralEdge data :=
          Subtype.ext hsecondCentral
        subst first
        subst second
        exact False.elim (hadj.ne rfl)
      · have hfirstEq : first = centralEdge data :=
          Subtype.ext hfirstCentral
        have hsecondEq : second = boundaryEdge data secondPort :=
          Subtype.ext hsecondPort
        subst first
        subst second
        simpa using bridge_ne_colorWord data C bridge hbridge secondPort
      · have hfirstEq : first = boundaryEdge data firstPort :=
          Subtype.ext hfirstPort
        have hsecondEq : second = centralEdge data :=
          Subtype.ext hsecondCentral
        subst first
        subst second
        simpa using (bridge_ne_colorWord data C bridge hbridge firstPort).symm
      · have hfirstEq : first = boundaryEdge data firstPort :=
          Subtype.ext hfirstPort
        have hsecondEq : second = boundaryEdge data secondPort :=
          Subtype.ext hsecondPort
        subst first
        subst second
        simpa using colorWord_ne_of_boundaryEdge_adj data C bridge hbridge
          firstPort secondPort hadj

/-- Restore the adjacent pair as a proper edge coloring of the ambient
graph. -/
def insertAdjacentPairColoring
    (data : AdjacentPairData G)
    (hboundary : data.degreeTwoBoundaryData.WellFormed)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge) :
    G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (insertAdjacentPairColorFunction data C bridge)
    (insertAdjacentPairColorFunction_valid data hboundary C hC bridge hbridge)

@[simp]
theorem insertAdjacentPairColoring_central
    (data : AdjacentPairData G)
    (hboundary : data.degreeTwoBoundaryData.WellFormed)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge) :
    insertAdjacentPairColoring data hboundary C hC bridge hbridge
        (centralEdge data) = bridge := by
  change insertAdjacentPairColorFunction data C bridge (centralEdge data) =
    bridge
  exact insertAdjacentPairColorFunction_central data C bridge

@[simp]
theorem insertAdjacentPairColoring_boundary
    (data : AdjacentPairData G)
    (hboundary : data.degreeTwoBoundaryData.WellFormed)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge)
    (port : Fin 4) :
    insertAdjacentPairColoring data hboundary C hC bridge hbridge
        (boundaryEdge data port) =
      data.degreeTwoBoundaryData.colorWord C port := by
  change insertAdjacentPairColorFunction data C bridge
      (boundaryEdge data port) = _
  exact insertAdjacentPairColorFunction_boundary data C bridge port

@[simp]
theorem insertAdjacentPairColoring_retained
    (data : AdjacentPairData G)
    (hboundary : data.degreeTwoBoundaryData.WellFormed)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge)
    (edge : G.edgeSet) (hretained : IsRetainedAmbientEdge data edge) :
    insertAdjacentPairColoring data hboundary C hC bridge hbridge edge =
      C (ambientEdgeToRetainedEdge data edge hretained) := by
  change insertAdjacentPairColorFunction data C bridge edge = _
  exact insertAdjacentPairColorFunction_retained data C bridge edge hretained

/-- Restoring an accepted bridge extension preserves the nonzero Tait
condition on every ambient edge. -/
theorem isTaitEdgeColoring_insertAdjacentPairColoring
    (data : AdjacentPairData G)
    (hboundary : data.degreeTwoBoundaryData.WellFormed)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge) :
    IsTaitEdgeColoring G
      (insertAdjacentPairColoring data hboundary C hC bridge hbridge) := by
  intro edge
  by_cases hretained : IsRetainedAmbientEdge data edge
  · rw [insertAdjacentPairColoring_retained data hboundary C hC bridge
      hbridge edge hretained]
    exact hC (ambientEdgeToRetainedEdge data edge hretained)
  · rcases (not_isRetainedAmbientEdge_iff data edge).1 hretained with
      hcentral | ⟨port, hport⟩
    · have hedge : edge = centralEdge data := Subtype.ext hcentral
      subst edge
      rw [insertAdjacentPairColoring_central]
      exact hbridge.1.2.2.1
    · have hedge : edge = boundaryEdge data port := Subtype.ext hport
      subst edge
      rw [insertAdjacentPairColoring_boundary]
      exact data.degreeTwoBoundaryData.colorWord_ne_zero hboundary C port

/-- Graph-level adjacent-pair insertion theorem: every accepted local
bridge extension yields a Tait coloring of the original cubic graph. -/
theorem exists_taitColoring_of_deletedAdjacentPair_bridgeExtension
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    (bridge : Color)
    (hbridge : IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge) :
    ∃ ambientColoring : G.EdgeColoring Color,
      IsTaitEdgeColoring G ambientColoring := by
  let hboundary := data.degreeTwoBoundaryData_wellFormed hcubic
  exact ⟨insertAdjacentPairColoring data hboundary C hC bridge hbridge,
    isTaitEdgeColoring_insertAdjacentPairColoring data hboundary C hC
      bridge hbridge⟩

/-- In an uncolorable cubic graph, no Tait coloring of an adjacent-pair
deletion can permit the local bridge extension. -/
theorem not_exists_deletedAdjacentPair_bridgeExtension_of_not_taitColorable
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    ¬ ∃ bridge : Color, IsTwoVertexBridgeExtension
      (data.degreeTwoBoundaryData.colorWord C) bridge := by
  rintro ⟨bridge, hbridge⟩
  exact hnotColorable
    (exists_taitColoring_of_deletedAdjacentPair_bridgeExtension
      data hcubic C hC bridge hbridge)

/-- Exact graph-backed obstruction sector: every colored adjacent-pair
deletion of an uncolorable cubic graph has equal requests on each restored
vertex side. -/
theorem sameSidePairs_of_not_taitColorable
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C) :
    data.degreeTwoBoundaryData.colorWord C 0 =
        data.degreeTwoBoundaryData.colorWord C 1 ∧
      data.degreeTwoBoundaryData.colorWord C 2 =
        data.degreeTwoBoundaryData.colorWord C 3 := by
  apply (data.deletedAdjacentPair_not_exists_bridgeExtension_iff
    hcubic C hC).1
  exact not_exists_deletedAdjacentPair_bridgeExtension_of_not_taitColorable
    data hcubic hnotColorable C hC

end AdjacentPairData

end

end GoertzelV24AdjacentPairInsertion

end Mettapedia.GraphTheory.FourColor
