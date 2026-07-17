import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileReversedDartSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCoherentCircuitExtraction

namespace List

/-- Forgetting subtype proofs commutes with reversing a list. -/
@[simp] theorem unattach_reverse_subtype {Alpha : Type*} {predicate : Alpha → Prop}
    (items : List {item // predicate item}) :
    items.reverse.unattach = items.unattach.reverse := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih]

/-- The second element of a reversed list is the penultimate element of
the original list. -/
theorem reverse_getElem_one {Alpha : Type*} (items : List Alpha)
    (htwo : 2 ≤ items.length) :
    items.reverse[1]'(by
      simp only [List.length_reverse]
      omega) =
      items[items.length - 2]'(by omega) := by
  change items.reverse.get ⟨1, by
    simp only [List.length_reverse]
    omega⟩ =
    items.get ⟨items.length - 2, by omega⟩
  rw [List.get_reverse']
  congr 1
  omega

/-- Equal lists written in opposite orders have equal second and
penultimate elements. -/
theorem getElem_one_eq_penultimate_of_eq_reverse {Alpha : Type*}
    (left right : List Alpha) (hleft : 2 ≤ left.length)
    (hright : 2 ≤ right.length) (heq : left = right.reverse) :
    left[1]'(by omega) = right[right.length - 2]'(by omega) := by
  subst left
  exact right.reverse_getElem_one hright

end List

namespace SimpleGraph.Walk

universe u

variable {Vertex : Type u} {Graph : SimpleGraph Vertex}

/-- The graph-edge vertices visited in the line graph by a primal walk. -/
def edgeSubtypeSupport {left right : Vertex}
    (walk : Graph.Walk left right) : List Graph.edgeSet :=
  walk.darts.map fun dart => ⟨dart.edge, dart.edge_mem⟩

@[simp] theorem edgeSubtypeSupport_length {left right : Vertex}
    (walk : Graph.Walk left right) :
    walk.edgeSubtypeSupport.length = walk.length := by
  simp [edgeSubtypeSupport]

/-- Forgetting edge-set membership recovers the primal edge list exactly. -/
@[simp] theorem edgeSubtypeSupport_map_val {left right : Vertex}
    (walk : Graph.Walk left right) :
    walk.edgeSubtypeSupport.map Subtype.val = walk.edges := by
  simp [edgeSubtypeSupport, SimpleGraph.Walk.edges, Function.comp_def]

@[simp] theorem edgeSubtypeSupport_unattach {left right : Vertex}
    (walk : Graph.Walk left right) :
    walk.edgeSubtypeSupport.unattach = walk.edges :=
  walk.edgeSubtypeSupport_map_val

/-- The first line-graph support vertex lies over the first primal edge. -/
theorem edgeSubtypeSupport_head_val {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length) :
    (walk.edgeSubtypeSupport.head (by
        intro hempty
        have hlength := congrArg List.length hempty
        rw [walk.edgeSubtypeSupport_length] at hlength
        change walk.length = 0 at hlength
        exact (Nat.ne_of_gt hpositive) hlength)).1 =
      walk.edges[0]'(by simpa using hpositive) := by
  cases walk with
  | nil => simp at hpositive
  | cons edge tail => rfl

/-- The last line-graph support vertex lies over the last primal edge. -/
theorem edgeSubtypeSupport_getLast_val {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length) :
    (walk.edgeSubtypeSupport.getLast (by
        intro hempty
        have hlength := congrArg List.length hempty
        rw [walk.edgeSubtypeSupport_length] at hlength
        change walk.length = 0 at hlength
        exact (Nat.ne_of_gt hpositive) hlength)).1 =
      walk.edges[walk.length - 1]'(by
        rw [walk.length_edges]
        omega) := by
  induction walk with
  | nil => simp at hpositive
  | @cons first middle last edge tail ih =>
      cases tail with
      | nil => rfl
      | @cons _ next _ nextEdge rest =>
          have htailPositive :
              0 < (SimpleGraph.Walk.cons nextEdge rest).length := by
            simp
          simpa [edgeSubtypeSupport] using ih htailPositive

/-- A primal trail visits no line-graph vertex twice. -/
theorem IsTrail.edgeSubtypeSupport_nodup {left right : Vertex}
    {walk : Graph.Walk left right} (htrail : walk.IsTrail) :
    walk.edgeSubtypeSupport.Nodup := by
  apply List.Nodup.of_map Subtype.val
  rw [walk.edgeSubtypeSupport_map_val]
  exact htrail.edges_nodup

/-- Consecutive edges of a primal trail are adjacent vertices of its line
graph. -/
theorem IsTrail.edgeSubtypeSupport_isChain {left right : Vertex}
    {walk : Graph.Walk left right} (htrail : walk.IsTrail) :
    walk.edgeSubtypeSupport.IsChain Graph.lineGraph.Adj := by
  induction walk with
  | nil => exact .nil
  | @cons first middle last hfirst tail ih =>
      cases tail with
      | nil => exact .singleton _
      | @cons _ next _ hsecond rest =>
          simp only [edgeSubtypeSupport, SimpleGraph.Walk.darts_cons,
            List.map_cons]
          apply List.IsChain.cons_cons
          · apply (SimpleGraph.lineGraph_adj_iff_exists).2
            refine ⟨?_, middle, Sym2.mem_mk_right _ _,
              Sym2.mem_mk_left _ _⟩
            intro hedge
            have hvalue : s(first, middle) = s(middle, next) :=
              congrArg Subtype.val hedge
            have htail := (SimpleGraph.Walk.isTrail_cons hfirst
              (SimpleGraph.Walk.cons hsecond rest)).1 htrail
            exact htail.2 (by simp [hvalue])
          · exact ih htrail.of_cons

/-- The canonical line-graph walk supported by every edge of a nonempty
primal trail. -/
def lineGraphWalkOfTrail {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length)
    (htrail : walk.IsTrail) :
    Graph.lineGraph.Walk
      (walk.edgeSubtypeSupport.head (by
        intro hempty
        have hlength := congrArg List.length hempty
        rw [walk.edgeSubtypeSupport_length] at hlength
        change walk.length = 0 at hlength
        exact (Nat.ne_of_gt hpositive) hlength))
      (walk.edgeSubtypeSupport.getLast (by
        intro hempty
        have hlength := congrArg List.length hempty
        rw [walk.edgeSubtypeSupport_length] at hlength
        change walk.length = 0 at hlength
        exact (Nat.ne_of_gt hpositive) hlength)) :=
  SimpleGraph.Walk.ofSupport walk.edgeSubtypeSupport
    (by
      intro hempty
      have hlength := congrArg List.length hempty
      rw [walk.edgeSubtypeSupport_length] at hlength
      change walk.length = 0 at hlength
      exact (Nat.ne_of_gt hpositive) hlength)
    htrail.edgeSubtypeSupport_isChain

/-- Its support is exactly the primal edge list, with membership proofs. -/
@[simp] theorem lineGraphWalkOfTrail_support {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length)
    (htrail : walk.IsTrail) :
    (walk.lineGraphWalkOfTrail hpositive htrail).support =
      walk.edgeSubtypeSupport := by
  exact SimpleGraph.Walk.support_ofSupport _ _

/-- Its line-graph length is one less than the primal trail length. -/
@[simp] theorem lineGraphWalkOfTrail_length {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length)
    (htrail : walk.IsTrail) :
    (walk.lineGraphWalkOfTrail hpositive htrail).length =
      walk.length - 1 := by
  simp [lineGraphWalkOfTrail]

/-- The canonical line-graph walk of a nonempty primal trail is a path. -/
theorem lineGraphWalkOfTrail_isPath {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length)
    (htrail : walk.IsTrail) :
    (walk.lineGraphWalkOfTrail hpositive htrail).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,
    walk.lineGraphWalkOfTrail_support hpositive htrail]
  exact htrail.edgeSubtypeSupport_nodup

/-- The junction at a step of the canonical line-graph path is exactly the
intermediate vertex of the primal trail. -/
theorem lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert
    {left right : Vertex} (walk : Graph.Walk left right)
    (hpositive : 0 < walk.length) (htrail : walk.IsTrail)
    (position : Fin (walk.lineGraphWalkOfTrail hpositive htrail).length) :
    (walk.lineGraphWalkOfTrail hpositive htrail).lineGraphJunctionAt
        position = walk.getVert (position.val + 1) := by
  let lineWalk := walk.lineGraphWalkOfTrail hpositive htrail
  have hlineLength : lineWalk.length = walk.length - 1 := by
    exact walk.lineGraphWalkOfTrail_length hpositive htrail
  have hfirstDart : position.val < walk.darts.length := by
    have hposition := position.isLt
    have hrawLength :=
      walk.lineGraphWalkOfTrail_length hpositive htrail
    have hdartsLength := walk.length_darts
    omega
  have hsecondDart : position.val + 1 < walk.darts.length := by
    have hposition := position.isLt
    have hrawLength :=
      walk.lineGraphWalkOfTrail_length hpositive htrail
    have hdartsLength := walk.length_darts
    omega
  have hfirstValue :
      (lineWalk.getVert position.val).1 =
        (walk.darts[position.val]'hfirstDart).edge := by
    dsimp only [lineWalk]
    rw [(walk.lineGraphWalkOfTrail hpositive htrail).getVert_eq_support_getElem
      (by omega)]
    simp [lineGraphWalkOfTrail, edgeSubtypeSupport]
  have hsecondValue :
      (lineWalk.getVert (position.val + 1)).1 =
        (walk.darts[position.val + 1]'hsecondDart).edge := by
    dsimp only [lineWalk]
    rw [(walk.lineGraphWalkOfTrail hpositive htrail).getVert_eq_support_getElem
      (by omega)]
    simp [lineGraphWalkOfTrail, edgeSubtypeSupport]
  change lineWalk.lineGraphJunctionAt position = _
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · rw [hfirstValue, walk.darts_getElem_eq_getVert]
    exact Sym2.mem_mk_right _ _
  · rw [hsecondValue, walk.darts_getElem_eq_getVert]
    exact Sym2.mem_mk_left _ _

/-- Hence every canonical line-graph path of a primal trail is internally
primal-coherent. -/
theorem lineGraphWalkOfTrail_isPrimalCoherent {left right : Vertex}
    (walk : Graph.Walk left right) (hpositive : 0 < walk.length)
    (htrail : walk.IsTrail) :
    (walk.lineGraphWalkOfTrail hpositive htrail).IsPrimalCoherent := by
  intro position hposition
  rw [walk.lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert hpositive
      htrail ⟨position, by omega⟩,
    walk.lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert hpositive
      htrail ⟨position + 1, hposition⟩]
  apply (walk.adj_getVert_succ (i := position + 1) (by
    have hlineLength :=
      walk.lineGraphWalkOfTrail_length hpositive htrail
    omega)).ne

/-- Endpoint copies do not change open primal coherence. -/
theorem IsPrimalCoherent.copy {first last first' last' : Graph.edgeSet}
    {walk : Graph.lineGraph.Walk first last}
    (hcoherent : walk.IsPrimalCoherent)
    (hfirst : first = first') (hlast : last = last') :
    (walk.copy hfirst hlast).IsPrimalCoherent := by
  subst first'
  subst last'
  simpa using hcoherent

/-- Junctions of a reversed line-graph walk are the original junctions in
reverse order. -/
theorem lineGraphJunctionAt_reverse_at {first last : Graph.edgeSet}
    (walk : Graph.lineGraph.Walk first last)
    (position : Fin walk.reverse.length) :
    walk.reverse.lineGraphJunctionAt position =
      walk.lineGraphJunctionAt ⟨walk.length - 1 - position.val, by
        have hposition := position.isLt
        have hreverseLength := SimpleGraph.Walk.length_reverse walk
        omega⟩ := by
  let originalPosition : Fin walk.length :=
    ⟨walk.length - 1 - position.val, by
      have hposition := position.isLt
      have hreverseLength := SimpleGraph.Walk.length_reverse walk
      omega⟩
  have hposition := position.isLt
  have hreverseLength := SimpleGraph.Walk.length_reverse walk
  have hrightIndex :
      walk.length - (position.val + 1) = originalPosition.val := by
    dsimp only [originalPosition]
    omega
  have hleftIndex :
      walk.length - position.val = originalPosition.val + 1 := by
    dsimp only [originalPosition]
    omega
  change walk.reverse.lineGraphJunctionAt position =
    walk.lineGraphJunctionAt originalPosition
  symm
  apply SimpleGraph.lineGraphCommonVertex_unique
  · have hmem := walk.lineGraphJunctionAt_mem_right originalPosition
    simpa only [SimpleGraph.Walk.getVert_reverse, hleftIndex] using hmem
  · have hmem := walk.lineGraphJunctionAt_mem_left originalPosition
    simpa only [SimpleGraph.Walk.getVert_reverse, hrightIndex] using hmem

/-- Reversal preserves open primal coherence. -/
theorem IsPrimalCoherent.reverse {first last : Graph.edgeSet}
    {walk : Graph.lineGraph.Walk first last}
    (hcoherent : walk.IsPrimalCoherent) :
    walk.reverse.IsPrimalCoherent := by
  intro position hposition
  let firstReversed : Fin walk.reverse.length := ⟨position, by omega⟩
  let secondReversed : Fin walk.reverse.length :=
    ⟨position + 1, hposition⟩
  rw [walk.lineGraphJunctionAt_reverse_at firstReversed,
    walk.lineGraphJunctionAt_reverse_at secondReversed]
  have hlength : walk.reverse.length = walk.length :=
    SimpleGraph.Walk.length_reverse walk
  have horiginal := hcoherent (walk.length - 2 - position) (by
    rw [SimpleGraph.Walk.length_reverse] at hposition
    omega)
  intro heq
  apply horiginal
  have hfirstValue :
      walk.length - 1 - firstReversed.val =
        walk.length - 2 - position + 1 := by
    dsimp only [firstReversed]
    rw [SimpleGraph.Walk.length_reverse] at hposition
    omega
  have hsecondValue :
      walk.length - 1 - secondReversed.val =
        walk.length - 2 - position := by
    dsimp only [secondReversed]
    rw [SimpleGraph.Walk.length_reverse] at hposition
    omega
  let originalFirst : Fin walk.length :=
    ⟨walk.length - 1 - firstReversed.val, by
      rw [SimpleGraph.Walk.length_reverse] at hposition
      omega⟩
  let originalSecond : Fin walk.length :=
    ⟨walk.length - 1 - secondReversed.val, by
      rw [SimpleGraph.Walk.length_reverse] at hposition
      omega⟩
  change walk.lineGraphJunctionAt originalFirst =
    walk.lineGraphJunctionAt originalSecond at heq
  have hfirstFin : originalFirst =
      ⟨walk.length - 2 - position + 1, by
        rw [SimpleGraph.Walk.length_reverse] at hposition
        omega⟩ := by
    apply Fin.ext
    exact hfirstValue
  have hsecondFin : originalSecond =
      ⟨walk.length - 2 - position, by
        rw [SimpleGraph.Walk.length_reverse] at hposition
        omega⟩ := by
    apply Fin.ext
    exact hsecondValue
  rw [hfirstFin, hsecondFin] at heq
  exact heq.symm

/-- Endpoint copies preserve every selected primal junction. -/
theorem lineGraphJunctionAt_copy_at {first last first' last' : Graph.edgeSet}
    (walk : Graph.lineGraph.Walk first last)
    (hfirst : first = first') (hlast : last = last')
    (position : Fin (walk.copy hfirst hlast).length) :
    (walk.copy hfirst hlast).lineGraphJunctionAt position =
      walk.lineGraphJunctionAt ⟨position.val, by
        simpa only [SimpleGraph.Walk.length_copy] using position.isLt⟩ := by
  subst first'
  subst last'
  rfl

/-- The first junction of a canonical line-graph path is the first
intermediate primal vertex. -/
theorem lineGraphWalkOfTrail_firstJunction {left right : Vertex}
    (walk : Graph.Walk left right) (htwo : 2 ≤ walk.length)
    (htrail : walk.IsTrail) :
    (walk.lineGraphWalkOfTrail (by omega) htrail).lineGraphJunctionAt
        ⟨0, by simp; omega⟩ = walk.getVert 1 := by
  exact walk.lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert
    (by omega) htrail ⟨0, by simp; omega⟩

/-- The last junction is the last intermediate primal vertex. -/
theorem lineGraphWalkOfTrail_lastJunction {left right : Vertex}
    (walk : Graph.Walk left right) (htwo : 2 ≤ walk.length)
    (htrail : walk.IsTrail) :
    (walk.lineGraphWalkOfTrail (by omega) htrail).lineGraphJunctionAt
        ⟨(walk.lineGraphWalkOfTrail (by omega) htrail).length - 1,
          by simp; omega⟩ = walk.getVert (walk.length - 1) := by
  rw [walk.lineGraphWalkOfTrail_lineGraphJunctionAt_eq_getVert
    (by omega) htrail]
  change walk.getVert
      ((walk.lineGraphWalkOfTrail (by omega) htrail).length - 1 + 1) =
    walk.getVert (walk.length - 1)
  have hlength := walk.lineGraphWalkOfTrail_length (by omega) htrail
  congr 1
  omega

/-- Exact vertices along an edge interval. -/
theorem edgeInterval_getVert {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (horder : first ≤ second)
    (offset : Nat) (hoffset : offset ≤ second.val - first.val + 1) :
    (walk.edgeInterval first second horder).getVert offset =
      walk.getVert (first.val + offset) := by
  simp only [SimpleGraph.Walk.edgeInterval,
    SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
    SimpleGraph.Walk.drop_getVert]
  rw [Nat.min_eq_right hoffset]

/-- If two selected darts have the same orientation, the edge immediately
after the first cannot equal the edge immediately before the second. -/
theorem IsTrail.nextEdge_ne_previousEdge_of_same_position_dart
    {firstLeft firstRight secondLeft secondRight : Vertex}
    {firstWalk : Graph.Walk firstLeft firstRight}
    (htrail : firstWalk.IsTrail)
    (firstPosition : Fin firstWalk.edges.length)
    (secondWalk : Graph.Walk secondLeft secondRight)
    (secondPosition : Fin secondWalk.edges.length)
    (hnext : firstPosition.val + 1 < firstWalk.edges.length)
    (hprevious : 0 < secondPosition.val)
    (hsame : secondWalk.dartAtEdgePosition secondPosition =
      firstWalk.dartAtEdgePosition firstPosition) :
    firstWalk.edges.get ⟨firstPosition.val + 1, hnext⟩ ≠
      secondWalk.edges.get ⟨secondPosition.val - 1, by omega⟩ := by
  let nextPosition : Fin firstWalk.edges.length :=
    ⟨firstPosition.val + 1, hnext⟩
  let previousPosition : Fin secondWalk.edges.length :=
    ⟨secondPosition.val - 1, by omega⟩
  intro hedge
  have hdartEdge :
      (firstWalk.dartAtEdgePosition nextPosition).edge =
        (secondWalk.dartAtEdgePosition previousPosition).edge := by
    simpa only [SimpleGraph.Walk.dartAtEdgePosition_edge] using hedge
  have hnextJoin :
      (firstWalk.dartAtEdgePosition nextPosition).fst =
        (firstWalk.dartAtEdgePosition firstPosition).snd := by
    simp only [SimpleGraph.Walk.dartAtEdgePosition_fst,
      SimpleGraph.Walk.dartAtEdgePosition_snd]
    rfl
  have hpreviousJoin :
      (secondWalk.dartAtEdgePosition previousPosition).snd =
        (secondWalk.dartAtEdgePosition secondPosition).fst := by
    simp only [SimpleGraph.Walk.dartAtEdgePosition_fst,
      SimpleGraph.Walk.dartAtEdgePosition_snd]
    congr 1
    dsimp only [previousPosition]
    omega
  have hsameFst :
      (secondWalk.dartAtEdgePosition secondPosition).fst =
        (firstWalk.dartAtEdgePosition firstPosition).fst :=
    congrArg (fun dart => dart.fst) hsame
  have htargetInNext :
      (firstWalk.dartAtEdgePosition firstPosition).snd ∈
        (firstWalk.dartAtEdgePosition nextPosition).edge := by
    rw [← hnextJoin]
    exact Sym2.mem_mk_left _ _
  have hsourceInNext :
      (firstWalk.dartAtEdgePosition firstPosition).fst ∈
        (firstWalk.dartAtEdgePosition nextPosition).edge := by
    rw [hdartEdge, ← hsameFst, ← hpreviousJoin]
    exact Sym2.mem_mk_right _ _
  have hnextEqSelected :
      (firstWalk.dartAtEdgePosition nextPosition).edge =
        (firstWalk.dartAtEdgePosition firstPosition).edge := by
    exact Sym2.eq_of_ne_mem
      (firstWalk.dartAtEdgePosition firstPosition).fst_ne_snd
      hsourceInNext htargetInNext
      (Sym2.mem_mk_left _ _) (Sym2.mem_mk_right _ _)
  have hedgeGet : firstWalk.edges.get nextPosition =
      firstWalk.edges.get firstPosition := by
    simpa only [SimpleGraph.Walk.dartAtEdgePosition_edge] using
      hnextEqSelected
  have hpositionEq : nextPosition = firstPosition :=
    htrail.edges_nodup.get_inj_iff.mp hedgeGet
  have hvalueEq := congrArg Fin.val hpositionEq
  dsimp only [nextPosition] at hvalueEq
  omega

/-- The second edge of a nontrivial edge interval is the edge immediately
after its first selected position. -/
theorem edgeInterval_secondEdge {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (hstrict : first < second) :
    (walk.edgeInterval first second hstrict.le).edges[1]'(by
        have hlength := walk.edgeInterval_length first second hstrict.le
        have hedgeLength :=
          (walk.edgeInterval first second hstrict.le).length_edges
        omega) =
      walk.edges[first.val + 1]'(by
        have _hsecond := second.isLt
        omega) := by
  simp only [SimpleGraph.Walk.edgeInterval_edges, List.getElem_take,
    List.getElem_drop]

/-- The penultimate edge of a nontrivial edge interval is the edge
immediately before its second selected position. -/
theorem edgeInterval_penultimateEdge {left right : Vertex}
    (walk : Graph.Walk left right)
    (first second : Fin walk.edges.length) (hstrict : first < second) :
    (walk.edgeInterval first second hstrict.le).edges[
        second.val - first.val - 1]'(by
          have hlength := walk.edgeInterval_length first second hstrict.le
          have hedgeLength :=
            (walk.edgeInterval first second hstrict.le).length_edges
          omega) =
      walk.edges[second.val - 1]'(by
        have _hsecond := second.isLt
        omega) := by
  simp only [SimpleGraph.Walk.edgeInterval_edges, List.getElem_take,
    List.getElem_drop]
  congr 1
  omega

end SimpleGraph.Walk

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The first line-graph vertex of the prefix interval is its first
selected profile edge. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineStart_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    let interval := pair.prefixSharedEdgeInterval witness.first
      witness.second witness.first_lt_second.le
    interval.edgeSubtypeSupport.head (by
      intro hempty
      have hlength := congrArg List.length hempty
      rw [interval.edgeSubtypeSupport_length] at hlength
      change interval.length = 0 at hlength
      exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two
        witness.two_le_prefix_interval_length)) hlength) =
      pair.sharedEdgeAt witness.first := by
  dsimp only
  apply Subtype.ext
  rw [SimpleGraph.Walk.edgeSubtypeSupport_head_val _ (by
    exact lt_of_lt_of_le Nat.zero_lt_two
      witness.two_le_prefix_interval_length)]
  calc
    (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).edges[0]'(by
            rw [SimpleGraph.Walk.length_edges]
            exact lt_of_lt_of_le Nat.zero_lt_two
              witness.two_le_prefix_interval_length) =
        pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding witness.first) := by
      exact pair.prefixTrail.edgeInterval_firstEdge
        (pair.prefixSharedEdgePositionEmbedding witness.first)
        (pair.prefixSharedEdgePositionEmbedding witness.second)
        ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
          witness.first_lt_second.le)
    _ = pair.prefixSharedEdgeOrder.get witness.first :=
      (pair.prefixSharedEdgePositionEmbedding_preserves_edge
        witness.first).symm
    _ = (pair.sharedEdgeAt witness.first).1 := rfl

/-- The last line-graph vertex of the prefix interval is its second
selected profile edge. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineEnd_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    let interval := pair.prefixSharedEdgeInterval witness.first
      witness.second witness.first_lt_second.le
    interval.edgeSubtypeSupport.getLast (by
      intro hempty
      have hlength := congrArg List.length hempty
      rw [interval.edgeSubtypeSupport_length] at hlength
      change interval.length = 0 at hlength
      exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two
        witness.two_le_prefix_interval_length)) hlength) =
      pair.sharedEdgeAt witness.second := by
  dsimp only
  apply Subtype.ext
  rw [SimpleGraph.Walk.edgeSubtypeSupport_getLast_val _ (by
    exact lt_of_lt_of_le Nat.zero_lt_two
      witness.two_le_prefix_interval_length)]
  calc
    (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).edges[
        (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).length - 1]'(by
            have hedgeLength := SimpleGraph.Walk.length_edges
              (pair.prefixSharedEdgeInterval witness.first witness.second
                witness.first_lt_second.le)
            have htwo := witness.two_le_prefix_interval_length
            omega) =
        (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).edges[
          (pair.prefixSharedEdgePositionEmbedding witness.second).val -
            (pair.prefixSharedEdgePositionEmbedding witness.first).val]'(by
              have hedgeLength := SimpleGraph.Walk.length_edges
                (pair.prefixSharedEdgeInterval witness.first witness.second
                  witness.first_lt_second.le)
              have hinterLength := pair.prefixSharedEdgeInterval_length
                witness.first witness.second witness.first_lt_second.le
              omega) := by
      congr 1
      rw [pair.prefixSharedEdgeInterval_length]
      omega
    _ = pair.prefixTrail.edges.get
          (pair.prefixSharedEdgePositionEmbedding witness.second) := by
      exact pair.prefixTrail.edgeInterval_lastEdge
        (pair.prefixSharedEdgePositionEmbedding witness.first)
        (pair.prefixSharedEdgePositionEmbedding witness.second)
        ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
          witness.first_lt_second.le)
    _ = pair.prefixSharedEdgeOrder.get witness.second :=
      (pair.prefixSharedEdgePositionEmbedding_preserves_edge
        witness.second).symm
    _ = (pair.sharedEdgeAt witness.second).1 := rfl

/-- The first line-graph vertex of the suffix-order interval is the second
prefix-order profile edge. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixLineStart_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    let interval := pair.suffixReversedSharedEdgeInterval witness.first
      witness.second witness.suffix_order_reversed.le
    interval.edgeSubtypeSupport.head (by
      intro hempty
      have hlength := congrArg List.length hempty
      rw [interval.edgeSubtypeSupport_length] at hlength
      change interval.length = 0 at hlength
      exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two
        witness.two_le_suffix_interval_length)) hlength) =
      pair.sharedEdgeAt witness.second := by
  dsimp only
  apply Subtype.ext
  rw [SimpleGraph.Walk.edgeSubtypeSupport_head_val _ (by
    exact lt_of_lt_of_le Nat.zero_lt_two
      witness.two_le_suffix_interval_length)]
  calc
    (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edges[0]'(by
            rw [SimpleGraph.Walk.length_edges]
            exact lt_of_lt_of_le Nat.zero_lt_two
              witness.two_le_suffix_interval_length) =
        pair.suffixTrail.edges.get
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv witness.second)) := by
      exact pair.suffixTrail.edgeInterval_firstEdge
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv witness.second))
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv witness.first))
        ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
          witness.suffix_order_reversed.le)
    _ = pair.suffixSharedEdgeOrder.get
          (pair.sharedEdgeOrderEquiv witness.second) :=
      (pair.suffixSharedEdgePositionEmbedding_preserves_edge _).symm
    _ = pair.prefixSharedEdgeOrder.get witness.second :=
      pair.sharedEdgeOrderEquiv_preserves_edge witness.second
    _ = (pair.sharedEdgeAt witness.second).1 := rfl

/-- The last line-graph vertex of the suffix-order interval is the first
prefix-order profile edge. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixLineEnd_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    let interval := pair.suffixReversedSharedEdgeInterval witness.first
      witness.second witness.suffix_order_reversed.le
    interval.edgeSubtypeSupport.getLast (by
      intro hempty
      have hlength := congrArg List.length hempty
      rw [interval.edgeSubtypeSupport_length] at hlength
      change interval.length = 0 at hlength
      exact (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two
        witness.two_le_suffix_interval_length)) hlength) =
      pair.sharedEdgeAt witness.first := by
  dsimp only
  apply Subtype.ext
  rw [SimpleGraph.Walk.edgeSubtypeSupport_getLast_val _ (by
    exact lt_of_lt_of_le Nat.zero_lt_two
      witness.two_le_suffix_interval_length)]
  calc
    (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edges[
        (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).length - 1]'(by
            have hedgeLength := SimpleGraph.Walk.length_edges
              (pair.suffixReversedSharedEdgeInterval witness.first
                witness.second witness.suffix_order_reversed.le)
            have htwo := witness.two_le_suffix_interval_length
            omega) =
        (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edges[
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv witness.first)).val -
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv witness.second)).val]'(by
              have hedgeLength := SimpleGraph.Walk.length_edges
                (pair.suffixReversedSharedEdgeInterval witness.first
                  witness.second witness.suffix_order_reversed.le)
              have hinterLength :=
                pair.suffixReversedSharedEdgeInterval_length witness.first
                  witness.second witness.suffix_order_reversed.le
              omega) := by
      congr 1
      rw [pair.suffixReversedSharedEdgeInterval_length]
      omega
    _ = pair.suffixTrail.edges.get
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv witness.first)) := by
      exact pair.suffixTrail.edgeInterval_lastEdge
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv witness.second))
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv witness.first))
        ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
          witness.suffix_order_reversed.le)
    _ = pair.suffixSharedEdgeOrder.get
          (pair.sharedEdgeOrderEquiv witness.first) :=
      (pair.suffixSharedEdgePositionEmbedding_preserves_edge _).symm
    _ = pair.prefixSharedEdgeOrder.get witness.first :=
      pair.sharedEdgeOrderEquiv_preserves_edge witness.first
    _ = (pair.sharedEdgeAt witness.first).1 := rfl

/-- The complete prefix interval, interpreted as a path in the retained
line graph with its two physical profile edges as endpoints. -/
def LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.Walk
      (pair.sharedEdgeAt witness.first) (pair.sharedEdgeAt witness.second) :=
  let interval := pair.prefixSharedEdgeInterval witness.first
    witness.second witness.first_lt_second.le
  (interval.lineGraphWalkOfTrail
      (lt_of_lt_of_le Nat.zero_lt_two
        witness.two_le_prefix_interval_length)
      witness.prefix_interval_isPath.isTrail).copy
    witness.prefixLineStart_eq witness.prefixLineEnd_eq

/-- The complete suffix interval, reversed in the line graph so that it
has the same endpoint order as the prefix interval. -/
def LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.Walk
      (pair.sharedEdgeAt witness.first) (pair.sharedEdgeAt witness.second) :=
  let interval := pair.suffixReversedSharedEdgeInterval witness.first
    witness.second witness.suffix_order_reversed.le
  (interval.lineGraphWalkOfTrail
      (lt_of_lt_of_le Nat.zero_lt_two
        witness.two_le_suffix_interval_length)
      witness.suffix_interval_isPath.isTrail).reverse.copy
    witness.suffixLineEnd_eq witness.suffixLineStart_eq

/-- The prefix lift remains a path in the line graph. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.prefixLineGraphPath.IsPath := by
  rw [LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath,
    SimpleGraph.Walk.isPath_copy]
  exact SimpleGraph.Walk.lineGraphWalkOfTrail_isPath _ _
    witness.prefix_interval_isPath.isTrail

/-- The reversed suffix lift is also a path in the line graph. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath_isPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.suffixReverseLineGraphPath.IsPath := by
  rw [LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath,
    SimpleGraph.Walk.isPath_copy]
  apply SimpleGraph.Walk.IsPath.reverse
  exact SimpleGraph.Walk.lineGraphWalkOfTrail_isPath _ _
    witness.suffix_interval_isPath.isTrail

/-- Exact prefix line-graph length. -/
@[simp] theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.prefixLineGraphPath.length =
      (pair.prefixSharedEdgeInterval witness.first witness.second
        witness.first_lt_second.le).length - 1 := by
  simp [LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath]

/-- Exact reversed-suffix line-graph length. -/
@[simp] theorem LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.suffixReverseLineGraphPath.length =
      (pair.suffixReversedSharedEdgeInterval witness.first witness.second
        witness.suffix_order_reversed.le).length - 1 := by
  simp [LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath]

/-- The complete prefix lift follows the primal interval coherently. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_isPrimalCoherent
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.prefixLineGraphPath.IsPrimalCoherent := by
  rw [LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath]
  apply SimpleGraph.Walk.IsPrimalCoherent.copy
  exact SimpleGraph.Walk.lineGraphWalkOfTrail_isPrimalCoherent _ _
    witness.prefix_interval_isPath.isTrail

/-- The reversed suffix lift follows its primal interval coherently in
reverse order. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath_isPrimalCoherent
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.suffixReverseLineGraphPath.IsPrimalCoherent := by
  rw [LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath]
  apply SimpleGraph.Walk.IsPrimalCoherent.copy
  apply SimpleGraph.Walk.IsPrimalCoherent.reverse
  exact SimpleGraph.Walk.lineGraphWalkOfTrail_isPrimalCoherent _ _
    witness.suffix_interval_isPath.isTrail

/-- The first prefix-path junction is the target of the first selected
profile dart. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_firstJunction
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.prefixLineGraphPath.lineGraphJunctionAt
        ⟨0, by
          have htwo := witness.two_le_prefix_interval_length
          rw [witness.prefixLineGraphPath_length]
          omega⟩ =
      (pair.prefixSharedEdgeDart witness.first).snd := by
  unfold LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath
  rw [SimpleGraph.Walk.lineGraphJunctionAt_copy_at]
  rw [SimpleGraph.Walk.lineGraphWalkOfTrail_firstJunction _
    witness.two_le_prefix_interval_length]
  change
    (pair.prefixTrail.edgeInterval
      (pair.prefixSharedEdgePositionEmbedding witness.first)
      (pair.prefixSharedEdgePositionEmbedding witness.second)
      ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
        witness.first_lt_second.le)).getVert 1 =
      (pair.prefixTrail.dartAtEdgePosition
        (pair.prefixSharedEdgePositionEmbedding witness.first)).snd
  rw [SimpleGraph.Walk.edgeInterval_getVert]
  simp only [SimpleGraph.Walk.dartAtEdgePosition_snd]
  have hstrict :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      witness.first_lt_second
  omega

/-- The final prefix-path junction is the source of the second selected
profile dart. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_lastJunction
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.prefixLineGraphPath.lineGraphJunctionAt
        ⟨witness.prefixLineGraphPath.length - 1, by
          have htwo := witness.two_le_prefix_interval_length
          rw [witness.prefixLineGraphPath_length]
          omega⟩ =
      (pair.prefixSharedEdgeDart witness.second).fst := by
  unfold LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath
  rw [SimpleGraph.Walk.lineGraphJunctionAt_copy_at]
  simp only [SimpleGraph.Walk.length_copy]
  rw [SimpleGraph.Walk.lineGraphWalkOfTrail_lastJunction _
    witness.two_le_prefix_interval_length]
  change
    (pair.prefixTrail.edgeInterval
      (pair.prefixSharedEdgePositionEmbedding witness.first)
      (pair.prefixSharedEdgePositionEmbedding witness.second)
      ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
        witness.first_lt_second.le)).getVert
        ((pair.prefixTrail.edgeInterval
          (pair.prefixSharedEdgePositionEmbedding witness.first)
          (pair.prefixSharedEdgePositionEmbedding witness.second)
          ((pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
            witness.first_lt_second.le)).length - 1) =
      (pair.prefixTrail.dartAtEdgePosition
        (pair.prefixSharedEdgePositionEmbedding witness.second)).fst
  rw [SimpleGraph.Walk.edgeInterval_getVert]
  simp only [SimpleGraph.Walk.dartAtEdgePosition_fst]
  rw [SimpleGraph.Walk.edgeInterval_length]
  congr 1
  have hstrict :=
    (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      witness.first_lt_second
  omega
  all_goals
    simp only [SimpleGraph.Walk.edgeInterval_length]
    omega

/-- The first reversed-suffix junction is the source of the first
prefix-order selected dart. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath_firstJunction
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.suffixReverseLineGraphPath.lineGraphJunctionAt
        ⟨0, by
          have htwo := witness.two_le_suffix_interval_length
          rw [witness.suffixReverseLineGraphPath_length]
          omega⟩ =
      (pair.suffixSharedEdgeDart witness.first).fst := by
  unfold LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath
  rw [SimpleGraph.Walk.lineGraphJunctionAt_copy_at]
  rw [SimpleGraph.Walk.lineGraphJunctionAt_reverse_zero]
  rw [SimpleGraph.Walk.lineGraphWalkOfTrail_lastJunction _
    witness.two_le_suffix_interval_length]
  change
    (pair.suffixTrail.edgeInterval
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.second))
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.first))
      ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
        witness.suffix_order_reversed.le)).getVert
        ((pair.suffixTrail.edgeInterval
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv witness.second))
          (pair.suffixSharedEdgePositionEmbedding
            (pair.sharedEdgeOrderEquiv witness.first))
          ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
            witness.suffix_order_reversed.le)).length - 1) =
      (pair.suffixTrail.dartAtEdgePosition
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv witness.first))).fst
  rw [SimpleGraph.Walk.edgeInterval_getVert]
  simp only [SimpleGraph.Walk.dartAtEdgePosition_fst]
  rw [SimpleGraph.Walk.edgeInterval_length]
  congr 1
  have hstrict :=
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      witness.suffix_order_reversed
  omega
  all_goals
    have htwo := witness.two_le_suffix_interval_length
    have hintervalLength :=
      pair.suffixReversedSharedEdgeInterval_length witness.first
        witness.second witness.suffix_order_reversed.le
    have hrawIntervalLength := SimpleGraph.Walk.edgeInterval_length
      pair.suffixTrail
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.second))
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.first))
      ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
        witness.suffix_order_reversed.le)
    have hlineLength := SimpleGraph.Walk.lineGraphWalkOfTrail_length
      (pair.suffixReversedSharedEdgeInterval witness.first witness.second
        witness.suffix_order_reversed.le) (by omega)
      witness.suffix_interval_isPath.isTrail
    omega

/-- The final reversed-suffix junction is the target of the second
prefix-order selected dart. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath_lastJunction
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.suffixReverseLineGraphPath.lineGraphJunctionAt
        ⟨witness.suffixReverseLineGraphPath.length - 1, by
          have htwo := witness.two_le_suffix_interval_length
          rw [witness.suffixReverseLineGraphPath_length]
          omega⟩ =
      (pair.suffixSharedEdgeDart witness.second).snd := by
  unfold LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath
  rw [SimpleGraph.Walk.lineGraphJunctionAt_copy_at]
  simp only [SimpleGraph.Walk.length_copy]
  rw [SimpleGraph.Walk.lineGraphJunctionAt_reverse_last]
  rw [SimpleGraph.Walk.lineGraphWalkOfTrail_firstJunction _
    witness.two_le_suffix_interval_length]
  change
    (pair.suffixTrail.edgeInterval
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.second))
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.first))
      ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
        witness.suffix_order_reversed.le)).getVert 1 =
      (pair.suffixTrail.dartAtEdgePosition
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv witness.second))).snd
  rw [SimpleGraph.Walk.edgeInterval_getVert]
  simp only [SimpleGraph.Walk.dartAtEdgePosition_snd]
  have hstrict :=
    (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      witness.suffix_order_reversed
  omega
  all_goals
    have htwo := witness.two_le_suffix_interval_length
    have hintervalLength :=
      pair.suffixReversedSharedEdgeInterval_length witness.first
        witness.second witness.suffix_order_reversed.le
    have hrawIntervalLength := SimpleGraph.Walk.edgeInterval_length
      pair.suffixTrail
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.second))
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv witness.first))
      ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
        witness.suffix_order_reversed.le)
    have hlineLength := SimpleGraph.Walk.lineGraphWalkOfTrail_length
      (pair.suffixReversedSharedEdgeInterval witness.first witness.second
        witness.suffix_order_reversed.le) (by omega)
      witness.suffix_interval_isPath.isTrail
    omega

/-- The prefix line-graph path has exactly the complete primal interval as
its support. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_support_val
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.prefixLineGraphPath.support.map Subtype.val =
      (pair.prefixSharedEdgeInterval witness.first witness.second
        witness.first_lt_second.le).edges := by
  simp [LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath]
  exact SimpleGraph.Walk.edgeSubtypeSupport_unattach _

/-- The reversed suffix line-graph support is the reverse of the complete
suffix-order primal interval. -/
theorem LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath_support_val
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.suffixReverseLineGraphPath.support.map Subtype.val =
      (pair.suffixReversedSharedEdgeInterval witness.first witness.second
        witness.suffix_order_reversed.le).edges.reverse := by
  simp only [
    LocalizedSharedEdgePathIntervalInversion.suffixReverseLineGraphPath,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
    SimpleGraph.Walk.lineGraphWalkOfTrail_support]
  calc
    _ = ((pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edgeSubtypeSupport.map
            Subtype.val).reverse := by
      rw [List.map_reverse]
    _ = _ := congrArg List.reverse
      (SimpleGraph.Walk.edgeSubtypeSupport_map_val _)

/-- Close the two complete line-graph interval paths in opposite
directions. -/
def LocalizedSharedEdgePathIntervalInversion.closedLineGraphWalk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.Walk
      (pair.sharedEdgeAt witness.first) (pair.sharedEdgeAt witness.first) :=
  witness.prefixLineGraphPath.append
    witness.suffixReverseLineGraphPath.reverse

/-- Exact length of the closed two-interval line-graph walk. -/
@[simp] theorem LocalizedSharedEdgePathIntervalInversion.closedLineGraphWalk_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    witness.closedLineGraphWalk.length =
      (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).length +
        (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).length - 2 := by
  simp only [LocalizedSharedEdgePathIntervalInversion.closedLineGraphWalk,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    witness.prefixLineGraphPath_length,
    witness.suffixReverseLineGraphPath_length]
  have hprefixTwo := witness.two_le_prefix_interval_length
  have hsuffixTwo := witness.two_le_suffix_interval_length
  omega

/-- Positive chirality at both inversion endpoints closes the complete
two-interval walk primal-coherently. -/
theorem LocalizedSharedEdgePathIntervalInversion.closedLineGraphWalk_isPrimalCoherentClosed_of_endpointDarts_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face)
    (hfirstSame : pair.suffixSharedEdgeDart witness.first =
      pair.prefixSharedEdgeDart witness.first)
    (hsecondSame : pair.suffixSharedEdgeDart witness.second =
      pair.prefixSharedEdgeDart witness.second) :
    witness.closedLineGraphWalk.IsPrimalCoherentClosed := by
  have hprefixPositive : 0 < witness.prefixLineGraphPath.length := by
    rw [witness.prefixLineGraphPath_length]
    have htwo := witness.two_le_prefix_interval_length
    omega
  have hsuffixPositive : 0 < witness.suffixReverseLineGraphPath.length := by
    rw [witness.suffixReverseLineGraphPath_length]
    have htwo := witness.two_le_suffix_interval_length
    omega
  have hreversePositive :
      0 < witness.suffixReverseLineGraphPath.reverse.length := by
    simpa only [SimpleGraph.Walk.length_reverse] using hsuffixPositive
  have hseam :
      witness.prefixLineGraphPath.lineGraphJunctionAt
          ⟨witness.prefixLineGraphPath.length - 1,
            Nat.sub_lt hprefixPositive Nat.zero_lt_one⟩ ≠
        witness.suffixReverseLineGraphPath.reverse.lineGraphJunctionAt
          ⟨0, hreversePositive⟩ := by
    rw [witness.prefixLineGraphPath_lastJunction,
      witness.suffixReverseLineGraphPath.lineGraphJunctionAt_reverse_zero
        hsuffixPositive,
      witness.suffixReverseLineGraphPath_lastJunction, hsecondSame]
    exact (pair.prefixSharedEdgeDart witness.second).fst_ne_snd
  have hclosing :
      witness.suffixReverseLineGraphPath.reverse.lineGraphJunctionAt
          ⟨witness.suffixReverseLineGraphPath.reverse.length - 1,
            Nat.sub_lt hreversePositive Nat.zero_lt_one⟩ ≠
        witness.prefixLineGraphPath.lineGraphJunctionAt
          ⟨0, hprefixPositive⟩ := by
    rw [witness.suffixReverseLineGraphPath.lineGraphJunctionAt_reverse_last
        hsuffixPositive,
      witness.suffixReverseLineGraphPath_firstJunction,
      witness.prefixLineGraphPath_firstJunction, hfirstSame]
    exact (pair.prefixSharedEdgeDart witness.first).fst_ne_snd
  exact witness.prefixLineGraphPath_isPrimalCoherent.append_isPrimalCoherentClosed
    witness.suffixReverseLineGraphPath_isPrimalCoherent.reverse
    hprefixPositive hreversePositive hseam hclosing

/-- The primal output of a positive-chirality order inversion: an actual
cycle in the retained graph, two edges shorter than the combined source
intervals. -/
structure LocalizedOrderInversionPrimalCycle
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  inversion : LocalizedSharedEdgePathIntervalInversion pair oldCross face
  first_dart_same :
    pair.suffixSharedEdgeDart inversion.first =
      pair.prefixSharedEdgeDart inversion.first
  second_dart_same :
    pair.suffixSharedEdgeDart inversion.second =
      pair.prefixSharedEdgeDart inversion.second
  root : retainedVertexSet data.firstVertex data.secondVertex
  cycle : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk root root
  cycle_isCycle : cycle.IsCycle
  cycle_edges_subset_closedLineGraphWalk :
    cycle.edges ⊆
      inversion.closedLineGraphWalk.support.tail.map Subtype.val
  cycle_length_add_two_le :
    cycle.length + 2 ≤
      (pair.prefixSharedEdgeInterval inversion.first inversion.second
          inversion.first_lt_second.le).length +
        (pair.suffixReversedSharedEdgeInterval inversion.first inversion.second
          inversion.suffix_order_reversed.le).length

/-- Lift the coherent two-interval line-graph loop and extract its bounded
primal cycle. -/
theorem LocalizedSharedEdgePathIntervalInversion.exists_localizedOrderInversionPrimalCycle_of_endpointDarts_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face)
    (hfirstSame : pair.suffixSharedEdgeDart witness.first =
      pair.prefixSharedEdgeDart witness.first)
    (hsecondSame : pair.suffixSharedEdgeDart witness.second =
      pair.prefixSharedEdgeDart witness.second) :
    Nonempty (LocalizedOrderInversionPrimalCycle pair oldCross face) := by
  have hpositive : 0 < witness.closedLineGraphWalk.length := by
    rw [witness.closedLineGraphWalk_length]
    have hprefixTwo := witness.two_le_prefix_interval_length
    have hsuffixTwo := witness.two_le_suffix_interval_length
    omega
  have hcoherent :=
    witness.closedLineGraphWalk_isPrimalCoherentClosed_of_endpointDarts_eq
      hfirstSame hsecondSame
  rcases SimpleGraph.Walk.exists_primal_isCycle_length_le_edges_subset_of_primalCoherentClosed
      witness.closedLineGraphWalk hpositive hcoherent with
    ⟨root, cycle, hcycle, hlength, hsubset⟩
  exact ⟨{
    inversion := witness
    first_dart_same := hfirstSame
    second_dart_same := hsecondSame
    root := root
    cycle := cycle
    cycle_isCycle := hcycle
    cycle_edges_subset_closedLineGraphWalk := hsubset
    cycle_length_add_two_le := by
      rw [witness.closedLineGraphWalk_length] at hlength
      have hprefixTwo := witness.two_le_prefix_interval_length
      have hsuffixTwo := witness.two_le_suffix_interval_length
      omega }⟩

/-- The extracted cycle is a nonempty edge-simple primal circuit. -/
theorem LocalizedOrderInversionPrimalCycle.cycle_isCircuit
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedOrderInversionPrimalCycle pair oldCross face) :
    descent.cycle.IsCircuit :=
  descent.cycle_isCycle.isCircuit

/-- The interval saving is also strict against the two complete source
trails, which is the measure used by fusion-chain descent. -/
theorem LocalizedOrderInversionPrimalCycle.cycle_length_lt_sourceTrails
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedOrderInversionPrimalCycle pair oldCross face) :
    descent.cycle.length <
      pair.prefixTrail.length + pair.suffixTrail.length := by
  have hprefixLe :
      (pair.prefixSharedEdgeInterval descent.inversion.first
        descent.inversion.second
        descent.inversion.first_lt_second.le).length ≤
          pair.prefixTrail.length := by
    rw [pair.prefixSharedEdgeInterval_length]
    have hposition :=
      (pair.prefixSharedEdgePositionEmbedding
        descent.inversion.second).isLt
    have hlength := pair.prefixTrail.length_edges
    omega
  have hsuffixLe :
      (pair.suffixReversedSharedEdgeInterval descent.inversion.first
        descent.inversion.second
        descent.inversion.suffix_order_reversed.le).length ≤
          pair.suffixTrail.length := by
    rw [pair.suffixReversedSharedEdgeInterval_length]
    have hposition :=
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv descent.inversion.first)).isLt
    have hlength := pair.suffixTrail.length_edges
    omega
  have hsave := descent.cycle_length_add_two_le
  omega

/-- Every extracted cycle edge comes from one of the two inverted primal
intervals. -/
theorem LocalizedOrderInversionPrimalCycle.cycle_edges_subset_intervals
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedOrderInversionPrimalCycle pair oldCross face) :
    descent.cycle.edges ⊆
      (pair.prefixSharedEdgeInterval descent.inversion.first
        descent.inversion.second
        descent.inversion.first_lt_second.le).edges ++
      (pair.suffixReversedSharedEdgeInterval descent.inversion.first
        descent.inversion.second
        descent.inversion.suffix_order_reversed.le).edges := by
  intro edge hedge
  have hclosed := descent.cycle_edges_subset_closedLineGraphWalk hedge
  rw [LocalizedSharedEdgePathIntervalInversion.closedLineGraphWalk,
    SimpleGraph.Walk.tail_support_append, List.map_append,
    List.mem_append] at hclosed
  rcases hclosed with hprefix | hsuffix
  · apply List.mem_append_left
    rcases List.mem_map.mp hprefix with
      ⟨lineEdge, hlineEdge, hedge⟩
    have hprefixFull : edge ∈
        descent.inversion.prefixLineGraphPath.support.map Subtype.val :=
      List.mem_map.mpr
        ⟨lineEdge, List.mem_of_mem_tail hlineEdge, hedge⟩
    rw [descent.inversion.prefixLineGraphPath_support_val] at hprefixFull
    exact hprefixFull
  · apply List.mem_append_right
    rcases List.mem_map.mp hsuffix with
      ⟨lineEdge, hlineEdge, hedge⟩
    have hsuffixFull : edge ∈
        descent.inversion.suffixReverseLineGraphPath.reverse.support.map
          Subtype.val :=
      List.mem_map.mpr
        ⟨lineEdge, List.mem_of_mem_tail hlineEdge, hedge⟩
    rw [SimpleGraph.Walk.support_reverse, List.map_reverse,
      descent.inversion.suffixReverseLineGraphPath_support_val,
      List.reverse_reverse] at hsuffixFull
    exact hsuffixFull

/-- Hence the complete source trails contain every edge of the strict
primal circuit. -/
theorem LocalizedOrderInversionPrimalCycle.cycle_edges_subset_sourceTrails
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (descent : LocalizedOrderInversionPrimalCycle pair oldCross face) :
    descent.cycle.edges ⊆
      pair.prefixTrail.edges ++ pair.suffixTrail.edges := by
  have hprefixSubwalk :
      (pair.prefixSharedEdgeInterval descent.inversion.first
        descent.inversion.second
        descent.inversion.first_lt_second.le).IsSubwalk pair.prefixTrail := by
    exact pair.prefixTrail.edgeInterval_isSubwalk _ _ _
  have hsuffixSubwalk :
      (pair.suffixReversedSharedEdgeInterval descent.inversion.first
        descent.inversion.second
        descent.inversion.suffix_order_reversed.le).IsSubwalk
          pair.suffixTrail := by
    exact pair.suffixTrail.edgeInterval_isSubwalk _ _ _
  intro edge hedge
  rcases List.mem_append.mp
      (descent.cycle_edges_subset_intervals hedge) with
    hprefix | hsuffix
  · exact List.mem_append_left _ (hprefixSubwalk.edges_subset hprefix)
  · exact List.mem_append_right _ (hsuffixSubwalk.edges_subset hsuffix)

/-- Thus every order inversion is resolved either by a reversed-edge
splice or by a strictly bounded primal cycle. -/
theorem LocalizedSharedEdgePathIntervalInversion.exists_reversedSharedEdgeDart_or_localizedOrderInversionPrimalCycle
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    Nonempty (LocalizedReversedSharedEdgeDart pair oldCross face) ∨
      Nonempty (LocalizedOrderInversionPrimalCycle pair oldCross face) := by
  rcases pair.suffixSharedEdgeDart_eq_or_eq_prefix_symm witness.first with
    hfirstSame | hfirstReverse
  · rcases pair.suffixSharedEdgeDart_eq_or_eq_prefix_symm witness.second with
      hsecondSame | hsecondReverse
    · exact Or.inr
        (witness.exists_localizedOrderInversionPrimalCycle_of_endpointDarts_eq
          hfirstSame hsecondSame)
    · exact Or.inl ⟨{
        position := witness.second
        retained_reversed := hsecondReverse
        ambient_reversed :=
          pair.ambientSuffixSharedEdgeDart_eq_ambientPrefix_symm_of_suffixSharedEdgeDart_eq_prefix_symm
            witness.second hsecondReverse
        edge_ne_oldCross := witness.second_edge_ne_oldCross
        ambient_edge_mem_face := witness.second_ambient_edge_mem_face }⟩
  · exact Or.inl ⟨{
      position := witness.first
      retained_reversed := hfirstReverse
      ambient_reversed :=
        pair.ambientSuffixSharedEdgeDart_eq_ambientPrefix_symm_of_suffixSharedEdgeDart_eq_prefix_symm
          witness.first hfirstReverse
      edge_ne_oldCross := witness.first_edge_ne_oldCross
      ambient_edge_mem_face := witness.first_ambient_edge_mem_face }⟩

/-- If the first selected edge has positive chirality, the complete
prefix interval cannot equal the reversed complete suffix interval. -/
theorem LocalizedSharedEdgePathIntervalInversion.intervalEdges_ne_reverse_of_firstDart_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face)
    (hsame : pair.suffixSharedEdgeDart witness.first =
      pair.prefixSharedEdgeDart witness.first) :
    (pair.prefixSharedEdgeInterval witness.first witness.second
        witness.first_lt_second.le).edges ≠
      (pair.suffixReversedSharedEdgeInterval witness.first witness.second
        witness.suffix_order_reversed.le).edges.reverse := by
  let prefixFirst := pair.prefixSharedEdgePositionEmbedding witness.first
  let prefixSecond := pair.prefixSharedEdgePositionEmbedding witness.second
  let suffixSecond := pair.suffixSharedEdgePositionEmbedding
    (pair.sharedEdgeOrderEquiv witness.second)
  let suffixFirst := pair.suffixSharedEdgePositionEmbedding
    (pair.sharedEdgeOrderEquiv witness.first)
  have hprefixStrict : prefixFirst < prefixSecond := by
    exact (pair.prefixSharedEdgePositionEmbedding.lt_iff_lt).2
      witness.first_lt_second
  have hsuffixStrict : suffixSecond < suffixFirst := by
    exact (pair.suffixSharedEdgePositionEmbedding.lt_iff_lt).2
      witness.suffix_order_reversed
  have hprefixNext : prefixFirst.val + 1 < pair.prefixTrail.edges.length := by
    have hsecond := prefixSecond.isLt
    omega
  have hsuffixPrevious : 0 < suffixFirst.val := by
    omega
  have hsamePositions :
      pair.suffixTrail.dartAtEdgePosition suffixFirst =
        pair.prefixTrail.dartAtEdgePosition prefixFirst := by
    simpa only [RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart,
      RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart] using hsame
  have hneighborNe :=
    pair.prefixRetained_isTrail.nextEdge_ne_previousEdge_of_same_position_dart
      prefixFirst pair.suffixTrail suffixFirst hprefixNext hsuffixPrevious
      hsamePositions
  intro hintervals
  have hprefixTwo :
      2 ≤ (pair.prefixSharedEdgeInterval witness.first witness.second
        witness.first_lt_second.le).edges.length := by
    simpa only [SimpleGraph.Walk.length_edges] using
      witness.two_le_prefix_interval_length
  have hsuffixTwo :
      2 ≤ (pair.suffixReversedSharedEdgeInterval witness.first witness.second
        witness.suffix_order_reversed.le).edges.length := by
    simpa only [SimpleGraph.Walk.length_edges] using
      witness.two_le_suffix_interval_length
  have hintervalSecond := List.getElem_one_eq_penultimate_of_eq_reverse
    (pair.prefixSharedEdgeInterval witness.first witness.second
      witness.first_lt_second.le).edges
    (pair.suffixReversedSharedEdgeInterval witness.first witness.second
      witness.suffix_order_reversed.le).edges
    hprefixTwo hsuffixTwo hintervals
  apply hneighborNe
  calc
    pair.prefixTrail.edges[prefixFirst.val + 1]'hprefixNext =
        (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).edges[1]'(by omega) := by
      symm
      simpa only [
        RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval] using
        pair.prefixTrail.edgeInterval_secondEdge prefixFirst prefixSecond
          hprefixStrict
    _ = (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edges[
            (pair.suffixReversedSharedEdgeInterval witness.first witness.second
              witness.suffix_order_reversed.le).edges.length - 2]'(by omega) :=
      hintervalSecond
    _ = (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edges[
            suffixFirst.val - suffixSecond.val - 1]'(by
              have hedgeLength :=
                (pair.suffixReversedSharedEdgeInterval witness.first
                  witness.second witness.suffix_order_reversed.le).length_edges
              have hintervalLength :=
                pair.suffixReversedSharedEdgeInterval_length witness.first
                  witness.second witness.suffix_order_reversed.le
              omega) := by
      congr 1
      have hedgeLength :=
        (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).length_edges
      have hintervalLength :=
        pair.suffixReversedSharedEdgeInterval_length witness.first
          witness.second witness.suffix_order_reversed.le
      omega
    _ = pair.suffixTrail.edges[suffixFirst.val - 1]'(by
          have hfirst := suffixFirst.isLt
          omega) := by
      simpa only [
        RetainedIntersectionExactFaceCutPair.suffixReversedSharedEdgeInterval]
        using pair.suffixTrail.edgeInterval_penultimateEdge suffixSecond
          suffixFirst hsuffixStrict

/-- Positive chirality at the first inversion edge makes the two complete
line-graph interval paths distinct. -/
theorem LocalizedSharedEdgePathIntervalInversion.prefixLineGraphPath_ne_suffixReverseLineGraphPath
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face)
    (hsame : pair.suffixSharedEdgeDart witness.first =
      pair.prefixSharedEdgeDart witness.first) :
    witness.prefixLineGraphPath ≠ witness.suffixReverseLineGraphPath := by
  intro hpaths
  apply witness.intervalEdges_ne_reverse_of_firstDart_eq hsame
  calc
    (pair.prefixSharedEdgeInterval witness.first witness.second
          witness.first_lt_second.le).edges =
        witness.prefixLineGraphPath.support.map Subtype.val :=
      witness.prefixLineGraphPath_support_val.symm
    _ = witness.suffixReverseLineGraphPath.support.map Subtype.val :=
      congrArg (fun path => path.support.map Subtype.val) hpaths
    _ = (pair.suffixReversedSharedEdgeInterval witness.first witness.second
          witness.suffix_order_reversed.le).edges.reverse :=
      witness.suffixReverseLineGraphPath_support_val

/-- A localized order inversion therefore supplies a genuine retained
line-graph circuit unless one of its endpoint darts is reversed. -/
structure LocalizedOrderInversionLineGraphCircuit
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  inversion : LocalizedSharedEdgePathIntervalInversion pair oldCross face
  root : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet
  first_dart_same :
    pair.suffixSharedEdgeDart inversion.first =
      pair.prefixSharedEdgeDart inversion.first
  second_dart_same :
    pair.suffixSharedEdgeDart inversion.second =
      pair.prefixSharedEdgeDart inversion.second
  circuit :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).lineGraph.Walk
      root root
  root_mem_prefixPath : root ∈ inversion.prefixLineGraphPath.support
  root_mem_suffixReversePath :
    root ∈ inversion.suffixReverseLineGraphPath.support
  circuit_isCycle : circuit.IsCycle
  circuit_length_add_two_le :
    circuit.length + 2 ≤
      (pair.prefixSharedEdgeInterval inversion.first inversion.second
          inversion.first_lt_second.le).length +
        (pair.suffixReversedSharedEdgeInterval inversion.first inversion.second
          inversion.suffix_order_reversed.le).length

/-- Extract the bounded circuit from two distinct complete interval paths. -/
theorem LocalizedSharedEdgePathIntervalInversion.exists_localizedOrderInversionLineGraphCircuit_of_endpointDarts_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face)
    (hfirstSame : pair.suffixSharedEdgeDart witness.first =
      pair.prefixSharedEdgeDart witness.first)
    (hsecondSame : pair.suffixSharedEdgeDart witness.second =
      pair.prefixSharedEdgeDart witness.second) :
    Nonempty (LocalizedOrderInversionLineGraphCircuit pair oldCross face) := by
  rcases witness.prefixLineGraphPath_isPath.exists_isCycle_length_le_add_of_ne
      witness.suffixReverseLineGraphPath_isPath
      (witness.prefixLineGraphPath_ne_suffixReverseLineGraphPath hfirstSame) with
    ⟨root, hrootPrefix, hrootSuffix, circuit, hcycle, hlength⟩
  exact ⟨{
    inversion := witness
    root := root
    first_dart_same := hfirstSame
    second_dart_same := hsecondSame
    circuit := circuit
    root_mem_prefixPath := hrootPrefix
    root_mem_suffixReversePath := hrootSuffix
    circuit_isCycle := hcycle
    circuit_length_add_two_le := by
      rw [witness.prefixLineGraphPath_length,
        witness.suffixReverseLineGraphPath_length] at hlength
      have hprefixTwo := witness.two_le_prefix_interval_length
      have hsuffixTwo := witness.two_le_suffix_interval_length
      omega }⟩

/-- Every localized order inversion resolves either to the existing
reversed-dart splice descent or to a bounded line-graph circuit. -/
theorem LocalizedSharedEdgePathIntervalInversion.exists_reversedSharedEdgeDart_or_localizedOrderInversionLineGraphCircuit
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (witness : LocalizedSharedEdgePathIntervalInversion pair oldCross face) :
    Nonempty (LocalizedReversedSharedEdgeDart pair oldCross face) ∨
      Nonempty (LocalizedOrderInversionLineGraphCircuit pair oldCross face) := by
  rcases pair.suffixSharedEdgeDart_eq_or_eq_prefix_symm witness.first with
    hsame | hreverse
  · rcases pair.suffixSharedEdgeDart_eq_or_eq_prefix_symm witness.second with
      hsecondSame | hsecondReverse
    · exact Or.inr
        (witness.exists_localizedOrderInversionLineGraphCircuit_of_endpointDarts_eq
          hsame hsecondSame)
    · exact Or.inl ⟨{
        position := witness.second
        retained_reversed := hsecondReverse
        ambient_reversed :=
          pair.ambientSuffixSharedEdgeDart_eq_ambientPrefix_symm_of_suffixSharedEdgeDart_eq_prefix_symm
            witness.second hsecondReverse
        edge_ne_oldCross := witness.second_edge_ne_oldCross
        ambient_edge_mem_face := witness.second_ambient_edge_mem_face }⟩
  · exact Or.inl ⟨{
      position := witness.first
      retained_reversed := hreverse
      ambient_reversed :=
        pair.ambientSuffixSharedEdgeDart_eq_ambientPrefix_symm_of_suffixSharedEdgeDart_eq_prefix_symm
          witness.first hreverse
      edge_ne_oldCross := witness.first_edge_ne_oldCross
      ambient_edge_mem_face := witness.first_ambient_edge_mem_face }⟩

/-- Resolving both nonidentity branches leaves only strict mixed-cycle
descent or a localized bounded order-inversion circuit. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles_or_localizedOrderInversionLineGraphCircuit
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (hlocalized : ∀ edge ∈ pair.sharedEdges,
      edge ≠ oldCross ∧
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem face) :
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair oldCross face) ∨
      Nonempty (LocalizedOrderInversionLineGraphCircuit pair oldCross face) := by
  rcases pair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_strictlyShorterMixedPortCycles
      hprefixPath hsuffixPath oldCross face hlocalized with
    hidentity | hinversion | hshorter
  · exact Or.inl hidentity
  · rcases hinversion with ⟨witness⟩
    rcases witness.exists_reversedSharedEdgeDart_or_localizedOrderInversionLineGraphCircuit with
      hreversed | hcircuit
    · rcases hreversed with ⟨reversed⟩
      exact Or.inr (Or.inl
        ⟨reversed.toLocalizedStrictlyShorterMixedPortCycles⟩)
    · exact Or.inr (Or.inr hcircuit)
  · exact Or.inr (Or.inl hshorter)

/-- Resolving the order inversion in the primal graph leaves only identity,
strict mixed-cycle descent, or a bounded retained-graph cycle. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeSignedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles_or_localizedOrderInversionPrimalCycle
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hprefixPath : pair.prefixTrail.IsPath)
    (hsuffixPath : pair.suffixTrail.IsPath)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (hlocalized : ∀ edge ∈ pair.sharedEdges,
      edge ≠ oldCross ∧
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem face) :
    pair.sharedEdgeSignedMonodromy =
        Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool) ∨
      Nonempty (LocalizedStrictlyShorterMixedPortCycles pair oldCross face) ∨
      Nonempty (LocalizedOrderInversionPrimalCycle pair oldCross face) := by
  rcases pair.sharedEdgeSignedMonodromy_eq_refl_or_exists_localizedPathIntervalInversion_or_strictlyShorterMixedPortCycles
      hprefixPath hsuffixPath oldCross face hlocalized with
    hidentity | hinversion | hshorter
  · exact Or.inl hidentity
  · rcases hinversion with ⟨witness⟩
    rcases witness.exists_reversedSharedEdgeDart_or_localizedOrderInversionPrimalCycle with
      hreversed | hcycle
    · rcases hreversed with ⟨reversed⟩
      exact Or.inr (Or.inl
        ⟨reversed.toLocalizedStrictlyShorterMixedPortCycles⟩)
    · exact Or.inr (Or.inr hcycle)
  · exact Or.inr (Or.inl hshorter)

/-- A remote-face fusion has a finite localized successor profile whose
nonidentity outcomes are strict mixed-cycle descent or a bounded primal
cycle. -/
theorem CrossCentralExactFaceCutPair.exists_localizedSuccessorResolvedSignedProfileNormalForm
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hprefixAvoids : cross.1 ∉ prefixSuccessor.edges)
    (hprefixCycle :
      (data.oppositePortClosure prefixSuccessor).IsCycle)
    (hprefixSubset : (data.retainedWalkToAmbient prefixSuccessor).edges ⊆
      firstFusion.edges)
    (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hsuffixCycle :
      (data.alternateOppositePortClosure suffixSuccessor).IsCycle)
    (hsuffixSubset : (data.retainedWalkToAmbient suffixSuccessor).edges ⊆
      secondFusion.edges) :
    ∃ successorPair : RetainedIntersectionExactFaceCutPair graphData data,
      successorPair.prefixTrail = prefixSuccessor ∧
        successorPair.suffixTrail = suffixSuccessor ∧
        (∀ edge ∈ successorPair.sharedEdges,
          edge ≠ cross ∧
            retainedEdgeToAmbientEdge data edge ∈
              orbitFaceBoundary graphData.toRotationSystem face) ∧
        successorPair.sharedEdges.card ≤
          (orbitFaceBoundary graphData.toRotationSystem face).card ∧
        (successorPair.sharedEdgeSignedMonodromy =
            Equiv.refl
              (Fin successorPair.prefixSharedEdgeOrder.length × Bool) ∨
          Nonempty (LocalizedStrictlyShorterMixedPortCycles successorPair
            cross face) ∨
          Nonempty (LocalizedOrderInversionPrimalCycle successorPair
            cross face)) := by
  rcases pair.exists_localizedSuccessorSignedProfileNormalForm minimal face
      firstFusion hfirstSupport secondFusion hsecondSupport prefixSuccessor
      hprefixAvoids hprefixCycle hprefixSubset suffixSuccessor hsuffixCycle
      hsuffixSubset with
    ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth, _⟩
  have hprefixPath : successorPair.prefixTrail.IsPath := by
    rw [hprefixEq]
    exact data.isPath_of_oppositePortClosure_isCycle prefixSuccessor
      hprefixCycle
  have hsuffixPath : successorPair.suffixTrail.IsPath := by
    rw [hsuffixEq]
    exact data.isPath_of_alternateOppositePortClosure_isCycle suffixSuccessor
      hsuffixCycle
  exact ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth,
    successorPair.sharedEdgeSignedMonodromy_eq_refl_or_strictlyShorterMixedPortCycles_or_localizedOrderInversionPrimalCycle
      hprefixPath hsuffixPath cross face hlocalized⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
