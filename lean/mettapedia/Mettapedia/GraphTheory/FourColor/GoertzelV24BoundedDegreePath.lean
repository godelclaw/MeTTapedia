import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.FaceIncidence

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundedDegreePath

open SimpleGraph

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-- Vertices reachable from `root` in at most `radius` closed-neighborhood
steps. The closed step permits waiting at a vertex, so this is convenient for
uniform upper bounds on walks of any shorter length. -/
def boundedReach (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (root : Vertex) : Nat → Finset Vertex
  | 0 => {root}
  | radius + 1 =>
      (boundedReach G root radius).biUnion fun vertex =>
        insert vertex (G.neighborFinset vertex)

@[simp]
theorem boundedReach_zero (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (root : Vertex) :
    boundedReach G root 0 = {root} :=
  rfl

@[simp]
theorem boundedReach_succ (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (root : Vertex) (radius : Nat) :
    boundedReach G root (radius + 1) =
      (boundedReach G root radius).biUnion fun vertex =>
        insert vertex (G.neighborFinset vertex) :=
  rfl

theorem card_closedNeighborFinset_le
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (degreeBound : Nat) (hdegree : ∀ vertex, G.degree vertex ≤ degreeBound)
    (vertex : Vertex) :
    (insert vertex (G.neighborFinset vertex)).card ≤ degreeBound + 1 := by
  calc
    (insert vertex (G.neighborFinset vertex)).card ≤
        (G.neighborFinset vertex).card + 1 :=
      Finset.card_insert_le _ _
    _ = G.degree vertex + 1 := by
      rw [G.card_neighborFinset_eq_degree]
    _ ≤ degreeBound + 1 := Nat.add_le_add_right (hdegree vertex) 1

/-- A closed radius-`r` reach set in a graph of degree at most `Δ` has at
most `(Δ+1)^r` vertices. This deliberately loose bound avoids any tree or
planarity assumption and is sufficient for the v24 bulk extraction. -/
theorem card_boundedReach_le_pow
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (degreeBound : Nat) (hdegree : ∀ vertex, G.degree vertex ≤ degreeBound)
    (root : Vertex) : ∀ radius,
    (boundedReach G root radius).card ≤ (degreeBound + 1) ^ radius := by
  intro radius
  induction radius with
  | zero => simp
  | succ radius ih =>
      rw [boundedReach_succ]
      calc
        ((boundedReach G root radius).biUnion fun vertex =>
            insert vertex (G.neighborFinset vertex)).card ≤
            (boundedReach G root radius).card * (degreeBound + 1) :=
          Finset.card_biUnion_le_card_mul _ _ _ fun vertex _ =>
            card_closedNeighborFinset_le G degreeBound hdegree vertex
        _ ≤ (degreeBound + 1) ^ radius * (degreeBound + 1) :=
          Nat.mul_le_mul_right (degreeBound + 1) ih
        _ = (degreeBound + 1) ^ (radius + 1) := by
          rw [pow_succ]

/-- The endpoint of a walk of length at most `radius` belongs to the closed
reach set of that radius. -/
theorem endpoint_mem_boundedReach_of_walk_length_le
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    {root endpoint : Vertex} (walk : G.Walk root endpoint) :
    ∀ {radius : Nat}, walk.length ≤ radius →
      endpoint ∈ boundedReach G root radius := by
  intro radius hlength
  induction radius generalizing endpoint with
  | zero =>
      have hzero : walk.length = 0 := Nat.eq_zero_of_le_zero hlength
      have hend : root = endpoint := walk.eq_of_length_eq_zero hzero
      subst endpoint
      simp
  | succ radius ih =>
      rw [boundedReach_succ, Finset.mem_biUnion]
      by_cases hshort : walk.length ≤ radius
      · exact ⟨endpoint, ih walk hshort, by simp⟩
      · have hnonempty : ¬ walk.Nil := by
          intro hnil
          apply hshort
          rw [hnil.length_eq_zero]
          exact Nat.zero_le radius
        have hdropLength : walk.dropLast.length ≤ radius := by
          rw [walk.length_dropLast]
          omega
        refine ⟨walk.penultimate, ih walk.dropLast hdropLength, ?_⟩
        simp [walk.adj_penultimate hnonempty]

/-- Quantitative long-axis lemma for the v24 bulk step. A connected finite
graph of maximum degree at most `Δ`, with more than `(Δ+1)^L` vertices,
contains a geodesic path of length at least `L`. Applied to an all-hexagonal
component of the facial dual, this supplies the candidate corridor axis; the
remaining local geometric theorem must expose its induced primal ladder. -/
theorem exists_geodesicPath_length_ge_of_pow_lt_card
    (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (hconnected : G.Connected)
    (degreeBound pathLength : Nat)
    (hdegree : ∀ vertex, G.degree vertex ≤ degreeBound)
    (hlarge : (degreeBound + 1) ^ pathLength < Fintype.card Vertex) :
    ∃ start finish : Vertex, ∃ path : G.Walk start finish,
      path.IsPath ∧ path.length = G.dist start finish ∧
        pathLength ≤ path.length := by
  let root : Vertex := Classical.choice hconnected.nonempty
  by_contra hnoPath
  push Not at hnoPath
  have hall : (Finset.univ : Finset Vertex) ⊆
      boundedReach G root pathLength := by
    intro finish _
    obtain ⟨path, hpath, hgeodesic⟩ :=
      hconnected.exists_path_of_dist root finish
    have hpathLength : path.length < pathLength :=
      hnoPath root finish path hpath hgeodesic
    exact endpoint_mem_boundedReach_of_walk_length_le G path
      (Nat.le_of_lt hpathLength)
  have hunivCard : Fintype.card Vertex ≤
      (boundedReach G root pathLength).card := by
    simpa using Finset.card_le_card hall
  have hreachCard := card_boundedReach_le_pow
    G degreeBound hdegree root pathLength
  omega

section FaceIncidence

variable {Face Edge : Type*} [Fintype Face] [DecidableEq Face]
  [Fintype Edge] [DecidableEq Edge]

omit [Fintype Face] [DecidableEq Face] [Fintype Edge] in
/-- In a face-incidence model with at most two faces per edge, the degree of
a face in the interior dual is at most the number of edges on its boundary.
The proof injects every neighboring face into a shared boundary edge; the
two-face incidence bound makes that injection faithful. -/
theorem interiorDualGraph_degree_le_faceBoundary_card
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    [DecidableRel (interiorDualGraph faceBoundary allFaces).Adj]
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (face : AmbientFace allFaces) :
    (interiorDualGraph faceBoundary allFaces).degree face ≤
      (faceBoundary face.1).card := by
  classical
  let dual := interiorDualGraph faceBoundary allFaces
  let witnessEdge : dual.neighborSet face →
      {edge // edge ∈ faceBoundary face.1} := fun neighbor => by
    let edge := Classical.choose
      (exists_mem_sharedInteriorEdges_of_adj
        faceBoundary allFaces neighbor.property)
    exact ⟨edge,
      (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
        (Classical.choose_spec
          (exists_mem_sharedInteriorEdges_of_adj
            faceBoundary allFaces neighbor.property)) |>.2.1⟩
  have hinjective : Function.Injective witnessEdge := by
    intro left right hedges
    have hleftEdge := Classical.choose_spec
      (exists_mem_sharedInteriorEdges_of_adj
        faceBoundary allFaces left.property)
    have hrightEdge := Classical.choose_spec
      (exists_mem_sharedInteriorEdges_of_adj
        faceBoundary allFaces right.property)
    have hleftData :=
      (mem_sharedInteriorEdges_iff faceBoundary allFaces).1 hleftEdge
    have hrightData :=
      (mem_sharedInteriorEdges_iff faceBoundary allFaces).1 hrightEdge
    have hedgeEq : Classical.choose
          (exists_mem_sharedInteriorEdges_of_adj
            faceBoundary allFaces left.property) =
        Classical.choose
          (exists_mem_sharedInteriorEdges_of_adj
            faceBoundary allFaces right.property) :=
      congrArg Subtype.val hedges
    have hfaceLeft : face.1 ≠ left.1.1 :=
      (interiorDualGraph_adj_iff faceBoundary allFaces).1
        left.property |>.1
    have hfaceRight : face.1 ≠ right.1.1 :=
      (interiorDualGraph_adj_iff faceBoundary allFaces).1
        right.property |>.1
    have hrightAtLeftEdge : Classical.choose
          (exists_mem_sharedInteriorEdges_of_adj
            faceBoundary allFaces left.property) ∈
        faceBoundary right.1.1 := by
      rw [hedgeEq]
      exact hrightData.2.2
    have hrightEq :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces hincidence
        face.2 left.1.2 right.1.2 hfaceLeft
        hleftData.2.1 hleftData.2.2 hrightAtLeftEdge
    apply Subtype.ext
    apply Subtype.ext
    rcases hrightEq with hrightFace | hrightLeft
    · exact False.elim (hfaceRight hrightFace.symm)
    · exact hrightLeft.symm
  calc
    dual.degree face = Fintype.card (dual.neighborSet face) := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
    _ ≤ Fintype.card {edge // edge ∈ faceBoundary face.1} :=
      Fintype.card_le_of_injective witnessEdge hinjective
    _ = (faceBoundary face.1).card := by simp

omit [Fintype Face] [Fintype Edge] in
/-- Face-incidence specialization of the v24 long-axis extraction. Any
connected patch whose face boundaries have at most six edges and whose edge
incidences are at most two contains a geodesic dual path of length `L` once
the patch has more than `7^L` faces. -/
theorem interiorDualGraph_exists_geodesicPath_length_ge_of_seven_pow_lt
    (faceBoundary : Face → Finset Edge) (allFaces : Finset Face)
    (hincidence : ∀ edge,
      totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    (hfaceSize : ∀ face ∈ allFaces, (faceBoundary face).card ≤ 6)
    (hconnected : (interiorDualGraph faceBoundary allFaces).Connected)
    (pathLength : Nat) (hlarge : 7 ^ pathLength < allFaces.card) :
    ∃ start finish : AmbientFace allFaces,
      ∃ path : (interiorDualGraph faceBoundary allFaces).Walk start finish,
        path.IsPath ∧
          path.length =
            (interiorDualGraph faceBoundary allFaces).dist start finish ∧
          pathLength ≤ path.length := by
  classical
  apply exists_geodesicPath_length_ge_of_pow_lt_card
    (interiorDualGraph faceBoundary allFaces) hconnected 6 pathLength
  · intro face
    exact (interiorDualGraph_degree_le_faceBoundary_card
      faceBoundary allFaces hincidence face).trans
        (hfaceSize face.1 face.2)
  · simpa using hlarge

end FaceIncidence

end GoertzelV24BoundedDegreePath

end Mettapedia.GraphTheory.FourColor
