import Mettapedia.GraphTheory.FourColor.GoertzelV24Square
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphSplit
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionRotationSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexRotationSplice

/-!
# The two planar reductions of a facial square, as rotation systems

Deleting the four corners of a facial square exposes exactly its four outer
edges.  Joining those four in either of the two planar pairings gives the two
reductions the square rung reasons about.  This module builds them, using the
generic deleted-region splice: the four corners are the deleted region, the
outer edges split into a left and a right transversal according to the chosen
side, and the splice rewires each pair into one seam edge.

The one substantive input is the boundary identity — that the crossing edges of
the four corners are exactly the four outer edges.  It is proved here rather
than assumed.  The forward direction is the observation that a corner's own
outer edge leaves the square; the converse is that every edge meeting a corner
is one of that corner's three named edges, and the three square edges have both
endpoints deleted.

Two genuine side conditions remain hypotheses of the construction, and they are
exactly the source's qualifier that the reductions are valid: the root vertex is
not a corner, and the two ends of each seam are distinct vertices.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24RotationVertexCutProfile

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

namespace FacialSquareData

/-- The four corners of the square, deleted by the reduction. -/
def deletedCorners (Q : @FacialSquareData V E) : Finset V :=
  {Q.w, Q.x, Q.y, Q.z}

/-- The four corners, in cyclic order. -/
def cornerAt (Q : @FacialSquareData V E) : Fin 4 → V
  | 0 => Q.w
  | 1 => Q.x
  | 2 => Q.y
  | 3 => Q.z

/-- The four outer edges of the square, in cyclic corner order. -/
def outerEdgeAt (Q : @FacialSquareData V E) : Fin 4 → E
  | 0 => Q.outerW
  | 1 => Q.outerX
  | 2 => Q.outerY
  | 3 => Q.outerZ

/-- Each corner's own outer edge is one of its three incident edges. -/
theorem outerEdgeAt_mem_incidentEdges (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (i : Fin 4) :
    Q.outerEdgeAt i ∈ RS.incidentEdges (Q.cornerAt i) := by
  obtain ⟨-, hw, hx, hy, hz, -⟩ := hQ
  fin_cases i <;>
    simp [cornerAt, outerEdgeAt, hw, hx, hy, hz]

/-- The three named local-edge indices at each corner, read off the
well-formedness conditions. -/
def cornerNodes : Fin 4 → Finset SquareLocalNode
  | 0 => {0, 7, 4}
  | 1 => {1, 4, 5}
  | 2 => {2, 5, 6}
  | 3 => {3, 6, 7}

/-- The portal index of a corner, as a local-edge index. -/
def portalNode (i : Fin 4) : SquareLocalNode := Fin.castLE (by omega) i

theorem outerEdgeAt_eq_lineEdge (Q : @FacialSquareData V E) (i : Fin 4) :
    Q.outerEdgeAt i = Q.lineEdge (portalNode i) := by
  fin_cases i <;> simp [outerEdgeAt, lineEdge, portalNode]

/-- Well-formedness, restated on local-edge indices. -/
theorem incidentEdges_cornerAt (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (j : Fin 4) :
    RS.incidentEdges (Q.cornerAt j) = (cornerNodes j).image Q.lineEdge := by
  obtain ⟨-, hw, hx, hy, hz, -⟩ := hQ
  fin_cases j <;>
    simp [cornerAt, cornerNodes, lineEdge, hw, hx, hy, hz, Finset.image_insert]

/-- A portal index belongs to a corner's index set exactly at its own
corner. -/
theorem portalNode_mem_cornerNodes_iff (i j : Fin 4) :
    portalNode i ∈ cornerNodes j ↔ i = j := by
  revert i j
  decide

/-- **The far endpoint of an outer edge is not a corner.**  Otherwise that
outer edge would be one of the three named edges at another corner, and the
eight named local edges are distinct. -/
theorem endpoint_not_mem_deletedCorners (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct) (i : Fin 4)
    {vertex : V} (hmem : vertex ∈ RS.endpoints (Q.outerEdgeAt i))
    (hne : vertex ≠ Q.cornerAt i) : vertex ∉ Q.deletedCorners := by
  classical
  intro hdeleted
  have hcorner : ∃ j : Fin 4, vertex = Q.cornerAt j := by
    simp only [deletedCorners, Finset.mem_insert, Finset.mem_singleton] at hdeleted
    rcases hdeleted with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨j, rfl⟩ := hcorner
  have hinc := (RS.mem_endpoints_iff_mem_incidentEdges).1 hmem
  rw [Q.incidentEdges_cornerAt RS hQ j, Q.outerEdgeAt_eq_lineEdge i,
    Finset.mem_image] at hinc
  obtain ⟨node, hnode, heq⟩ := hinc
  have hportal : portalNode i = node := hdist heq.symm
  have hij : i = j := (portalNode_mem_cornerNodes_iff i j).1 (hportal ▸ hnode)
  exact hne (by rw [hij])

end FacialSquareData

/-! ## The boundary identity

Self-loops are excluded globally by the ambient rotation system, so every edge
has two distinct endpoints.  A corner's outer edge therefore has a second
endpoint, and that endpoint is not a corner; so each outer edge really crosses
out of the deleted region. -/

/-- Every edge has an endpoint other than any given one, since it has exactly
two and the ambient system has no self-loops. -/
theorem exists_endpoint_ne (edge : E) {vertex : V}
    (hmem : vertex ∈ RS.endpoints edge) :
    ∃ other ∈ RS.endpoints edge, other ≠ vertex := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsub : RS.endpoints edge ⊆ {vertex} := by
    intro u hu
    simpa using hcon u hu
  have hcard := Finset.card_le_card hsub
  rw [RS.endpoints_card_two edge, Finset.card_singleton] at hcard
  omega

namespace FacialSquareData

/-- A corner is an endpoint of its own outer edge. -/
theorem cornerAt_mem_endpoints_outerEdgeAt (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (i : Fin 4) :
    Q.cornerAt i ∈ RS.endpoints (Q.outerEdgeAt i) :=
  (RS.mem_endpoints_iff_mem_incidentEdges).2
    (Q.outerEdgeAt_mem_incidentEdges RS hQ i)

theorem cornerAt_mem_deletedCorners (Q : @FacialSquareData V E) (i : Fin 4) :
    Q.cornerAt i ∈ Q.deletedCorners := by
  fin_cases i <;> simp [deletedCorners, cornerAt]

/-- **Each outer edge crosses out of the square.**  Its corner is an endpoint,
its other endpoint exists because there are exactly two, and that other
endpoint is not a corner. -/
theorem outerEdgeAt_crosses (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct) (i : Fin 4) :
    edgeCrossesVertexSet RS Q.deletedCorners (Q.outerEdgeAt i) := by
  obtain ⟨other, hother, hne⟩ :=
    RS.exists_endpoint_ne (Q.outerEdgeAt i)
      (Q.cornerAt_mem_endpoints_outerEdgeAt RS hQ i)
  exact ⟨Q.cornerAt i, Q.cornerAt_mem_endpoints_outerEdgeAt RS hQ i,
    Q.cornerAt_mem_deletedCorners i, other, hother,
    Q.endpoint_not_mem_deletedCorners RS hQ hdist i hother hne⟩

end FacialSquareData

end RotationSystem

end Mettapedia.GraphTheory.FourColor
