import Mettapedia.GraphTheory.FourColor.GoertzelV24Square
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphSplit
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionRotationSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexRotationSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexTaitSplice

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

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RetainedVertexTaitSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
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

/-! ## The corners are distinct, and square edges cross nothing -/

private theorem card_pair_le (a b : V) : ({a, b} : Finset V).card ≤ 2 := by
  classical
  exact le_trans (Finset.card_insert_le _ _) (by simp)

private theorem card_triple_le (a b c : V) : ({a, b, c} : Finset V).card ≤ 3 := by
  classical
  refine le_trans (Finset.card_insert_le _ _) ?_
  have := card_pair_le b c
  omega

/-- The well-formed cardinality condition, unpacked. -/
theorem corners_nodup (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS) :
    Q.w ∉ ({Q.x, Q.y, Q.z} : Finset V) ∧
      Q.x ∉ ({Q.y, Q.z} : Finset V) ∧ Q.y ≠ Q.z := by
  classical
  have hcard : ({Q.w, Q.x, Q.y, Q.z} : Finset V).card = 4 := hQ.1
  have hw : Q.w ∉ ({Q.x, Q.y, Q.z} : Finset V) := by
    intro hmem
    rw [Finset.insert_eq_self.2 hmem] at hcard
    have := card_triple_le (V := V) Q.x Q.y Q.z
    omega
  rw [Finset.card_insert_of_notMem hw] at hcard
  have hx : Q.x ∉ ({Q.y, Q.z} : Finset V) := by
    intro hmem
    rw [Finset.insert_eq_self.2 hmem] at hcard
    have := card_pair_le (V := V) Q.y Q.z
    omega
  rw [Finset.card_insert_of_notMem hx] at hcard
  refine ⟨hw, hx, ?_⟩
  intro hyz
  rw [hyz, Finset.insert_eq_self.2 (Finset.mem_singleton_self _)] at hcard
  simp at hcard

/-- The four corners are pairwise distinct. -/
theorem cornerAt_injective (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS) :
    Function.Injective Q.cornerAt := by
  obtain ⟨hw, hx, hyz⟩ := Q.corners_nodup RS hQ
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw hx
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cornerAt]

/-- A corner is an endpoint of each of its three named edges. -/
theorem cornerAt_mem_endpoints_lineEdge (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) {node : SquareLocalNode} {i : Fin 4}
    (hnode : node ∈ cornerNodes i) :
    Q.cornerAt i ∈ RS.endpoints (Q.lineEdge node) := by
  refine (RS.mem_endpoints_iff_mem_incidentEdges).2 ?_
  rw [Q.incidentEdges_cornerAt RS hQ i]
  exact Finset.mem_image_of_mem _ hnode

/-- An edge named at two distinct corners has exactly those two corners as its
endpoints. -/
theorem endpoints_lineEdge_eq_pair (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) {node : SquareLocalNode} {i j : Fin 4} (hij : i ≠ j)
    (hi : node ∈ cornerNodes i) (hj : node ∈ cornerNodes j) :
    RS.endpoints (Q.lineEdge node) = {Q.cornerAt i, Q.cornerAt j} := by
  classical
  have hne : Q.cornerAt i ≠ Q.cornerAt j := fun h =>
    hij (Q.cornerAt_injective RS hQ h)
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Q.cornerAt_mem_endpoints_lineEdge RS hQ hi
    · exact Q.cornerAt_mem_endpoints_lineEdge RS hQ hj
  · rw [RS.endpoints_card_two, Finset.card_pair hne]

/-- **A square edge crosses nothing.**  Both of its endpoints are corners. -/
theorem squareNode_not_crosses (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) {node : SquareLocalNode} (hnode : 4 ≤ node.val) :
    ¬ edgeCrossesVertexSet RS Q.deletedCorners (Q.lineEdge node) := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ :
      ∃ i j : Fin 4, i ≠ j ∧ node ∈ cornerNodes i ∧ node ∈ cornerNodes j := by
    fin_cases node <;> simp_all <;>
      first
        | exact ⟨0, 1, by decide, by decide, by decide⟩
        | exact ⟨1, 2, by decide, by decide, by decide⟩
        | exact ⟨2, 3, by decide, by decide, by decide⟩
        | exact ⟨3, 0, by decide, by decide, by decide⟩
  rintro ⟨inner, -, -, outer, houter, houterOut⟩
  rw [Q.endpoints_lineEdge_eq_pair RS hQ hij hi hj] at houter
  simp only [Finset.mem_insert, Finset.mem_singleton] at houter
  rcases houter with rfl | rfl
  · exact houterOut (Q.cornerAt_mem_deletedCorners i)
  · exact houterOut (Q.cornerAt_mem_deletedCorners j)

/-- A low-index named edge is the outer edge of its own corner. -/
theorem lineEdge_eq_outerEdgeAt (Q : @FacialSquareData V E)
    {node : SquareLocalNode} (hnode : node.val < 4) :
    Q.lineEdge node = Q.outerEdgeAt ⟨node.val, hnode⟩ := by
  rw [Q.outerEdgeAt_eq_lineEdge]
  congr 1

/-- **The boundary identity.**  The crossing edges of the four corners are
exactly the four outer edges.  One direction is that every outer edge leaves
the square; the other is that any crossing edge meets a corner, hence is one of
that corner's three named edges, and the two square edges there cross
nothing. -/
theorem vertexSetCrossingEdges_deletedCorners (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct) :
    vertexSetCrossingEdges RS Q.deletedCorners =
      Finset.image Q.outerEdgeAt Finset.univ := by
  classical
  ext edge
  rw [mem_vertexSetCrossingEdges_iff, Finset.mem_image]
  constructor
  · rintro ⟨inner, hinner, hinnerDeleted, outer, houter, houterOut⟩
    have hcorner : ∃ j : Fin 4, inner = Q.cornerAt j := by
      simp only [deletedCorners, Finset.mem_insert,
        Finset.mem_singleton] at hinnerDeleted
      rcases hinnerDeleted with h | h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    obtain ⟨j, rfl⟩ := hcorner
    have hinc := (RS.mem_endpoints_iff_mem_incidentEdges).1 hinner
    rw [Q.incidentEdges_cornerAt RS hQ j, Finset.mem_image] at hinc
    obtain ⟨node, -, rfl⟩ := hinc
    by_cases hlow : node.val < 4
    · exact ⟨⟨node.val, hlow⟩, Finset.mem_univ _,
        (Q.lineEdge_eq_outerEdgeAt hlow).symm⟩
    · exact absurd ⟨Q.cornerAt j, hinner, Q.cornerAt_mem_deletedCorners j,
        outer, houter, houterOut⟩
        (Q.squareNode_not_crosses RS hQ (by omega))
  · rintro ⟨i, -, rfl⟩
    exact Q.outerEdgeAt_crosses RS hQ hdist i

/-! ## The two transversals of each planar reduction -/

theorem outerEdgeAt_injective (Q : @FacialSquareData V E)
    (hdist : Q.LocalEdgesDistinct) : Function.Injective Q.outerEdgeAt := by
  intro i j hij
  rw [Q.outerEdgeAt_eq_lineEdge, Q.outerEdgeAt_eq_lineEdge] at hij
  have hnode := hdist hij
  exact Fin.ext (by simpa [portalNode] using congrArg Fin.val hnode)

/-- The corner portals joined on the left of each planar reduction. -/
def leftPortal : SquareReductionSide → Fin 2 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 2
  | 1, 0 => 1
  | 1, 1 => 3

/-- The corner portals joined on the right of each planar reduction. -/
def rightPortal : SquareReductionSide → Fin 2 → Fin 4
  | 0, 0 => 1
  | 0, 1 => 3
  | 1, 0 => 2
  | 1, 1 => 0

def leftCrossingAt (Q : @FacialSquareData V E) (side : SquareReductionSide) :
    Fin 2 → E := fun step => Q.outerEdgeAt (leftPortal side step)

def rightCrossingAt (Q : @FacialSquareData V E) (side : SquareReductionSide) :
    Fin 2 → E := fun step => Q.outerEdgeAt (rightPortal side step)

theorem leftPortal_injective (side : SquareReductionSide) :
    Function.Injective (leftPortal side) := by
  revert side
  decide

theorem rightPortal_injective (side : SquareReductionSide) :
    Function.Injective (rightPortal side) := by
  revert side
  decide

/-- The two transversals together use every corner portal exactly once. -/
theorem portalImages_union (side : SquareReductionSide) :
    (Finset.image (leftPortal side) Finset.univ ∪
        Finset.image (rightPortal side) Finset.univ) =
      (Finset.univ : Finset (Fin 4)) := by
  revert side
  decide

theorem leftPortal_ne_rightPortal (side : SquareReductionSide) (s t : Fin 2) :
    leftPortal side s ≠ rightPortal side t := by
  revert side s t
  decide

theorem portalImages_disjoint (side : SquareReductionSide) :
    Disjoint (Finset.image (leftPortal side) Finset.univ)
      (Finset.image (rightPortal side) Finset.univ) := by
  revert side
  decide

theorem leftCrossingAt_injective (Q : @FacialSquareData V E)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) :
    Function.Injective (Q.leftCrossingAt side) :=
  (Q.outerEdgeAt_injective hdist).comp (leftPortal_injective side)

theorem rightCrossingAt_injective (Q : @FacialSquareData V E)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) :
    Function.Injective (Q.rightCrossingAt side) :=
  (Q.outerEdgeAt_injective hdist).comp (rightPortal_injective side)

/-- **The two transversals cover exactly the crossing edges.**  This is the
substantive input the generic deleted-region splice asks for. -/
theorem orderedCut_union_eq_crossingEdges (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct)
    (side : SquareReductionSide) :
    orderedCut (Q.leftCrossingAt side) ∪ orderedCut (Q.rightCrossingAt side) =
      vertexSetCrossingEdges RS Q.deletedCorners := by
  classical
  rw [Q.vertexSetCrossingEdges_deletedCorners RS hQ hdist]
  unfold orderedCut leftCrossingAt rightCrossingAt
  ext edge
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨step, rfl⟩ | ⟨step, rfl⟩)
    · exact ⟨leftPortal side step, rfl⟩
    · exact ⟨rightPortal side step, rfl⟩
  · rintro ⟨i, rfl⟩
    have hi : i ∈ Finset.image (leftPortal side) Finset.univ ∪
        Finset.image (rightPortal side) Finset.univ := by
      rw [portalImages_union side]
      exact Finset.mem_univ i
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hi
    rcases hi with ⟨step, hstep⟩ | ⟨step, hstep⟩
    · exact Or.inl ⟨step, by rw [hstep]⟩
    · exact Or.inr ⟨step, by rw [hstep]⟩

/-- The two transversals are disjoint. -/
theorem orderedCut_disjoint (Q : @FacialSquareData V E)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) :
    Disjoint (orderedCut (Q.leftCrossingAt side))
      (orderedCut (Q.rightCrossingAt side)) := by
  classical
  unfold orderedCut leftCrossingAt rightCrossingAt
  rw [Finset.disjoint_left]
  rintro edge hleft hright
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hleft hright
  obtain ⟨step, hstep⟩ := hleft
  obtain ⟨other, hother⟩ := hright
  exact leftPortal_ne_rightPortal side step other
    (Q.outerEdgeAt_injective hdist (hstep.trans hother.symm))

/-! ## The reduction rotation system

With the boundary identity in hand the generic splice applies.  Its two
remaining hypotheses are the source's reduction-validity qualifiers and are
carried as arguments: the root vertex is not a corner, and the two ends of each
seam are distinct vertices. -/

/-- Outward orientations of the left transversal. -/
theorem leftCrosses (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) :
    ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = Q.leftCrossingAt side step ∧
      deletedRegionKeep Q.deletedCorners (RS.vertOf dart) ∧
      ¬ deletedRegionKeep Q.deletedCorners (RS.vertOf (RS.alpha dart)) :=
  fun step => leftCrossing_outward RS Q.deletedCorners _ _
    (Q.orderedCut_union_eq_crossingEdges RS hQ hdist side) step

/-- Outward orientations of the right transversal. -/
theorem rightCrosses (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) :
    ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = Q.rightCrossingAt side step ∧
      deletedRegionKeep Q.deletedCorners (RS.vertOf dart) ∧
      ¬ deletedRegionKeep Q.deletedCorners (RS.vertOf (RS.alpha dart)) :=
  fun step => rightCrossing_outward RS Q.deletedCorners _ _
    (Q.orderedCut_union_eq_crossingEdges RS hQ hdist side) step

/-- Every boundary dart of the deleted region lies on one of the two
transversals. -/
theorem boundaryCover (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) :
    ∀ dart : BoundaryDart RS (deletedRegionKeep Q.deletedCorners),
      RS.edgeOf dart.1.1 ∈ orderedCut (Q.leftCrossingAt side) ∨
        RS.edgeOf dart.1.1 ∈ orderedCut (Q.rightCrossingAt side) :=
  fun dart => deletedRegionBoundaryCover RS Q.deletedCorners _ _
    (Q.orderedCut_union_eq_crossingEdges RS hQ hdist side) dart

/-- **The root qualifier.**  The ambient root vertex is not a corner of the
square. -/
def RootRetained (Q : @FacialSquareData V E) : Prop :=
  deletedRegionKeep Q.deletedCorners (RS.vertOf RS.outer)

/-- **The seam qualifier.**  The two ends of each seam are distinct vertices,
so joining them creates no loop. -/
def SeamEndpointsDistinct (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct) (side : SquareReductionSide) : Prop :=
  ∀ step : Fin 2,
    RS.vertOf (orderedBoundaryDart RS (deletedRegionKeep Q.deletedCorners)
        (Q.leftCrossingAt side) (Q.leftCrosses RS hQ hdist side) step).1.1.1 ≠
      RS.vertOf (orderedBoundaryDart RS (deletedRegionKeep Q.deletedCorners)
        (Q.rightCrossingAt side) (Q.rightCrosses RS hQ hdist side) step).1.1.1

/-- **The planar reduction of a facial square, as a rotation system.**  The
four corners are deleted and the four outer edges are rejoined in the chosen
planar pairing. -/
noncomputable def reductionRotationSystem (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct)
    (side : SquareReductionSide) (hroot : Q.RootRetained RS)
    (hseam : Q.SeamEndpointsDistinct RS hQ hdist side) :=
  orderedCutRetainedVertexRotationSystem RS
    (deletedRegionKeep Q.deletedCorners)
    (Q.leftCrossingAt side) (Q.rightCrossingAt side)
    (Q.leftCrosses RS hQ hdist side) (Q.rightCrosses RS hQ hdist side)
    (Q.leftCrossingAt_injective hdist side)
    (Q.rightCrossingAt_injective hdist side)
    (Q.boundaryCover RS hQ hdist side)
    (Q.orderedCut_disjoint hdist side)
    hroot hseam

/-! ## The induced colouring projection

A colouring of the ambient map descends to the reduction exactly when the two
outer edges joined by each seam already carry the same colour — that is, when
the square's boundary word is compatible with the chosen side.  The descent
itself is the generic retained-vertex Tait splice. -/

/-- The ambient colouring is compatible with a side when each seam's two outer
edges agree. -/
def CompatibleWithSide (Q : @FacialSquareData V E) (side : SquareReductionSide)
    (C : RS.EdgeColoring Color) : Prop :=
  ∀ step : Fin 2,
    C (Q.leftCrossingAt side step) = C (Q.rightCrossingAt side step)

/-- **The induced colouring of a planar reduction.** -/
noncomputable def reductionColoring (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct)
    (side : SquareReductionSide) (hroot : Q.RootRetained RS)
    (hseam : Q.SeamEndpointsDistinct RS hQ hdist side)
    (C : RS.EdgeColoring Color) (hcut : Q.CompatibleWithSide RS side C) :
    (Q.reductionRotationSystem RS hQ hdist side hroot hseam).EdgeColoring
      Color :=
  orderedCutRetainedVertexSplicedColoring RS
    (deletedRegionKeep Q.deletedCorners)
    (Q.leftCrossingAt side) (Q.rightCrossingAt side)
    (Q.leftCrosses RS hQ hdist side) (Q.rightCrosses RS hQ hdist side)
    (Q.leftCrossingAt_injective hdist side)
    (Q.rightCrossingAt_injective hdist side)
    (Q.boundaryCover RS hQ hdist side)
    (Q.orderedCut_disjoint hdist side)
    hroot hseam C hcut

/-- **The induced colouring is a Tait colouring.** -/
theorem reductionColoring_isTait (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct)
    (side : SquareReductionSide) (hroot : Q.RootRetained RS)
    (hseam : Q.SeamEndpointsDistinct RS hQ hdist side)
    (C : RS.EdgeColoring Color) (hcut : Q.CompatibleWithSide RS side C)
    (hC : RS.IsTaitEdgeColoring C) :
    (Q.reductionRotationSystem RS hQ hdist side hroot hseam).IsTaitEdgeColoring
      (Q.reductionColoring RS hQ hdist side hroot hseam C hcut) :=
  orderedCutRetainedVertexSplicedColoring_isTait RS
    (deletedRegionKeep Q.deletedCorners)
    (Q.leftCrossingAt side) (Q.rightCrossingAt side)
    (Q.leftCrosses RS hQ hdist side) (Q.rightCrosses RS hQ hdist side)
    (Q.leftCrossingAt_injective hdist side)
    (Q.rightCrossingAt_injective hdist side)
    (Q.boundaryCover RS hQ hdist side)
    (Q.orderedCut_disjoint hdist side)
    hroot hseam C hC hcut

/-! ## Classifying ambient edges against the deleted region

Every edge meeting a corner is one of the eight named local edges.  The four
portal indices give the outer edges, which cross; the four higher indices give
the square edges, which do not.  So an edge that neither crosses nor is a
square edge meets no corner at all, and both of its darts are internal to the
retained region. -/

/-- The four square edges, by local-edge index. -/
theorem squareEdges_eq_image (Q : @FacialSquareData V E) :
    Q.squareEdges = Finset.image Q.lineEdge ({4, 5, 6, 7} : Finset SquareLocalNode) := by
  classical
  simp [squareEdges, lineEdge, Finset.image_insert]

/-- **The classification.**  An edge which neither crosses the deleted region
nor is one of the square edges has no corner among its endpoints. -/
theorem endpoints_not_corner_of_not_crossing (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct) {edge : E}
    (hcross : edge ∉ vertexSetCrossingEdges RS Q.deletedCorners)
    (hsquare : edge ∉ Q.squareEdges) :
    ∀ vertex ∈ RS.endpoints edge, vertex ∉ Q.deletedCorners := by
  classical
  intro vertex hvertex hdeleted
  have hcorner : ∃ j : Fin 4, vertex = Q.cornerAt j := by
    simp only [deletedCorners, Finset.mem_insert, Finset.mem_singleton] at hdeleted
    rcases hdeleted with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨j, rfl⟩ := hcorner
  have hinc := (RS.mem_endpoints_iff_mem_incidentEdges).1 hvertex
  rw [Q.incidentEdges_cornerAt RS hQ j, Finset.mem_image] at hinc
  obtain ⟨node, hnode, rfl⟩ := hinc
  by_cases hlow : node.val < 4
  · refine hcross ?_
    rw [Q.vertexSetCrossingEdges_deletedCorners RS hQ hdist]
    exact Finset.mem_image.2 ⟨⟨node.val, hlow⟩, Finset.mem_univ _,
      (Q.lineEdge_eq_outerEdgeAt hlow).symm⟩
  · refine hsquare ?_
    rw [Q.squareEdges_eq_image]
    refine Finset.mem_image.2 ⟨node, ?_, rfl⟩
    have : node.val = 4 ∨ node.val = 5 ∨ node.val = 6 ∨ node.val = 7 := by
      omega
    rcases this with h | h | h | h <;>
      simp [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, h]

/-- Both darts of such an edge are internal to the retained region. -/
theorem keep_both_ends_of_not_crossing (Q : @FacialSquareData V E)
    (hQ : Q.WellFormed RS) (hdist : Q.LocalEdgesDistinct) {edge : E}
    (hcross : edge ∉ vertexSetCrossingEdges RS Q.deletedCorners)
    (hsquare : edge ∉ Q.squareEdges) {dart : RS.D} (hdart : RS.edgeOf dart = edge) :
    deletedRegionKeep Q.deletedCorners (RS.vertOf dart) ∧
      deletedRegionKeep Q.deletedCorners (RS.vertOf (RS.alpha dart)) := by
  have hpair := RS.endpoints_eq_pair_of_mem
    ((RS.mem_dartsOn).2 hdart)
  constructor
  · refine Q.endpoints_not_corner_of_not_crossing RS hQ hdist hcross hsquare _ ?_
    rw [hpair]
    simp
  · refine Q.endpoints_not_corner_of_not_crossing RS hQ hdist hcross hsquare _ ?_
    rw [hpair]
    simp

end FacialSquareData

end RotationSystem

end Mettapedia.GraphTheory.FourColor
