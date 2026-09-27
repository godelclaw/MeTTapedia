import Mettapedia.GraphTheory.FourColor.FaceExposedDegrees
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairInsertion
import Mettapedia.GraphTheory.FourColor.GoertzelV24RecoveredAdjacentPairData

/-!
# A three-edge facial tail is an adjacent-pair deletion

Suppose a facial event exposes three edges and leaves precisely two
ambient edges missing. The two internal path vertices each require one
of those missing edges. Consequently the patch before the event is
exactly the graph obtained by deleting those adjacent vertices.

The identification is on the original edge identifiers. No colouring
extension or successful repair is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceMatchingCapDeletion

open SimpleGraphDartRotation GoertzelV24RotationVertexCutProfile
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open FaceRegionShelling FaceExposedBoundary FaceExposedPath FaceExposedEndpoints
open FaceBoundarySplice FaceRegionComplement
open FaceExposedDegrees FaceRegionMissingColour FaceRegionDegree EdgeShoreRotation
open PhysicalForkCodeCut PhysicalForkCodeFaces PermutationSingleExitArc

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

private theorem edge_eq_of_two_endpoints {x y : G.edgeSet} {v w : V}
    (hne : v ≠ w)
    (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hwx : w ∈ data.toRotationSystem.endpoints x)
    (hvy : v ∈ data.toRotationSystem.endpoints y)
    (hwy : w ∈ data.toRotationSystem.endpoints y) : x = y := by
  have value (z : G.edgeSet) (hv : v ∈ data.toRotationSystem.endpoints z)
      (hw : w ∈ data.toRotationSystem.endpoints z) : z.val = s(v, w) := by
    obtain ⟨other, he⟩ := Sym2.mem_iff_exists.mp
      ((mem_simpleGraphRotationSystem_endpoints_iff data z v).mp hv)
    have hm := (mem_simpleGraphRotationSystem_endpoints_iff data z w).mp hw
    rw [he, Sym2.mem_iff] at hm
    rcases hm with hm | rfl
    · exact (hne hm.symm).elim
    · exact he
  exact Subtype.ext ((value x hvx hwx).trans (value y hvy hwy).symm)

private theorem touched_of_endpoint {A : Finset G.edgeSet} {x : G.edgeSet} {v : V}
    (hx : x ∈ A) (hv : v ∈ data.toRotationSystem.endpoints x) :
    v ∈ touched data.toRotationSystem A := by
  obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hv
  exact mem_touched.mpr ⟨d, hdv, (data.toRotationSystem.mem_dartsOn.mp hd).symm ▸ hx⟩

private theorem nonretained_edges_unique
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (F : Finset (OrbitFace data.toRotationSystem)) {v : V}
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem F))
    {x y : G.edgeSet} (hx : x ∉ edges data.toRotationSystem F)
    (hy : y ∉ edges data.toRotationSystem F)
    (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hvy : v ∈ data.toRotationSystem.endpoints y) : x = y := by
  obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
  obtain ⟨a, ha, hav⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvy
  have hdx := data.toRotationSystem.mem_dartsOn.mp hd
  have hay := data.toRotationSystem.mem_dartsOn.mp ha
  have hda := nonretained_dart_unique
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) hv hdv hav
    (hdx.symm ▸ hx) (hay.symm ▸ hy)
  exact hdx.symm.trans ((congrArg data.toRotationSystem.edgeOf hda).trans hay)

/-- Fewer than three missing edges cannot hide an entire cubic vertex. -/
theorem touched_of_small_complement
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (F : Finset (OrbitFace data.toRotationSystem))
    (hcap : (Finset.univ \ edges data.toRotationSystem F).card < 3) (v : V) :
    v ∈ touched data.toRotationSystem (edges data.toRotationSystem F) := by
  have hthree := data.toRotationSystem.incidentEdges_card_eq_three_of_isCubic
    ambient.spherical.cubic v
  obtain ⟨x, hx, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card (hthree.symm ▸ hcap)
  have hxF : x ∈ edges data.toRotationSystem F := by simpa using hn
  exact touched_of_endpoint data hxF (data.toRotationSystem.mem_endpoints_iff_mem_incidentEdges.mpr hx)

/-- A facial patch with at most two missing edges has a matching complement.
At a touched vertex, a selected face already retains two incident edges. -/
theorem small_complement_matching
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (F : Finset (OrbitFace data.toRotationSystem))
    (hcap : (Finset.univ \ edges data.toRotationSystem F).card < 3)
    {x y : G.edgeSet} (hx : x ∉ edges data.toRotationSystem F)
    (hy : y ∉ edges data.toRotationSystem F) (hne : x ≠ y) :
    Disjoint (data.toRotationSystem.endpoints x) (data.toRotationSystem.endpoints y) := by
  apply Finset.disjoint_left.mpr
  intro v hvx hvy
  exact hne (nonretained_edges_unique data ambient F
    (touched_of_small_complement data ambient F hcap v) hx hy hvx hvy)

variable {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)
variable (b : Arc (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))
variable (hlen : b.length = 3)

/-- The four vertices in the actual exposed-path order. -/
def node (i : Fin 4) : V :=
  (path data e outer ambient ho b).vertex
    ⟨i.val, by change i.val < b.length + 1; have := hlen; have := i.isLt; omega⟩

/-- The three original edges in exposed-path order. -/
def pathEdge (i : Fin 3) : G.edgeSet :=
  ((path data e outer ambient ho b).edge
    ⟨i.val, by change i.val < b.length; have := hlen; have := i.isLt; omega⟩).val

theorem node_injective : Function.Injective (node data e ambient outer ho b hlen) := by
  intro i j h
  have hh := (path data e outer ambient ho b).vertex_injective h
  exact Fin.ext (congrArg (fun k : Fin (b.length + 1) => k.val) hh)

theorem pathEdge_mem (i : Fin 3) : pathEdge data e ambient outer ho b hlen i ∈ exposedEdges data e :=
  ((path data e outer ambient ho b).edge
    ⟨i.val, by change i.val < b.length; have := hlen; have := i.isLt; omega⟩).property

theorem pathEdge_endpoints (i : Fin 3) :
    data.toRotationSystem.endpoints (pathEdge data e ambient outer ho b hlen i) =
      {node data e ambient outer ho b hlen i.castSucc,
        node data e ambient outer ho b hlen i.succ} := by
  exact (path data e outer ambient ho b).endpoints
    ⟨i.val, by change i.val < b.length; have := hlen; have := i.isLt; omega⟩

theorem exists_pathEdge {x : G.edgeSet} (hx : x ∈ exposedEdges data e) :
    ∃ i : Fin 3, pathEdge data e ambient outer ho b hlen i = x := by
  obtain ⟨i, hi⟩ := (path data e outer ambient ho b).edge.surjective ⟨x, hx⟩
  refine ⟨⟨i.val, by have := i.isLt; change i.val < b.length at this; omega⟩, ?_⟩
  exact congrArg Subtype.val hi

theorem node_old_iff (i : Fin 4) :
    node data e ambient outer ho b hlen i ∈
      touched data.toRotationSystem (edges data.toRotationSystem S.faces) ↔
      i = 0 ∨ i = 3 := by
  have h := vertex_old_iff data e ambient outer ho b
    ⟨i.val, by have := i.isLt; omega⟩
  constructor
  · intro hx
    rcases h.mp hx with hz | hl
    · exact Or.inl (Fin.ext hz)
    · exact Or.inr (Fin.ext (hl.trans hlen))
  · intro hx
    apply h.mpr
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hlen.symm

private theorem internal_missing_edge (i : Fin 4) (hi : i = 1 ∨ i = 2) :
    ∃ x : G.edgeSet, x ∉ edges data.toRotationSystem R.faces ∧
      node data e ambient outer ho b hlen i ∈ data.toRotationSystem.endpoints x := by
  let v := node data e ambient outer ho b hlen i
  have hold : v ∉ touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
    rw [node_old_iff]
    rcases hi with rfl | rfl <;> decide
  have hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem R.faces) := by
    apply touched_of_endpoint data (exposed_mem_new data e (pathEdge_mem data e ambient outer ho b hlen 1))
    rw [pathEdge_endpoints]
    rcases hi with rfl | rfl <;> simp [v]
  have htwo := degree_two_at_new_vertex data e ambient hv hold
  have hthree : ((Finset.univ : Finset G.edgeSet).filter
      fun x => v ∈ data.toRotationSystem.endpoints x).card = 3 := by
    rw [incident_card]
    simpa using ambient.spherical.cubic v
  have hlt : ((edges data.toRotationSystem R.faces).filter
      fun x => v ∈ data.toRotationSystem.endpoints x).card <
      ((Finset.univ : Finset G.edgeSet).filter
        fun x => v ∈ data.toRotationSystem.endpoints x).card := by
    rw [incident_card, htwo, hthree]
    decide
  obtain ⟨x, hx, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨x, fun hh => hn (Finset.mem_filter.mpr ⟨hh, (Finset.mem_filter.mp hx).2⟩),
    (Finset.mem_filter.mp hx).2⟩

/-- The two missing edges meet different internal vertices and exhaust
the complement. This part does not require the missing edges to be a matching. -/
theorem missing_edges_exhaust
    (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2) :
    ∃ x y : G.edgeSet, x ≠ y ∧
      Finset.univ \ edges data.toRotationSystem R.faces = {x, y} ∧
      node data e ambient outer ho b hlen 1 ∈ data.toRotationSystem.endpoints x ∧
      node data e ambient outer ho b hlen 2 ∈ data.toRotationSystem.endpoints y := by
  obtain ⟨x, hx, hvx⟩ := internal_missing_edge data e ambient outer ho b hlen 1 (Or.inl rfl)
  obtain ⟨y, hy, hwy⟩ := internal_missing_edge data e ambient outer ho b hlen 2 (Or.inr rfl)
  have hne : x ≠ y := by
    intro heq
    have hvw : node data e ambient outer ho b hlen 1 ≠ node data e ambient outer ho b hlen 2 :=
      fun hh => (by decide : (1 : Fin 4) ≠ 2) (node_injective data e ambient outer ho b hlen hh)
    have he : x = pathEdge data e ambient outer ho b hlen 1 := by
      apply edge_eq_of_two_endpoints data hvw hvx (heq ▸ hwy)
      · rw [pathEdge_endpoints]; simp
      · rw [pathEdge_endpoints]; simp
    exact hx (he ▸ exposed_mem_new data e (pathEdge_mem data e ambient outer ho b hlen 1))
  have heq : ({x, y} : Finset G.edgeSet) = Finset.univ \ edges data.toRotationSystem R.faces := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [hx, hy]
    · simp [hcap, hne]
  exact ⟨x, y, hne, heq.symm, hvx, hwy⟩

/-- Before the last three-edge path, the retained ambient edges are exactly
those avoiding its two internal vertices. -/
theorem retained_iff_avoids_internal
    (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2)
    (x : G.edgeSet) :
    x ∈ edges data.toRotationSystem S.faces ↔
      node data e ambient outer ho b hlen 1 ∉ data.toRotationSystem.endpoints x ∧
      node data e ambient outer ho b hlen 2 ∉ data.toRotationSystem.endpoints x := by
  constructor
  · intro hx
    constructor <;> intro hv
    · have hh := (node_old_iff data e ambient outer ho b hlen 1).mp (touched_of_endpoint data hx hv)
      rcases hh with hh | hh <;> cases hh
    · have hh := (node_old_iff data e ambient outer ho b hlen 2).mp (touched_of_endpoint data hx hv)
      rcases hh with hh | hh <;> cases hh
  · rintro ⟨hv, hw⟩
    by_contra hold
    by_cases hnew : x ∈ edges data.toRotationSystem R.faces
    · have hx : x ∈ exposedEdges data e := by
        rw [FaceRegionStepBoundary.event_retained_edges data e, Finset.mem_union] at hnew
        exact Finset.mem_sdiff.mpr ⟨hnew.resolve_left hold, hold⟩
      obtain ⟨i, rfl⟩ := exists_pathEdge data e ambient outer ho b hlen hx
      fin_cases i
      · apply hv; rw [pathEdge_endpoints]; simp
      · apply hv; rw [pathEdge_endpoints]; simp
      · apply hw; rw [pathEdge_endpoints]; simp
    · obtain ⟨y, z, _, hrest, hy, hz⟩ := missing_edges_exhaust data e ambient outer ho b hlen hcap
      have hx : x ∈ Finset.univ \ edges data.toRotationSystem R.faces := by simp [hnew]
      rw [hrest, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv hy
      · exact hw hz

/-- The middle path edge is the central edge of the deleted adjacent pair. -/
theorem internal_adjacent :
    G.Adj (node data e ambient outer ho b hlen 1) (node data e ambient outer ho b hlen 2) := by
  let x := pathEdge data e ambient outer ho b hlen 1
  have hv := (mem_simpleGraphRotationSystem_endpoints_iff data x _).mp
    (show node data e ambient outer ho b hlen 1 ∈ data.toRotationSystem.endpoints x by
      rw [pathEdge_endpoints]; simp)
  have hw := (mem_simpleGraphRotationSystem_endpoints_iff data x _).mp
    (show node data e ambient outer ho b hlen 2 ∈ data.toRotationSystem.endpoints x by
      rw [pathEdge_endpoints]; simp)
  obtain ⟨other, he⟩ := Sym2.mem_iff_exists.mp hv
  rw [he, Sym2.mem_iff] at hw
  rcases hw with hw | rfl
  · have hh := node_injective data e ambient outer ho b hlen hw
    cases hh
  · rw [← SimpleGraph.mem_edgeSet G, ← he]
    exact x.property

private theorem new_endpoint_old_or_internal {x : G.edgeSet}
    (hx : x ∈ edges data.toRotationSystem R.faces) {v : V}
    (hv : v ∈ data.toRotationSystem.endpoints x) :
    v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) ∨
      v = node data e ambient outer ho b hlen 1 ∨
      v = node data e ambient outer ho b hlen 2 := by
  by_cases hold : x ∈ edges data.toRotationSystem S.faces
  · exact Or.inl (touched_of_endpoint data hold hv)
  have hexposed : x ∈ exposedEdges data e := by
    rw [FaceRegionStepBoundary.event_retained_edges data e, Finset.mem_union] at hx
    exact Finset.mem_sdiff.mpr ⟨hx.resolve_left hold, hold⟩
  obtain ⟨i, rfl⟩ := exists_pathEdge data e ambient outer ho b hlen hexposed
  rw [pathEdge_endpoints, Finset.mem_insert, Finset.mem_singleton] at hv
  have classify (j : Fin 4) :
      node data e ambient outer ho b hlen j ∈
          touched data.toRotationSystem (edges data.toRotationSystem S.faces) ∨
        node data e ambient outer ho b hlen j = node data e ambient outer ho b hlen 1 ∨
        node data e ambient outer ho b hlen j = node data e ambient outer ho b hlen 2 := by
    fin_cases j
    · exact Or.inl ((node_old_iff data e ambient outer ho b hlen 0).mpr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ((node_old_iff data e ambient outer ho b hlen 3).mpr (Or.inr rfl))
  rcases hv with rfl | rfl
  · exact classify i.castSucc
  · exact classify i.succ

/-- The two internal vertices have no common external neighbor. Thus their
deletion has four distinct ports, as required by the existing restoration theory. -/
theorem no_common_neighbor
    (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2)
    (v : V)
    (hv : G.Adj (node data e ambient outer ho b hlen 1) v)
    (hw : G.Adj (node data e ambient outer ho b hlen 2) v) : False := by
  let x : G.edgeSet := ⟨s(v, node data e ambient outer ho b hlen 1), hv.symm⟩
  let y : G.edgeSet := ⟨s(v, node data e ambient outer ho b hlen 2), hw.symm⟩
  have hvx : v ∈ data.toRotationSystem.endpoints x :=
    (mem_simpleGraphRotationSystem_endpoints_iff data x v).mpr (by simp [x])
  have hvy : v ∈ data.toRotationSystem.endpoints y :=
    (mem_simpleGraphRotationSystem_endpoints_iff data y v).mpr (by simp [y])
  have hxy : x ≠ y := by
    intro he
    have he' : node data e ambient outer ho b hlen 1 = node data e ambient outer ho b hlen 2 := by
      have hh := congrArg Subtype.val he
      simpa [x, y, hv.ne] using hh
    have hh := node_injective data e ambient outer ho b hlen he'
    cases hh
  have hx : x ∉ edges data.toRotationSystem S.faces := by
    intro hh
    exact ((retained_iff_avoids_internal data e ambient outer ho b hlen hcap x).mp hh).1
      ((mem_simpleGraphRotationSystem_endpoints_iff data x _).mpr (by simp [x]))
  have hy : y ∉ edges data.toRotationSystem S.faces := by
    intro hh
    exact ((retained_iff_avoids_internal data e ambient outer ho b hlen hcap y).mp hh).2
      ((mem_simpleGraphRotationSystem_endpoints_iff data y _).mpr (by simp [y]))
  have hold_of_new {z : G.edgeSet}
      (hz : z ∈ edges data.toRotationSystem R.faces)
      (hvz : v ∈ data.toRotationSystem.endpoints z) :
      v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
    rcases new_endpoint_old_or_internal data e ambient outer ho b hlen hz hvz with hold | he | he
    · exact hold
    · exact (hv.ne he.symm).elim
    · exact (hw.ne he.symm).elim
  have hold : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
    by_cases hxR : x ∈ edges data.toRotationSystem R.faces
    · exact hold_of_new hxR hvx
    by_cases hyR : y ∈ edges data.toRotationSystem R.faces
    · exact hold_of_new hyR hvy
    have hd := small_complement_matching data ambient R.faces (by omega) hxR hyR hxy
    exact (Finset.disjoint_left.mp hd hvx hvy).elim
  exact hxy (nonretained_edges_unique data ambient S.faces hold hx hy hvx hvy)

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The actual facial construction determines the existing ordered adjacent
pair, with its ports read from the ambient cubic rotation. -/
def adjacentPair
    (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2) : AdjacentPairData G :=
  GoertzelV24RecoveredAdjacentPairData.adjacentPairData data
    (internal_adjacent data e ambient outer ho b hlen)
    ambient.spherical.cubic ambient.vertexRotationCyclic
    (no_common_neighbor data e ambient outer ho b hlen hcap)

/-- The old facial edge set is precisely the retained carrier of the
existing two-vertex insertion construction. -/
theorem retained_iff_adjacentPair
    (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2)
    (x : G.edgeSet) :
    x ∈ edges data.toRotationSystem S.faces ↔
      IsRetainedAmbientEdge (adjacentPair data e ambient outer ho b hlen hcap) x := by
  let pair := adjacentPair data e ambient outer ho b hlen hcap
  rw [retained_iff_avoids_internal data e ambient outer ho b hlen hcap]
  simp only [mem_simpleGraphRotationSystem_endpoints_iff]
  change (pair.firstVertex ∉ x.val ∧ pair.secondVertex ∉ x.val) ↔ IsRetainedAmbientEdge pair x
  constructor
  · rintro ⟨hv, hw⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro he
    · apply hv; rw [he]; simp [centralEdgeValue]
    · apply hv; rw [he]; simp
    · apply hv; rw [he]; simp
    · apply hw; rw [he]; simp
    · apply hw; rw [he]; simp
  · intro h
    constructor
    · intro hv
      exact (endpoints_mem_retainedVertexSet pair x h pair.firstVertex hv).1 rfl
    · intro hw
      exact (endpoints_mem_retainedVertexSet pair x h pair.secondVertex hw).2 rfl

include ambient
omit outer ho b hlen in
/-- The operational event and two cardinalities suffice: the boundary arc
and ordered adjacent pair are constructed from the spherical geometry. -/
theorem exists_adjacentPair
    (hthree : (exposedEdges data e).card = 3)
    (hcap : (Finset.univ \ edges data.toRotationSystem R.faces).card = 2) :
    ∃ pair : AdjacentPairData G, ∀ x : G.edgeSet,
      x ∈ edges data.toRotationSystem S.faces ↔ IsRetainedAmbientEdge pair x := by
  obtain ⟨outer, ho, _, _⟩ := Region.realizes ambient R
  obtain ⟨b⟩ := exists_exposed_arc data e outer ambient ho
  have hlen : b.length = 3 := by
    rw [b.length_eq_card, exposed_darts_card data e outer ambient ho]
    exact hthree
  exact ⟨adjacentPair data e ambient outer ho b hlen hcap,
    retained_iff_adjacentPair data e ambient outer ho b hlen hcap⟩

end
end Mettapedia.GraphTheory.FourColor.FaceMatchingCapDeletion
