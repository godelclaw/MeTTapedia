import MettapediaFourColor.StripSixBarrierRepair

/-! # Complementary paths at the three-port ear

An exterior path from port six to port eight closes through core vertex
11. The two specified facial sides at edge 8--11 put ports seven and nine
on opposite sides. The exterior paths may have arbitrary length.
-/

namespace FourColor.StripComplementaryGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24WalkFaceParityCut GoertzelV24WalkCycleParity
open GoertzelV24OrbitFaceParityBoundary GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation TriangleStripAnchors StripSixBarrierGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
noncomputable section

/-- Two actual face incidences across the core return edge. -/
def EarSides (s : StripSixBarrierGeometry.Patch data) : Prop :=
  data.toRotationSystem.phi (s.dart 7 11 (by decide +kernel)) =
      s.dart 11 8 (by decide +kernel) ∧
  data.toRotationSystem.phi (s.dart 12 8 (by decide +kernel)) =
      s.dart 8 11 (by decide +kernel)

def returnRoute : input0099.graph.Walk 6 8 :=
  .cons (by decide +kernel : input0099.graph.Adj 6 11)
    (.cons (by decide +kernel) .nil)

def tailRoute : input0099.graph.Walk 9 12 :=
  .cons (by decide +kernel : input0099.graph.Adj 9 15)
    (.cons (by decide +kernel) .nil)

variable (s : StripSixBarrierGeometry.Patch data) (sides : EarSides s)
  (rotation : VertexRotationCyclic data.toRotationSystem)
  (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
  (connected : G.Connected)
  (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
    Fintype.card (OrbitFace data.toRotationSystem) = 2)

include sides rotation dual connected euler in
/-- Alternating exterior paths across this ear cannot be vertex-disjoint. -/
theorem no_crossing (p : G.Walk (s.point 6) (s.point 8))
    (outsideP : ∀ x ∈ p.support, s.Exterior x)
    (q : G.Walk (s.point 7) (s.point 9))
    (outsideQ : ∀ x ∈ q.support, s.Exterior x)
    (disjoint : ∀ x ∈ q.support, x ∉ p.support) : False := by
  let r := returnRoute.map s.sourceHom
  let closed := r.append p.reverse
  obtain ⟨labels,potential⟩ := exists_orbitFaceLabeling_eq_walkEdgeParity
    data dual connected euler closed
  have absent : s(s.point 11,s.point 8) ∉ p.edges := fun h =>
    outsideP _ (p.fst_mem_support_of_mem_edges h) 11 (by decide) rfl
  have eqs : ∀ i j : Fin 19, s.point i = s.point j ↔ i = j :=
    fun _ _ => s.injective.eq_iff
  have parity : walkEdgeParity closed
      (data.toRotationSystem.edgeOf (s.dart 11 8 (by decide +kernel))) = 1 := by
    change (↑(List.count s(s.point 11,s.point 8)
      ([s(s.point 6,s.point 11),s(s.point 11,s.point 8)] ++ p.reverse.edges)) : F2) = 1
    simp [Walk.edges_reverse,eqs,List.count_eq_zero.mpr absent]
  have crossing := congrFun potential
    (data.toRotationSystem.edgeOf (s.dart 11 8 (by decide +kernel)))
  rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf data.toRotationSystem labels
    (s.dart 11 8 (by decide +kernel)),parity] at crossing
  have different := (f2_add_eq_one_iff_ne _ _).mp crossing
  have f0 := dartOrbitFace_phi_eq data.toRotationSystem (s.dart 7 11 (by decide +kernel))
  have f1 := dartOrbitFace_phi_eq data.toRotationSystem (s.dart 12 8 (by decide +kernel))
  rw [sides.1] at f0
  rw [sides.2] at f1
  let t := tailRoute.map s.sourceHom
  have avoidQ : ∀ x ∈ q.support, x ∉ closed.support := by
    intro x hx hc
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hc
    rcases hc with hc | hc
    · change x ∈ [s.point 6,s.point 11,s.point 8] at hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact disjoint _ hx p.start_mem_support
      · exact outsideQ _ hx 11 (by decide) rfl
      · exact disjoint _ hx p.end_mem_support
    · exact disjoint _ hx hc
  have avoidT : ∀ x ∈ t.support, x ∉ closed.support := by
    intro x hx hc
    change x ∈ [s.point 9,s.point 15,s.point 12] at hx
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hc
    rcases hc with hc | hc
    · change x ∈ [s.point 6,s.point 11,s.point 8] at hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hc
      rcases hx with rfl | rfl | rfl <;> simp [eqs] at hc
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact disjoint _ q.end_mem_support hc
      · exact outsideP _ hc 15 (by decide) rfl
      · exact outsideP _ hc 12 (by decide) rfl
  have same := PrimalPathSeparation.labels_eq_of_disjoint_walk data rotation closed
    (q.append t) (by
      intro x hx
      rw [Walk.mem_support_append_iff] at hx
      exact hx.elim (avoidQ x) (avoidT x)) labels potential
    (s.dart 7 11 (by decide +kernel)) (s.dart 12 8 (by decide +kernel)) rfl rfl
  apply different
  change labels (dartOrbitFace data.toRotationSystem (s.dart 11 8 (by decide +kernel))) =
    labels (dartOrbitFace data.toRotationSystem (s.dart 8 11 (by decide +kernel)))
  exact (congrArg labels f0).trans (same.trans (congrArg labels f1).symm)

private theorem component_walk {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    {u v : W} (hu : u ∈ C.kempeComponentSet a b K)
    (hv : v ∈ C.kempeComponentSet a b K) :
    ∃ walk : H.Walk u v, ∀ w ∈ walk.support, C w = a ∨ C w = b := by
  obtain ⟨hua,huK⟩ := hu
  obtain ⟨hva,hvK⟩ := hv
  obtain ⟨q⟩ := ConnectedComponent.exact (huK.trans hvK.symm)
  let forget : C.bicoloredSubgraph a b →g H := ⟨Subtype.val,fun h => h⟩
  refine ⟨q.map forget,?_⟩
  intro w hw
  rw [Walk.support_map,List.mem_map] at hw
  obtain ⟨z,_,rfl⟩ := hw
  exact z.property

include sides rotation dual connected euler in
/-- A connected zero/one pair of outer ports separates the complementary
components at the two intervening ports. -/
theorem complementary_separation {W : Type*} {H : SimpleGraph W}
    (e : ExteriorReading s H) (C : H.Coloring Color)
    (K : (C.bicoloredSubgraph Color.c0 Color.c1).ConnectedComponent)
    (m6 : e.ports 6 ∈ C.kempeComponentSet Color.c0 Color.c1 K)
    (m8 : e.ports 8 ∈ C.kempeComponentSet Color.c0 Color.c1 K)
    (L : (C.bicoloredSubgraph Color.c2 Color.c3).ConnectedComponent)
    (m7 : e.ports 7 ∈ C.kempeComponentSet Color.c2 Color.c3 L) :
    e.ports 9 ∉ C.kempeComponentSet Color.c2 Color.c3 L := by
  intro m9
  obtain ⟨p,hp⟩ := component_walk C Color.c0 Color.c1 K m6 m8
  obtain ⟨q,hq⟩ := component_walk C Color.c2 Color.c3 L m7 m9
  let P := (p.map e.embedding.toHom).copy (e.boundary 6) (e.boundary 8)
  let Q := (q.map e.embedding.toHom).copy (e.boundary 7) (e.boundary 9)
  have image {u v : W} (r : H.Walk u v) {u' v' : V}
      (hu : e.embedding u = u') (hv : e.embedding v = v') (x : V) :
      x ∈ ((r.map e.embedding.toHom).copy hu hv).support ↔
        ∃ y ∈ r.support, e.embedding y = x := by
    simp [Walk.support_copy,Walk.support_map]
  have outsideP : ∀ x ∈ P.support, s.Exterior x := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := (image p _ _ x).mp hx
    exact e.outside y
  have outsideQ : ∀ x ∈ Q.support, s.Exterior x := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := (image q _ _ x).mp hx
    exact e.outside y
  have disjoint : ∀ x ∈ Q.support, x ∉ P.support := by
    intro x hx hp'
    obtain ⟨y,hy,ey⟩ := (image q _ _ x).mp hx
    obtain ⟨z,hz,ez⟩ := (image p _ _ x).mp hp'
    have same := e.embedding.injective (ey.trans ez.symm)
    subst z
    rcases hq y hy with h | h <;> rcases hp y hz with h' | h' <;>
      cases h.symm.trans h'
  exact no_crossing s sides rotation dual connected euler P outsideP Q outsideQ disjoint

end
end FourColor.StripComplementaryGeometry
