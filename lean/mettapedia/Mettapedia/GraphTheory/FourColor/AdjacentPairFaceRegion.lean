import Mettapedia.GraphTheory.FourColor.FaceRegionConnectivityConverse
import Mettapedia.GraphTheory.FourColor.FaceRegionShelling
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualTriangleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree

/-!
# Facial realization of an adjacent-pair deletion

The original faces avoiding two adjacent vertices retain exactly the edges
of the induced vertex deletion in a vertex-minimal Tait counterexample.
The argument uses unique intersections of faces and the classification of
dual triangles. In particular, no additional edge between the surrounding
faces is silently deleted.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentPairFaceRegion

open SimpleGraphDartRotation GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceTwoSided
open GoertzelV24PrimalCycleFacialBond SphericalDistanceContours
open FaceRegionDegree PhysicalForkCodeEuler PhysicalForkCodeCut
open GoertzelV24TwoEdgeCutMinimality GoertzelV24AdjacentPairBoundary

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)

/-- Every endpoint of a facial edge is incident with that same face. -/
theorem face_at_endpoint {f : OrbitFace data.toRotationSystem} {x : G.edgeSet}
    (hx : x ∈ orbitFaceBoundary data.toRotationSystem f) {v : V} (hv : v ∈ x.val) :
    f ∈ vertexFaces data v := by
  obtain ⟨d, hd, hdx⟩ := (mem_orbitFaceBoundary_iff _ _ _).mp hx
  have hdf := (mem_orbitFaceDarts_iff _ _ _).mp hd
  have hv' : v = d.fst ∨ v = d.snd := by
    rw [← hdx] at hv
    exact Sym2.mem_iff.mp hv
  rcases hv' with rfl | rfl
  · exact ⟨d, rfl, hdf⟩
  · exact ⟨data.toRotationSystem.phi d,
      data.toRotationSystem.vert_phi_eq_vert_alpha d,
      (dartOrbitFace_phi_eq _ d).trans hdf⟩

/-- Two distinct faces at a cubic vertex share an edge at that vertex. -/
theorem shared_edge_at_vertex
    (hc : data.toRotationSystem.IsCubic)
    (hr : VertexRotationCyclic data.toRotationSystem)
    {v : V} {f g : OrbitFace data.toRotationSystem} (hne : f ≠ g)
    (hf : f ∈ vertexFaces data v) (hg : g ∈ vertexFaces data v) :
    ∃ x : G.edgeSet, v ∈ x.val ∧ x ∈ orbitFaceBoundary data.toRotationSystem f ∧
      x ∈ orbitFaceBoundary data.toRotationSystem g := by
  obtain ⟨d, hd, hdf⟩ := hf
  obtain ⟨a, ha, hag⟩ := hg
  have hda : d ≠ a := fun h => hne (hdf.symm.trans ((congrArg (dartOrbitFace _) h).trans hag))
  have shared (b : data.toRotationSystem.D) :
      data.toRotationSystem.edgeOf b ∈
        orbitFaceBoundary data.toRotationSystem (dartOrbitFace data.toRotationSystem (data.toRotationSystem.rho b)) := by
    rw [← dartOrbitFace_alpha_eq_dartOrbitFace_rho]
    simpa only [data.toRotationSystem.edge_alpha] using
      edgeOf_mem_orbitFaceBoundary_dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha b)
  rcases data.toRotationSystem.rho_eq_or_rho_eq_of_cubic hc hr (ha.trans hd.symm) hda with h | h
  · refine ⟨data.toRotationSystem.edgeOf d, ?_, ?_, ?_⟩
    · change v ∈ s(d.fst, d.snd)
      exact Sym2.mem_iff.mpr (Or.inl hd.symm)
    · exact hdf ▸ edgeOf_mem_orbitFaceBoundary_dartOrbitFace _ d
    · simpa only [h, hag] using shared d
  · refine ⟨data.toRotationSystem.edgeOf a, ?_, ?_, ?_⟩
    · change v ∈ s(a.fst, a.snd)
      exact Sym2.mem_iff.mpr (Or.inl ha.symm)
    · simpa only [h, hdf] using shared a
    · exact hag ▸ edgeOf_mem_orbitFaceBoundary_dartOrbitFace _ a

variable (minimal : GraphBackedVertexMinimalTaitCounterexample data)

include minimal

/-- Unique facial intersections make the shared edge local to every common
vertex of its two faces. -/
theorem shared_edge_endpoint {f g : OrbitFace data.toRotationSystem} (hne : f ≠ g)
    {x : G.edgeSet} (hxf : x ∈ orbitFaceBoundary data.toRotationSystem f)
    (hxg : x ∈ orbitFaceBoundary data.toRotationSystem g) {v : V}
    (hf : f ∈ vertexFaces data v) (hg : g ∈ vertexFaces data v) : v ∈ x.val := by
  obtain ⟨y, hv, hyf, hyg⟩ := shared_edge_at_vertex data minimal.spherical.cubic
    minimal.vertexRotationCyclic hne hf hg
  have he := GoertzelV24MinimalFaceIntersections.edge_eq_of_mem_distinct_orbitFace_pair
    data minimal hne hyf hyg hxf hxg
  exact he ▸ hv

omit minimal [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem adj_of_endpoints {x : G.edgeSet} {v w : V}
    (hv : v ∈ x.val) (hw : w ∈ x.val) (hne : v ≠ w) : G.Adj v w := by
  obtain ⟨z, hx⟩ := Sym2.mem_iff_exists.mp hv
  rw [hx, Sym2.mem_iff] at hw
  rcases hw with h | h
  · exact (hne h.symm).elim
  · have he : s(v, w) ∈ G.edgeSet := by simpa only [hx, ← h] using x.property
    exact (SimpleGraph.mem_edgeSet G).mp he

private theorem triangle_meets
    {f g h : OrbitFace data.toRotationSystem}
    (hfg : (orbitFaceDualGraph data).Adj f g)
    (hgh : (orbitFaceDualGraph data).Adj g h)
    (hhf : (orbitFaceDualGraph data).Adj h f)
    {x y z : G.edgeSet}
    (hxf : x ∈ orbitFaceBoundary data.toRotationSystem f)
    (hxg : x ∈ orbitFaceBoundary data.toRotationSystem g)
    (hyg : y ∈ orbitFaceBoundary data.toRotationSystem g)
    (hyh : y ∈ orbitFaceBoundary data.toRotationSystem h)
    (hzh : z ∈ orbitFaceBoundary data.toRotationSystem h)
    (hzf : z ∈ orbitFaceBoundary data.toRotationSystem f) :
    ∃ v : V, v ∈ x.val ∧ v ∈ y.val ∧ v ∈ z.val := by
  let unique := GoertzelV24MinimalFaceIntersections.pairwiseUniqueSharedInteriorEdges data minimal
  have identify {a b : OrbitFace data.toRotationSystem}
      (hab : (orbitFaceDualGraph data).Adj a b) (e : G.edgeSet)
      (hea : e ∈ orbitFaceBoundary data.toRotationSystem a)
      (heb : e ∈ orbitFaceBoundary data.toRotationSystem b) :
      sharedInteriorEdgeOfAdjOfPairwiseUnique (orbitFaceBoundary data.toRotationSystem)
        Finset.univ unique hab = e := by
    apply GoertzelV24MinimalFaceIntersections.edge_eq_of_mem_distinct_orbitFace_pair
      data minimal hab.ne
    · exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left _ _ unique hab
    · exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right _ _ unique hab
    · exact hea
    · exact heb
  obtain ⟨v, hvx, hvy, hvz⟩ :=
    GoertzelV24MinimalDualTriangleClassification.exists_vertex_mem_three_shared_edges_of_dual_triangle
      data minimal hfg hgh hhf
  change v ∈ (sharedInteriorEdgeOfAdjOfPairwiseUnique _ _ unique hfg).val at hvx
  change v ∈ (sharedInteriorEdgeOfAdjOfPairwiseUnique _ _ unique hgh).val at hvy
  change v ∈ (sharedInteriorEdgeOfAdjOfPairwiseUnique _ _ unique hhf).val at hvz
  rw [identify hfg x hxf hxg] at hvx
  rw [identify hgh y hyg hyh] at hvy
  rw [identify hhf z hzh hzf] at hvz
  exact ⟨v, hvx, hvy, hvz⟩

private theorem no_cross_edge {v w : V} (hvw : G.Adj v w)
    {f g : OrbitFace data.toRotationSystem} (hne : f ≠ g)
    (hfv : f ∈ vertexFaces data v) (hfw : f ∉ vertexFaces data w)
    (hgv : g ∉ vertexFaces data v) (hgw : g ∈ vertexFaces data w)
    {x : G.edgeSet} (hxf : x ∈ orbitFaceBoundary data.toRotationSystem f)
    (hxg : x ∈ orbitFaceBoundary data.toRotationSystem g) : False := by
    let d : data.toRotationSystem.D := ⟨(v, w), hvw⟩
    let c := dartOrbitFace data.toRotationSystem d
    have hcv : c ∈ vertexFaces data v := ⟨d, rfl, rfl⟩
    have hcw : c ∈ vertexFaces data w := ⟨data.toRotationSystem.phi d,
      data.toRotationSystem.vert_phi_eq_vert_alpha d, dartOrbitFace_phi_eq _ d⟩
    have hfc : f ≠ c := fun h => hfw (h.symm ▸ hcw)
    have hcg : c ≠ g := fun h => hgv (h ▸ hcv)
    obtain ⟨y, hvy, hyf, hyc⟩ := shared_edge_at_vertex data minimal.spherical.cubic
      minimal.vertexRotationCyclic hfc hfv hcv
    obtain ⟨z, hwz, hzc, hzg⟩ := shared_edge_at_vertex data minimal.spherical.cubic
      minimal.vertexRotationCyclic hcg hcw hgw
    have adjacent {a b : OrbitFace data.toRotationSystem} (hab : a ≠ b)
        {e : G.edgeSet} (ha : e ∈ orbitFaceBoundary data.toRotationSystem a)
        (hb : e ∈ orbitFaceBoundary data.toRotationSystem b) :
        (orbitFaceDualGraph data).Adj a b :=
      interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary data.toRotationSystem) Finset.univ
        (orbitFace_incidence_le_two _) hab ha hb
    obtain ⟨u, huy, huz, _⟩ := triangle_meets data minimal
      (adjacent hfc hyf hyc) (adjacent hcg hzc hzg) (adjacent hne.symm hxg hxf)
      hyf hyc hzc hzg hxg hxf
    have huv : u ≠ v := by
      intro h
      exact hgv (face_at_endpoint data hzg (h ▸ huz))
    have huw : u ≠ w := by
      intro h
      exact hfw (face_at_endpoint data hyf (h ▸ huy))
    exact GoertzelV24MinimalTriangleFree.no_common_neighbor_of_vertexMinimalTaitCounterexample
      data minimal hvw u (adj_of_endpoints hvy huy huv.symm)
        (adj_of_endpoints hwz huz huw.symm)

/-- An edge between faces surrounding an adjacent pair is incident with the
pair itself. An extra edge would give a primal triangle through the pair. -/
theorem surrounding_edge_incident {v w : V} (hvw : G.Adj v w)
    {f g : OrbitFace data.toRotationSystem} (hne : f ≠ g)
    (hf : f ∈ vertexFaces data v ∪ vertexFaces data w)
    (hg : g ∈ vertexFaces data v ∪ vertexFaces data w)
    {x : G.edgeSet} (hxf : x ∈ orbitFaceBoundary data.toRotationSystem f)
    (hxg : x ∈ orbitFaceBoundary data.toRotationSystem g) : v ∈ x.val ∨ w ∈ x.val := by
  by_cases hfv : f ∈ vertexFaces data v
  · by_cases hgv : g ∈ vertexFaces data v
    · exact Or.inl (shared_edge_endpoint data minimal hne hxf hxg hfv hgv)
    have hgw : g ∈ vertexFaces data w := hg.resolve_left hgv
    by_cases hfw : f ∈ vertexFaces data w
    · exact Or.inr (shared_edge_endpoint data minimal hne hxf hxg hfw hgw)
    exact (no_cross_edge data minimal hvw hne hfv hfw hgv hgw hxf hxg).elim
  · have hfw : f ∈ vertexFaces data w := hf.resolve_left hfv
    by_cases hgw : g ∈ vertexFaces data w
    · exact Or.inr (shared_edge_endpoint data minimal hne hxf hxg hfw hgw)
    have hgv : g ∈ vertexFaces data v := hg.resolve_right hgw
    exact (no_cross_edge data minimal hvw.symm hne hfw hfv hgw hgv hxf hxg).elim

/-- Select the original faces avoiding the two central vertices. -/
def faces (first second : V) : Finset (OrbitFace data.toRotationSystem) :=
  Finset.univ.filter fun f => f ∉ vertexFaces data first ∧ f ∉ vertexFaces data second

omit minimal in
@[simp] theorem mem_faces (first second : V) (f : OrbitFace data.toRotationSystem) :
    f ∈ faces data first second ↔
      f ∉ vertexFaces data first ∧ f ∉ vertexFaces data second := by
  simp [faces]

/-- Removing the surrounding faces loses exactly the five edges incident
with the adjacent pair, and no unrelated edge. -/
theorem retained_edge_iff {first second : V} (hadj : G.Adj first second) (x : G.edgeSet) :
    x ∈ edges data.toRotationSystem (faces data first second) ↔
      first ∉ x.val ∧ second ∉ x.val := by
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.mp hx
    have hh := (mem_faces data first second f).mp hf
    exact ⟨fun hv => hh.1 (face_at_endpoint data hxf hv),
      fun hv => hh.2 (face_at_endpoint data hxf hv)⟩
  · rintro ⟨hfirst, hsecond⟩
    by_contra hx
    obtain ⟨d, hd⟩ := data.toRotationSystem.dartsOn_nonempty x
    have hdx := data.toRotationSystem.mem_dartsOn.mp hd
    have hsides :
        dartOrbitFace data.toRotationSystem d ∉ faces data first second ∧
        dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉ faces data first second := by
      rw [← hdx, edge_mem_iff] at hx
      exact not_or.mp hx
    have side {f : OrbitFace data.toRotationSystem} (hf : f ∉ faces data first second) :
        f ∈ vertexFaces data first ∪ vertexFaces data second := by
      simpa only [mem_faces, not_and_or, not_not, Set.mem_union] using hf
    have hxf : x ∈ orbitFaceBoundary data.toRotationSystem (dartOrbitFace data.toRotationSystem d) :=
      hdx ▸ edgeOf_mem_orbitFaceBoundary_dartOrbitFace _ d
    have hxg : x ∈ orbitFaceBoundary data.toRotationSystem
        (dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d)) := by
      have h := edgeOf_mem_orbitFaceBoundary_dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha d)
      simpa only [data.toRotationSystem.edge_alpha, hdx] using h
    exact (surrounding_edge_incident data minimal hadj (minimal.facesTwoSided d)
      (side hsides.1) (side hsides.2) hxf hxg).elim hfirst hsecond

omit minimal in
theorem touched_avoids {first second v : V}
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem (faces data first second))) :
    v ≠ first ∧ v ≠ second := by
  obtain ⟨d, hd, hf⟩ := (touched_iff _ _ _).mp hv
  have hh := (mem_faces data first second _).mp hf
  constructor
  · intro h
    exact hh.1 ⟨d, hd.trans h, rfl⟩
  · intro h
    exact hh.2 ⟨d, hd.trans h, rfl⟩

variable (pair : AdjacentPairData G)

/-- The induced deletion maps into the original retained edge shore by the
literal inclusion of vertices. -/
def retainedHom :
    DeletedAdjacentPairGraph G pair.firstVertex pair.secondVertex →g
      shoreGraph data.toRotationSystem
        (edges data.toRotationSystem (faces data pair.firstVertex pair.secondVertex)) where
  toFun := Subtype.val
  map_rel' := by
    intro v w h
    let d : data.toRotationSystem.D := ⟨(v.val, w.val), h⟩
    refine ⟨d, (retained_edge_iff data minimal pair.centralAdjacent _).mpr ?_, rfl, rfl⟩
    change pair.firstVertex ∉ s(v.val, w.val) ∧ pair.secondVertex ∉ s(v.val, w.val)
    simp only [Sym2.mem_iff, not_or]
    exact ⟨⟨Ne.symm v.property.1, Ne.symm w.property.1⟩,
      ⟨Ne.symm v.property.2, Ne.symm w.property.2⟩⟩

/-- Connectivity of the induced deletion is inherited by the facial edge
shore, using its exact original-edge description. -/
theorem shore_connected :
    ShoreConnected data.toRotationSystem
      (edges data.toRotationSystem (faces data pair.firstVertex pair.secondVertex)) := by
  have hc := GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedRegion_connected_of_vertexMinimalTaitCounterexample
    data minimal pair
  intro v w hv hw
  exact (hc ⟨v, touched_avoids data hv⟩ ⟨w, touched_avoids data hw⟩).map
    (retainedHom data minimal pair)

/-- At least one original face survives the deletion. Distinct retained
ports and their connected path provide a retained edge. -/
theorem faces_nonempty : (faces data pair.firstVertex pair.secondVertex).Nonempty := by
  have hc := GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedRegion_connected_of_vertexMinimalTaitCounterexample
    data minimal pair
  obtain ⟨p⟩ := hc (pair.retainedPort 0) (pair.retainedPort 1)
  have hne : pair.retainedPort 0 ≠ pair.retainedPort 1 := by
    intro h
    have hh := pair.retainedPort_injective h
    cases hh
  obtain ⟨d, hd, _, _⟩ := (retainedHom data minimal pair).map_rel
    (p.adj_snd (p.not_nil_of_ne hne))
  obtain ⟨f, hf, _⟩ := Finset.mem_biUnion.mp hd
  exact ⟨f, hf⟩

/-- The facial deletion retains every vertex except the chosen pair. -/
theorem touched_iff_retained (v : V) :
    v ∈ touched data.toRotationSystem
      (edges data.toRotationSystem (faces data pair.firstVertex pair.secondVertex)) ↔
        v ≠ pair.firstVertex ∧ v ≠ pair.secondVertex := by
  refine ⟨touched_avoids data, ?_⟩
  intro hv
  let u : retainedVertexSet pair.firstVertex pair.secondVertex := ⟨v, hv⟩
  have hports : pair.retainedPort 0 ≠ pair.retainedPort 1 := by
    intro h
    have hh := pair.retainedPort_injective h
    cases hh
  have other : ∃ w : retainedVertexSet pair.firstVertex pair.secondVertex, u ≠ w := by
    by_cases h : u = pair.retainedPort 0
    · exact ⟨pair.retainedPort 1, h ▸ hports⟩
    · exact ⟨pair.retainedPort 0, h⟩
  obtain ⟨w, hw⟩ := other
  have hc := pair.retainedRegion_connected_of_vertexMinimalTaitCounterexample data minimal
  obtain ⟨p⟩ := hc u w
  obtain ⟨d, hd, hdu, _⟩ := (retainedHom data minimal pair).map_rel
    (p.adj_snd (p.not_nil_of_ne hw))
  exact mem_touched.mpr ⟨d, hdu, hd⟩

/-- The selected original faces are connected, not merely their primal
vertex deletion. -/
theorem inside_connected :
    ((orbitFaceDualGraph data).induce
      (faces data pair.firstVertex pair.secondVertex : Set _)).Connected :=
  FaceRegionConnectivityConverse.connected_of_shoreConnected data _ minimal.spherical.cubic
    minimal.vertexRotationCyclic minimal.facesTwoSided (faces_nonempty data minimal pair)
    (shore_connected data minimal pair)

/-- The omitted faces form the union of two intersecting local cliques. -/
theorem outside_connected :
    ((orbitFaceDualGraph data).induce
      (faces data pair.firstVertex pair.secondVertex : Set _)ᶜ).Connected := by
  let d : data.toRotationSystem.D := ⟨(pair.firstVertex, pair.secondVertex), pair.centralAdjacent⟩
  let c := dartOrbitFace data.toRotationSystem d
  have hcv : c ∈ vertexFaces data pair.firstVertex := ⟨d, rfl, rfl⟩
  have hcw : c ∈ vertexFaces data pair.secondVertex := ⟨data.toRotationSystem.phi d,
    data.toRotationSystem.vert_phi_eq_vert_alpha d, dartOrbitFace_phi_eq _ d⟩
  have pre (v : V) : ((orbitFaceDualGraph data).induce (vertexFaces data v)).Preconnected := by
    intro f g
    rcases vertexFaces_clique data minimal.spherical.cubic minimal.vertexRotationCyclic
      minimal.facesTwoSided v f.val g.val f.property g.property with h | h
    · exact Subtype.ext h ▸ SimpleGraph.Reachable.refl f
    · exact SimpleGraph.Adj.reachable h
  have heq : (faces data pair.firstVertex pair.secondVertex : Set _)ᶜ =
      vertexFaces data pair.firstVertex ∪ vertexFaces data pair.secondVertex := by
    ext f
    simp only [Set.mem_compl_iff, Finset.mem_coe, mem_faces, Set.mem_union,
      not_and_or, not_not]
  rw [heq]
  exact SimpleGraph.induce_union_connected (pre _) (pre _) ⟨c, hcv, hcw⟩

/-- An adjacent-pair deletion is an actual state of the facial GSLT.
Both sides are proved connected, with their original face identifiers. -/
def region : FaceRegionShelling.Region data where
  faces := faces data pair.firstVertex pair.secondVertex
  inside := inside_connected data minimal pair
  outside := outside_connected data minimal pair

open GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The facial and vertex-deletion APIs retain precisely the same ambient
edge identifiers. -/
theorem retained_iff (x : G.edgeSet) :
    x ∈ edges data.toRotationSystem (region data minimal pair).faces ↔
      IsRetainedAmbientEdge pair x := by
  rw [show (region data minimal pair).faces = faces data pair.firstVertex pair.secondVertex from rfl,
    retained_edge_iff data minimal pair.centralAdjacent]
  constructor
  · rintro ⟨hv, hw⟩
    have left (z : Sym2 V) (hz : pair.firstVertex ∈ z) : x.val ≠ z := fun h => hv (h ▸ hz)
    have right (z : Sym2 V) (hz : pair.secondVertex ∈ z) : x.val ≠ z := fun h => hw (h ▸ hz)
    exact ⟨left _ (by simp [centralEdgeValue]),
      left _ (by simp), left _ (by simp), right _ (by simp), right _ (by simp)⟩
  · intro h
    exact ⟨fun hv => (endpoints_mem_retainedVertexSet pair x h _ hv).1 rfl,
      fun hw => (endpoints_mem_retainedVertexSet pair x h _ hw).2 rfl⟩

/-- The omitted original edges are the central edge and the four distinct
external edges of the adjacent pair. -/
theorem missing_edges :
    Finset.univ \ edges data.toRotationSystem (region data minimal pair).faces =
      insert (centralEdge pair) (Finset.univ.image (boundaryEdge pair)) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, retained_iff data minimal pair,
    not_isRetainedAmbientEdge_iff, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨i, h⟩)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr ⟨i, Subtype.ext h.symm⟩
  · rintro (h | ⟨i, h⟩)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr ⟨i, (congrArg Subtype.val h).symm⟩

theorem missing_edges_card :
    (Finset.univ \ edges data.toRotationSystem (region data minimal pair).faces).card = 5 := by
  have hn : centralEdge pair ∉ Finset.univ.image (boundaryEdge pair) := by
    rintro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact centralEdgeValue_ne_boundaryEdgeValue pair i (congrArg Subtype.val hi).symm
  have hi : Function.Injective (boundaryEdge pair) := fun i j h =>
    boundaryEdgeValue_injective pair (congrArg Subtype.val h)
  rw [missing_edges data minimal pair, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ hi]
  simp

end
end Mettapedia.GraphTheory.FourColor.AdjacentPairFaceRegion
