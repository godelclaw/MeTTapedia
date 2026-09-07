import Mettapedia.GraphTheory.FourColor.SphericalDistanceContours
import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceBoundaryCycleRigidity
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

/-!
# From connected face regions to complete vertex hulls

Take every vertex incident with a chosen face region. This closed vertex
region is connected when the face region is connected in the actual dual.
It may disconnect its complement. Keeping the component of a fixed outside
vertex, and filling all other components, constructs a full connected bond.
The operation is monotone and introduces no new boundary edge.

The intended input is a union of the face components cut out by contour and
linkage barriers. No bounded width or strict growth is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionHull

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceWalk GoertzelV24PrimalCycleFacialBond
open GoertzelV24FaceDualConnectedness VertexSeparatorBond
open GoertzelV24DeletedRegionRotationSplice GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24ComplementaryRegionBoundaryOrder GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24OrbitFaceCurvatureBulk

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

def faceVertices (data : Data G) (f : OrbitFace data.toRotationSystem) : Set V :=
  {v | ∃ d : G.Dart, d.fst = v ∧ dartOrbitFace data.toRotationSystem d = f}

def closedVertices (data : Data G) (R : Set (OrbitFace data.toRotationSystem)) : Set V :=
  {v | ∃ f ∈ R, v ∈ faceVertices data f}

/-- The actual face dual, allowing only crossings of non-barrier edges. -/
def barrierDual (data : Data G) (B : Finset G.edgeSet) :
    SimpleGraph (OrbitFace data.toRotationSystem) where
  Adj f g := (orbitFaceDualGraph data).Adj f g ∧ ∃ e ∉ B,
    e ∈ orbitFaceBoundary data.toRotationSystem f ∧ e ∈ orbitFaceBoundary data.toRotationSystem g
  symm := ⟨by rintro f g ⟨h, e, he, hf, hg⟩; exact ⟨h.symm, e, he, hg, hf⟩⟩
  loopless := ⟨fun f h => h.1.ne rfl⟩

/-- A region is selected by reachability after deleting dual crossings,
not by independently erasing each four-path rim. -/
def cell (data : Data G) (B : Finset G.edgeSet) (root : OrbitFace data.toRotationSystem) :
    Set (OrbitFace data.toRotationSystem) :=
  ((barrierDual data B).connectedComponentMk root).supp

theorem cell_dual_connected (data : Data G) (B : Finset G.edgeSet)
    (root : OrbitFace data.toRotationSystem) :
    ((orbitFaceDualGraph data).induce (cell data B root)).Connected := by
  have h : ((barrierDual data B).induce (cell data B root)).Connected :=
    ((barrierDual data B).connectedComponentMk root).connected_toSimpleGraph
  have hle : (barrierDual data B).induce (cell data B root) ≤
      (orbitFaceDualGraph data).induce (cell data B root) := fun _ _ hadj => hadj.1
  exact SimpleGraph.Connected.mono hle h

/-- Every original edge separating a cell from another face is a barrier
edge. All face occurrences are used, including lateral attachments. -/
theorem cell_crossing_in_barrier (data : Data G) (B : Finset G.edgeSet)
    (root : OrbitFace data.toRotationSystem) {f g : OrbitFace data.toRotationSystem}
    (hf : f ∈ cell data B root) (hg : g ∉ cell data B root)
    {e : G.edgeSet} (hef : e ∈ orbitFaceBoundary data.toRotationSystem f)
    (heg : e ∈ orbitFaceBoundary data.toRotationSystem g) : e ∈ B := by
  by_contra he
  have hne : f ≠ g := by rintro rfl; exact hg hf
  have hadj : (orbitFaceDualGraph data).Adj f g :=
    interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary data.toRotationSystem) Finset.univ
      (orbitFace_incidence_le_two data.toRotationSystem) hne hef heg
  exact hg (((barrierDual data B).connectedComponentMk root).mem_supp_of_adj_mem_supp
    hf ⟨hadj, e, he, hef, heg⟩)

theorem face_cycle (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (f : OrbitFace data.toRotationSystem) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ {x | x ∈ p.support} = faceVertices data f := by
  obtain ⟨d, hd⟩ := exists_dartOrbitFace_eq data.toRotationSystem f
  obtain ⟨p, hp, hdarts, _⟩ := exists_rootedFaceCycle data hc ht d
  refine ⟨d.fst, p, hp, ?_⟩
  ext v
  change v ∈ p.support ↔ ∃ e : G.Dart, e.fst = v ∧ dartOrbitFace data.toRotationSystem e = f
  rw [← p.map_fst_darts_append, hdarts, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro (⟨e, he, rfl⟩ | rfl)
    · exact ⟨e, rfl, ((mem_faceOrbitDarts_iff data d e).mp he).trans hd⟩
    · exact ⟨d, rfl, hd⟩
  · rintro ⟨e, hev, hef⟩
    exact Or.inl ⟨e, (mem_faceOrbitDarts_iff data d e).mpr (hef.trans hd.symm), hev⟩

theorem face_connected (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (f : OrbitFace data.toRotationSystem) :
    (G.induce (faceVertices data f)).Connected := by
  obtain ⟨v, p, _, heq⟩ := face_cycle data hc ht f
  rw [← heq]
  exact p.connected_induce_support

theorem dart_snd_mem_face (data : Data G) (d : G.Dart) :
    d.snd ∈ faceVertices data (dartOrbitFace data.toRotationSystem d) := by
  refine ⟨data.toRotationSystem.phi d, ?_, dartOrbitFace_phi_eq data.toRotationSystem d⟩
  exact data.toRotationSystem.vert_phi_eq_vert_alpha d

theorem adjacent_faces_overlap (data : Data G) {f g : OrbitFace data.toRotationSystem}
    (h : (orbitFaceDualGraph data).Adj f g) :
    (faceVertices data f ∩ faceVertices data g).Nonempty := by
  obtain ⟨_, e, _, hef, heg⟩ := h
  obtain ⟨d, hd, hde⟩ := (mem_orbitFaceBoundary_iff _ f e).mp hef
  obtain ⟨a, ha, hae⟩ := (mem_orbitFaceBoundary_iff _ g e).mp heg
  have hdf := (mem_orbitFaceDarts_iff _ f d).mp hd
  have hag := (mem_orbitFaceDarts_iff _ g a).mp ha
  have hsame : d.edge = a.edge := congrArg Subtype.val (hde.trans hae.symm)
  refine ⟨d.fst, ⟨d, rfl, hdf⟩, ?_⟩
  rcases (SimpleGraph.dart_edge_eq_iff d a).mp hsame with h | h
  · subst d
    exact ⟨a, rfl, hag⟩
  · rw [h]
    simpa [hag] using dart_snd_mem_face data a

theorem closedVertices_mono (data : Data G) : Monotone (closedVertices data) := by
  rintro R S h v ⟨f, hf, hv⟩
  exact ⟨f, h hf, hv⟩

theorem walk_closed_connected (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem)
    {f g : OrbitFace data.toRotationSystem} (p : (orbitFaceDualGraph data).Walk f g) :
    (G.induce (closedVertices data {h | h ∈ p.support})).Connected := by
  induction p with
  | @nil f =>
    have heq : closedVertices data {q | q ∈ ([f] : List _)} = faceVertices data f := by
      ext v
      simp only [closedVertices, Set.mem_setOf_eq, List.mem_singleton, exists_eq_left]
    change (G.induce (closedVertices data {q | q ∈ ([f] : List _)})).Connected
    rw [heq]
    exact face_connected data hc ht f
  | @cons f h g hadj p ih =>
    have heq : closedVertices data {q | q ∈ (p.cons hadj).support} =
        faceVertices data f ∪ closedVertices data {q | q ∈ p.support} := by
      ext v
      simp only [closedVertices, Set.mem_setOf_eq, SimpleGraph.Walk.support_cons, List.mem_cons,
        Set.mem_union]
      aesop
    rw [heq]
    apply G.induce_union_connected (face_connected data hc ht f).preconnected ih.preconnected
    obtain ⟨v, hvf, hvh⟩ := adjacent_faces_overlap data hadj
    exact ⟨v, hvf, h, p.start_mem_support, hvh⟩

/-- Connectivity is constructed from a dual walk of actual faces. -/
theorem closed_connected (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem)
    {R : Set (OrbitFace data.toRotationSystem)}
    (hR : ((orbitFaceDualGraph data).induce R).Connected) :
    (G.induce (closedVertices data R)).Connected := by
  obtain ⟨f⟩ := hR.nonempty
  obtain ⟨u⟩ := (face_connected data hc ht f.val).nonempty
  apply SimpleGraph.induce_connected_of_patches (G := G) (s := closedVertices data R)
    u.val ⟨f.val, f.property, u.property⟩
  rintro v ⟨g, hg, hv⟩
  obtain ⟨p, hp⟩ := exists_walk_in (orbitFaceDualGraph data) hR f.property hg
  let S := closedVertices data {h | h ∈ p.support}
  have hS := walk_closed_connected data hc ht p
  have huS : u.val ∈ S := ⟨f.val, p.start_mem_support, u.property⟩
  have hvS : v ∈ S := ⟨g, p.end_mem_support, hv⟩
  exact ⟨S, closedVertices_mono data hp, huS, hvS, hS ⟨u.val, huS⟩ ⟨v, hvS⟩⟩

/-- Fill every complementary component except the one containing b. -/
def filled (S : Set V) (b : V) : Set V := (flood G Sᶜ {b})ᶜ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem subset_filled (S : Set V) (b : V) : S ⊆ filled (G := G) S b := by
  intro v hv h
  exact flood_subset G Sᶜ {b} h hv

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem filled_mono (b : V) : Monotone (fun S => filled (G := G) S b) := by
  rintro S T h v hv ⟨a, ha, p, hp⟩
  exact hv ⟨a, ha, p, fun x hx hs => hp x hx (h hs)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem filled_idem (S : Set V) (b : V) :
    filled (G := G) (filled (G := G) S b) b = filled (G := G) S b := by
  apply Set.Subset.antisymm ?_ (subset_filled _ b)
  intro v hv
  by_contra h
  have hf : v ∈ flood G Sᶜ {b} := not_not.mp h
  obtain ⟨a, ha, p, hp⟩ := hf
  apply hv
  exact ⟨a, ha, p, fun x hx => not_not.mpr (support_subset_flood G ha p hp x hx)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Adding faces need not advance a filled side: a new vertex must meet the
old retained exterior. This is the exact strict-growth criterion. -/
theorem filled_strict_iff {S T : Set V} (hST : S ⊆ T) (b : V) :
    filled (G := G) S b ⊂ filled (G := G) T b ↔
      ∃ v ∈ T, v ∉ filled (G := G) S b := by
  constructor
  · intro h
    by_contra hnone
    have hT : T ⊆ filled (G := G) S b := by
      intro v hv
      by_contra hn
      exact hnone ⟨v, hv, hn⟩
    have hle : filled (G := G) T b ⊆ filled (G := G) (filled (G := G) S b) b :=
      filled_mono b hT
    rw [filled_idem] at hle
    exact h.not_ge hle
  · rintro ⟨v, hv, hn⟩
    exact ⟨filled_mono b hST, fun h => hn (h (subset_filled T b hv))⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A crossing edge of the hull already crossed the original closed side. -/
theorem filled_crossing {S : Set V} {b u v : V} (h : G.Adj u v)
    (hu : u ∈ filled (G := G) S b) (hv : v ∉ filled (G := G) S b) :
    u ∈ S ∧ v ∉ S := by
  have hvf : v ∈ flood G Sᶜ {b} := by simpa [filled] using hv
  refine ⟨?_, flood_subset G Sᶜ {b} hvf⟩
  by_contra hus
  exact hu (flood_adj G hvf h.symm hus)

theorem filled_boundary_subset (S : Set V) (b : V) :
    edgeBoundary G (filled (G := G) S b) ⊆ edgeBoundary G S := by
  classical
  rintro e he
  obtain ⟨he, u, hue, hu, v, hve, hv⟩ := Finset.mem_filter.mp he
  have heG := G.mem_edgeFinset.mp he
  have hne : u ≠ v := by rintro rfl; exact hv hu
  have huv := G.adj_of_mem_incidenceSet hne
    ((G.edge_mem_incidenceSet_iff (e := ⟨e, heG⟩)).mpr hue)
    ((G.edge_mem_incidenceSet_iff (e := ⟨e, heG⟩)).mpr hve)
  obtain ⟨huS, hvS⟩ := filled_crossing huv hu hv
  exact Finset.mem_filter.mpr ⟨he, u, hue, huS, v, hve, hvS⟩

def hull (data : Data G) (R : Set (OrbitFace data.toRotationSystem)) (b : V) : Set V :=
  filled (G := G) (closedVertices data R) b

/-- The hull supplies both connected vertex shores without assuming a
simple cell rim or connectivity of the original vertex complement. -/
theorem hull_connected_sides (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (hG : G.Connected)
    {R : Set (OrbitFace data.toRotationSystem)}
    (hR : ((orbitFaceDualGraph data).induce R).Connected)
    {b : V} (hb : b ∉ closedVertices data R) :
    (G.induce (hull data R b)).Connected ∧ (G.induce (hull data R b)ᶜ).Connected := by
  refine ⟨filled_connected G hG (closed_connected data hc ht hR) b, ?_⟩
  have heq : (hull data R b)ᶜ = flood G (closedVertices data R)ᶜ {b} := by
    ext v
    exact not_not
  rw [heq]
  exact flood_singleton_connected G (U := (closedVertices data R)ᶜ) (b := b) hb

theorem hull_mono (data : Data G) (b : V) : Monotone (fun R => hull data R b) :=
  (filled_mono b).comp (closedVertices_mono data)

theorem hull_boundary_subset (data : Data G) (R : Set (OrbitFace data.toRotationSystem))
    (b : V) : edgeBoundary G (hull data R b) ⊆ edgeBoundary G (closedVertices data R) :=
  filled_boundary_subset _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An entire connected outside set is retained, not just its anchor. -/
theorem outside_kept {S B : Set V} (hB : (G.induce B).Connected)
    {b : V} (hb : b ∈ B) (hBS : B ⊆ Sᶜ) : B ⊆ (filled (G := G) S b)ᶜ := by
  intro v hv
  obtain ⟨p, hp⟩ := exists_walk_in G hB hb hv
  have hf : v ∈ flood G Sᶜ {b} := ⟨b, rfl, p, fun x hx => hBS (hp x hx)⟩
  simpa only [filled, compl_compl] using hf

theorem face_hasCycle (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (f : OrbitFace data.toRotationSystem) :
    HasCycleOnSide G (fun v => v ∈ faceVertices data f) := by
  obtain ⟨v, p, hp, heq⟩ := face_cycle data hc ht f
  have hsub : ∀ x ∈ p.support, x ∈ faceVertices data f := fun x hx => heq ▸ hx
  exact ⟨v, hsub v p.start_mem_support, p, hp, hsub⟩

/-- An inner face and a disjoint outside face give cycles on both hull sides. -/
theorem hull_hasCycles (data : Data G) (hc : data.toRotationSystem.IsCubic)
    (ht : OrbitFacesTwoSided data.toRotationSystem)
    {R : Set (OrbitFace data.toRotationSystem)} (hR : R.Nonempty)
    {f : OrbitFace data.toRotationSystem} (hf : Disjoint (faceVertices data f) (closedVertices data R))
    {b : V} (hb : b ∈ faceVertices data f) :
    HasCycleOnSide G (fun v => v ∈ hull data R b) ∧
      HasCycleOnSide G (fun v => v ∉ hull data R b) := by
  obtain ⟨g, hg⟩ := hR
  refine ⟨HasCycleOnSide.mono (fun v hv => subset_filled _ b ⟨g, hg, hv⟩)
    (face_hasCycle data hc ht g), ?_⟩
  exact HasCycleOnSide.mono
    (fun v hv => outside_kept (face_connected data hc ht f) hb
      (fun x hx => Set.disjoint_left.mp hf hx) hv)
    (face_hasCycle data hc ht f)

/-- Deleting the retained outside component represents exactly the hull. -/
def deleted (data : Data G) (R : Set (OrbitFace data.toRotationSystem)) (b : V) : Finset V :=
  (hull data R b)ᶜ.toFinset

@[simp] theorem keep_deleted (data : Data G) (R : Set (OrbitFace data.toRotationSystem))
    (b v : V) : deletedRegionKeep (deleted data R b) v ↔ v ∈ hull data R b := by
  classical
  simp only [deletedRegionKeep, deleted, Set.mem_toFinset, Set.mem_compl_iff, not_not]

/-- The complete constructed bond has the exact complementary facial order. -/
theorem hull_boundary_order (data : Data G)
    (hs : OrbitSphericalCubicMapData data.toRotationSystem)
    (ht : OrbitFacesTwoSided data.toRotationSystem) (hG : G.Connected)
    (hr : VertexRotationCyclic data.toRotationSystem)
    {R : Set (OrbitFace data.toRotationSystem)}
    (hR : ((orbitFaceDualGraph data).induce R).Connected)
    {b : V} (hb : b ∉ closedVertices data R) :
    CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem (deleted data R b) ∧
      retainedRegionBoundarySuccessor data.toRotationSystem
        (deletedRegionKeep (deleted data R b)) =
        (deletedRegionBoundarySuccessor data.toRotationSystem (deleted data R b))⁻¹ := by
  obtain ⟨hi, ho⟩ := hull_connected_sides data hs.cubic ht hG hR hb
  have hside : {v | deletedRegionKeep (deleted data R b) v} = hull data R b :=
    Set.ext (keep_deleted data R b)
  have hcomp : {v | ¬ deletedRegionKeep (deleted data R b) v} = (hull data R b)ᶜ :=
    Set.ext (fun v => not_congr (keep_deleted data R b v))
  have hi' : (G.induce {v | deletedRegionKeep (deleted data R b) v}).Connected := by
    rw [hside]
    exact hi
  have ho' : (G.induce {v | ¬ deletedRegionKeep (deleted data R b) v}).Connected := by
    rw [hcomp]
    exact ho
  exact ⟨cutFacesHaveUniqueRetainedBoundaryDart_of_planar_bond data _ hs ht hG hr hi' ho',
    retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond data _ hs ht hG hr hi' ho'⟩

end
end Mettapedia.GraphTheory.FourColor.FaceRegionHull
