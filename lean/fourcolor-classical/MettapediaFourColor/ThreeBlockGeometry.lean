import MettapediaFourColor.ThreeBlockCore
import Mettapedia.GraphTheory.FourColor.PrimalPathSeparation

/-!
# A complementary exterior path separates the three D0092 boundary runs

Close a path from port 1 to port 6 through the fixed core route
`1,15,12,13,6`. Seven source facial triangles then place ports 2 and 5
on the opposite face-potential side from port 7. Any exterior path
disjoint from the first path preserves that potential and cannot connect
either of those ports to port 7. No bound on exterior size or degree is
used. Availability of the complementary path is a separate question.

The source and attribution are inherited from `ThreeBlockCore`.
-/

namespace FourColor.ThreeBlockGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24WalkFaceParityCut GoertzelV24WalkCycleParity
open GoertzelV24OrbitFaceParityBoundary GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation FiveTriangleCollapseObstruction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Only the seven facial triangles used by the two dual routes. -/
def triangles : List (Fin 18 × Fin 18 × Fin 18) :=
  [(2,3,15), (3,12,15), (11,15,12), (11,12,14),
   (12,13,14), (7,14,13), (5,13,12)]

/-- An injective source reading preserving actual edges and the specified
facial rotations. No component separation or repair is included. -/
structure Patch (data : Data G) where
  point : Fin 18 → V
  injective : Function.Injective point
  adjacent : ∀ i j, upper.graph.Adj i j → G.Adj (point i) (point j)
  facial : ∀ a b c, (a,b,c) ∈ triangles →
    ∃ (ab : G.Adj (point a) (point b)) (bc : G.Adj (point b) (point c))
      (ca : G.Adj (point c) (point a)),
      data.toRotationSystem.phi ⟨(point a, point b), ab⟩ = ⟨(point b, point c), bc⟩ ∧
      data.toRotationSystem.phi ⟨(point b, point c), bc⟩ = ⟨(point c, point a), ca⟩ ∧
      data.toRotationSystem.phi ⟨(point c, point a), ca⟩ = ⟨(point a, point b), ab⟩

namespace Patch

variable {data : Data G} (s : Patch data)

def dart (i j : Fin 18) (h : upper.graph.Adj i j) : G.Dart :=
  ⟨(s.point i, s.point j), s.adjacent i j h⟩

def coreRoute : G.Walk (s.point 1) (s.point 6) :=
  .cons (s.adjacent 1 15 (by decide +kernel))
    (.cons (s.adjacent 15 12 (by decide +kernel))
      (.cons (s.adjacent 12 13 (by decide +kernel))
        (.cons (s.adjacent 13 6 (by decide +kernel)) .nil)))

def Exterior (v : V) : Prop := ∀ i : Fin 18, 11 ≤ i.val → v ≠ s.point i

theorem face_labels (labels : OrbitFace data.toRotationSystem → F2)
    (a b c : Fin 18) (h : (a,b,c) ∈ triangles)
    (ab : upper.graph.Adj a b) (bc : upper.graph.Adj b c) (ca : upper.graph.Adj c a) :
    labels (dartOrbitFace data.toRotationSystem (s.dart a b ab)) =
        labels (dartOrbitFace data.toRotationSystem (s.dart b c bc)) ∧
    labels (dartOrbitFace data.toRotationSystem (s.dart a b ab)) =
        labels (dartOrbitFace data.toRotationSystem (s.dart c a ca)) := by
  obtain ⟨_, _, _, hab, hbc, _⟩ := s.facial a b c h
  have first := dartOrbitFace_phi_eq data.toRotationSystem (s.dart a b ab)
  have second := dartOrbitFace_phi_eq data.toRotationSystem (s.dart b c bc)
  rw [show data.toRotationSystem.phi (s.dart a b ab) = s.dart b c bc from hab] at first
  rw [show data.toRotationSystem.phi (s.dart b c bc) = s.dart c a ca from hbc] at second
  exact ⟨congrArg labels first.symm, congrArg labels (first.symm.trans second.symm)⟩

/-- At an edge incident to a core vertex, an exterior walk contributes zero
to the closed walk's parity. -/
theorem closed_parity (p : G.Walk (s.point 1) (s.point 6))
    (outside : ∀ x ∈ p.support, s.Exterior x)
    (i j : Fin 18) (edge : upper.graph.Adj i j) (core : 11 ≤ i.val ∨ 11 ≤ j.val) :
    walkEdgeParity (s.coreRoute.append p.reverse)
        (data.toRotationSystem.edgeOf (s.dart i j edge)) =
      walkEdgeParity s.coreRoute (data.toRotationSystem.edgeOf (s.dart i j edge)) := by
  have absent : s(s.point i, s.point j) ∉ p.edges := by
    intro h
    rcases core with hi | hj
    · exact outside _ (p.fst_mem_support_of_mem_edges h) i hi rfl
    · exact outside _ (p.snd_mem_support_of_mem_edges h) j hj rfl
  simp [walkEdgeParity, Walk.edges_append, Walk.edges_reverse,
    dart, Data.toRotationSystem, List.count_eq_zero.mpr absent]

/-- The source's two small dual routes cross the closed path oddly. -/
theorem separated_faces (p : G.Walk (s.point 1) (s.point 6))
    (outside : ∀ x ∈ p.support, s.Exterior x)
    (labels : OrbitFace data.toRotationSystem → F2)
    (potential : orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
      walkEdgeParity (s.coreRoute.append p.reverse)) :
    labels (dartOrbitFace data.toRotationSystem (s.dart 2 3 (by decide +kernel))) ≠
        labels (dartOrbitFace data.toRotationSystem (s.dart 7 14 (by decide +kernel))) ∧
    labels (dartOrbitFace data.toRotationSystem (s.dart 5 13 (by decide +kernel))) ≠
        labels (dartOrbitFace data.toRotationSystem (s.dart 7 14 (by decide +kernel))) := by
  let L (i j : Fin 18) (h : upper.graph.Adj i j) :=
    labels (dartOrbitFace data.toRotationSystem (s.dart i j h))
  have crossing (i j : Fin 18) (h : upper.graph.Adj i j) (core : 11 ≤ i.val ∨ 11 ≤ j.val) :
      L i j h + L j i h.symm =
        walkEdgeParity s.coreRoute (data.toRotationSystem.edgeOf (s.dart i j h)) := by
    have e := congrFun potential (data.toRotationSystem.edgeOf (s.dart i j h))
    rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf data.toRotationSystem labels (s.dart i j h),
      s.closed_parity p outside i j h core] at e
    exact e
  have at315 := crossing 3 15 (by decide +kernel) (by decide)
  have at1215 := crossing 12 15 (by decide +kernel) (by decide)
  have at1112 := crossing 11 12 (by decide +kernel) (by decide)
  have at1214 := crossing 12 14 (by decide +kernel) (by decide)
  have at1314 := crossing 13 14 (by decide +kernel) (by decide)
  have at1312 := crossing 13 12 (by decide +kernel) (by decide)
  have eqs : ∀ i j : Fin 18, s.point i = s.point j ↔ i = j :=
    fun _ _ => s.injective.eq_iff
  simp [walkEdgeParity, coreRoute, dart, Data.toRotationSystem, eqs] at at315 at1215 at1112 at1214 at1314 at1312
  have f0 := s.face_labels labels 2 3 15 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have f1 := s.face_labels labels 3 12 15 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have f2 := s.face_labels labels 11 15 12 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have f3 := s.face_labels labels 11 12 14 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have f4 := s.face_labels labels 12 13 14 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have f5 := s.face_labels labels 7 14 13 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have f6 := s.face_labels labels 5 13 12 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change L 2 3 _ ≠ L 7 14 _ ∧ L 5 13 _ ≠ L 7 14 _
  have zero_eq (a b : F2) (h : a + b = 0) : a = b := by
    have h' := congrArg (fun x => x + b) h
    simpa [add_assoc, zmod2_add_self] using h'
  have e0 := zero_eq _ _ at315
  have e2 := zero_eq _ _ at1112
  have e3 := zero_eq _ _ at1214
  have e4 := zero_eq _ _ at1314
  have n1 := (f2_add_eq_one_iff_ne _ _).mp at1215
  have n6 := (f2_add_eq_one_iff_ne _ _).mp at1312
  constructor
  · intro same
    apply n1
    calc
      L 12 15 _ = L 3 12 _ := f1.1.symm
      _ = L 15 3 _ := f1.2
      _ = L 3 15 _ := e0.symm
      _ = L 2 3 _ := f0.1.symm
      _ = L 7 14 _ := same
      _ = L 14 13 _ := f5.1
      _ = L 13 14 _ := e4.symm
      _ = L 12 13 _ := f4.1.symm
      _ = L 14 12 _ := f4.2
      _ = L 12 14 _ := e3.symm
      _ = L 11 12 _ := f3.1.symm
      _ = L 12 11 _ := e2
      _ = L 11 15 _ := f2.2.symm
      _ = L 15 12 _ := f2.1
  · intro same
    apply n6
    exact f6.1.symm.trans (same.trans (f5.1.trans (e4.symm.trans f4.1.symm)))

/-- A complementary exterior path forbids either crossing connection. -/
theorem no_crossing_paths
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (p : G.Walk (s.point 1) (s.point 6))
    (outsideP : ∀ x ∈ p.support, s.Exterior x)
    (i : Fin 18) (which : i = 2 ∨ i = 5)
    (q : G.Walk (s.point i) (s.point 7))
    (outsideQ : ∀ x ∈ q.support, s.Exterior x)
    (disjoint : ∀ x ∈ q.support, x ∉ p.support) : False := by
  obtain ⟨labels, potential⟩ := exists_orbitFaceLabeling_eq_walkEdgeParity
    data dual connected euler (s.coreRoute.append p.reverse)
  have avoid : ∀ x ∈ q.support, x ∉ (s.coreRoute.append p.reverse).support := by
    intro x hx hc
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hc
    rcases hc with hc | hc
    · simp only [coreRoute, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with h | h | h | h | h
      · exact disjoint x hx (h ▸ p.start_mem_support)
      · exact outsideQ x hx 15 (by decide) h
      · exact outsideQ x hx 12 (by decide) h
      · exact outsideQ x hx 13 (by decide) h
      · exact disjoint x hx (h ▸ p.end_mem_support)
    · exact disjoint x hx hc
  have separation := s.separated_faces p outsideP labels potential
  rcases which with rfl | rfl
  · exact separation.1 (PrimalPathSeparation.labels_eq_of_disjoint_walk data rotation
      _ q avoid labels potential (s.dart 2 3 (by decide +kernel))
      (s.dart 7 14 (by decide +kernel)) rfl rfl)
  · exact separation.2 (PrimalPathSeparation.labels_eq_of_disjoint_walk data rotation
      _ q avoid labels potential (s.dart 5 13 (by decide +kernel))
      (s.dart 7 14 (by decide +kernel)) rfl rfl)

end Patch
end
end FourColor.ThreeBlockGeometry
