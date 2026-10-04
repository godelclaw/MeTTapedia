import MettapediaFourColor.StripSourceExtension
import Mettapedia.GraphTheory.FourColor.PrimalPathSeparation

/-!
# A connection around the last D0099 port supplies a separator

Close an exterior path from port eight to port ten through the source
route 8,15,17,10. The two facial triangles incident to the internal edge
15--17 put port nine and the remaining active ports on opposite sides of
the closed walk's face potential. A disjoint exterior path cannot cross.
The exterior path may be arbitrarily long and need not be simple.
-/

namespace FourColor.StripConnectionGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24WalkFaceParityCut GoertzelV24WalkCycleParity
open GoertzelV24OrbitFaceParityBoundary GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation TriangleStripAnchors

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable section

def triangles : List (Fin 19 × Fin 19 × Fin 19) := [(9,17,15),(13,15,17)]
def otherPort (i : Fin 5) : Fin 19 := ⟨i.val + 3,by omega⟩

def tailRoute : (i : Fin 5) → input0099.graph.Walk (otherPort i) 13
  | ⟨0,_⟩ => .cons (by change input0099.graph.Adj 3 16; decide +kernel)
      (.cons (by decide +kernel : input0099.graph.Adj 16 13) .nil)
  | ⟨1,_⟩ => .cons (by change input0099.graph.Adj 4 13; decide +kernel) .nil
  | ⟨2,_⟩ => .cons (by change input0099.graph.Adj 5 14; decide +kernel)
      (.cons (by decide +kernel : input0099.graph.Adj 14 13) .nil)
  | ⟨3,_⟩ => .cons (by change input0099.graph.Adj 6 14; decide +kernel)
      (.cons (by decide +kernel : input0099.graph.Adj 14 13) .nil)
  | ⟨4,_⟩ => .cons (by change input0099.graph.Adj 7 11; decide +kernel)
      (.cons (by decide +kernel : input0099.graph.Adj 11 12)
        (.cons (by decide +kernel) .nil))

theorem tail_support : ∀ i x, x ∈ (tailRoute i).support →
    (x = otherPort i ∨ 11 ≤ x.val) ∧ x ∉ ([8,15,17,10] : List (Fin 19)) := by
  decide +kernel

/-- Only actual source edges and the two facial turns are assumed. -/
structure Patch (data : Data G) where
  point : Fin 19 → V
  injective : Function.Injective point
  adjacent : ∀ i j, input0099.graph.Adj i j → G.Adj (point i) (point j)
  facial : ∀ a b c, (a, b, c) ∈ triangles →
    ∃ (ab : G.Adj (point a) (point b)) (bc : G.Adj (point b) (point c))
      (ca : G.Adj (point c) (point a)),
      data.toRotationSystem.phi ⟨(point a,point b),ab⟩ = ⟨(point b,point c),bc⟩ ∧
      data.toRotationSystem.phi ⟨(point b,point c),bc⟩ = ⟨(point c,point a),ca⟩ ∧
      data.toRotationSystem.phi ⟨(point c,point a),ca⟩ = ⟨(point a,point b),ab⟩

namespace Patch
variable {data : Data G} (s : Patch data)

abbrev sourceHom : input0099.graph →g G := ⟨s.point,fun h => s.adjacent _ _ h⟩
def dart (i j : Fin 19) (h : input0099.graph.Adj i j) : G.Dart :=
  ⟨(s.point i,s.point j),s.adjacent i j h⟩
def coreRoute : G.Walk (s.point 8) (s.point 10) :=
  .cons (s.adjacent 8 15 (by decide +kernel))
    (.cons (s.adjacent 15 17 (by decide +kernel))
      (.cons (s.adjacent 17 10 (by decide +kernel)) .nil))
def Exterior (v : V) : Prop := ∀ i : Fin 19, 11 ≤ i.val → v ≠ s.point i

theorem face_labels (labels : OrbitFace data.toRotationSystem → F2)
    (a b c : Fin 19) (h : (a, b, c) ∈ triangles)
    (ab : input0099.graph.Adj a b) (bc : input0099.graph.Adj b c) :
    labels (dartOrbitFace data.toRotationSystem (s.dart a b ab)) =
      labels (dartOrbitFace data.toRotationSystem (s.dart b c bc)) := by
  obtain ⟨_,_,_,hab,_,_⟩ := s.facial a b c h
  have first := dartOrbitFace_phi_eq data.toRotationSystem (s.dart a b ab)
  rw [show data.toRotationSystem.phi (s.dart a b ab) = s.dart b c bc from hab] at first
  exact congrArg labels first.symm

theorem separated_faces (p : G.Walk (s.point 8) (s.point 10))
    (outside : ∀ x ∈ p.support, s.Exterior x)
    (labels : OrbitFace data.toRotationSystem → F2)
    (potential : orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
      walkEdgeParity (s.coreRoute.append p.reverse)) :
    labels (dartOrbitFace data.toRotationSystem (s.dart 9 17 (by decide +kernel))) ≠
      labels (dartOrbitFace data.toRotationSystem (s.dart 13 15 (by decide +kernel))) := by
  have absent : s(s.point 15,s.point 17) ∉ p.edges := fun h =>
    outside _ (p.fst_mem_support_of_mem_edges h) 15 (by decide) rfl
  have eqs : ∀ i j : Fin 19, s.point i = s.point j ↔ i = j :=
    fun _ _ => s.injective.eq_iff
  have crossing := congrFun potential
    (data.toRotationSystem.edgeOf (s.dart 15 17 (by decide +kernel)))
  rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf data.toRotationSystem labels
    (s.dart 15 17 (by decide +kernel))] at crossing
  have parity : walkEdgeParity (s.coreRoute.append p.reverse)
      (data.toRotationSystem.edgeOf (s.dart 15 17 (by decide +kernel))) = 1 := by
    simp [walkEdgeParity,Walk.edges_reverse,coreRoute,dart,
      Data.toRotationSystem,eqs,List.count_eq_zero.mpr absent]
  rw [parity] at crossing
  have different := (f2_add_eq_one_iff_ne _ _).mp crossing
  have f0 := s.face_labels labels 9 17 15 (by decide) (by decide +kernel) (by decide +kernel)
  have f1 := s.face_labels labels 13 15 17 (by decide) (by decide +kernel) (by decide +kernel)
  intro same
  exact different (f1.symm.trans (same.symm.trans f0))

/-- The supplied connection excludes all complementary connections across it. -/
theorem no_crossing_paths
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (p : G.Walk (s.point 8) (s.point 10))
    (outsideP : ∀ x ∈ p.support, s.Exterior x)
    (i : Fin 5) (q : G.Walk (s.point 9) (s.point (otherPort i)))
    (outsideQ : ∀ x ∈ q.support, s.Exterior x)
    (disjoint : ∀ x ∈ q.support, x ∉ p.support) : False := by
  obtain ⟨labels,potential⟩ := exists_orbitFaceLabeling_eq_walkEdgeParity
    data dual connected euler (s.coreRoute.append p.reverse)
  have qavoid : ∀ x ∈ q.support, x ∉ (s.coreRoute.append p.reverse).support := by
    intro x hx hc
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hc
    rcases hc with hc | hc
    · simp only [coreRoute,Walk.support_cons,Walk.support_nil,List.mem_cons,
        List.not_mem_nil,or_false] at hc
      rcases hc with h | h | h | h
      · exact disjoint x hx (h ▸ p.start_mem_support)
      · exact outsideQ x hx 15 (by decide) h
      · exact outsideQ x hx 17 (by decide) h
      · exact disjoint x hx (h ▸ p.end_mem_support)
    · exact disjoint x hx hc
  let t : G.Walk (s.point (otherPort i)) (s.point 13) :=
    (tailRoute i).map s.sourceHom
  have tavoid : ∀ x ∈ t.support, x ∉ (s.coreRoute.append p.reverse).support := by
    intro x hx hc
    simp only [t,Walk.support_map,List.mem_map] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨kind,distinct⟩ := tail_support i a ha
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hc
    rcases hc with hc | hc
    · have eqs : ∀ b : Fin 19, s.sourceHom a = s.point b ↔ a = b :=
        fun _ => s.injective.eq_iff
      simp only [coreRoute,Walk.support_cons,Walk.support_nil,List.mem_cons,
        List.not_mem_nil,or_false,eqs] at hc
      exact distinct (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hc)
    · rcases kind with rfl | core
      · exact disjoint _ q.end_mem_support hc
      · exact outsideP _ hc a core rfl
  have equality := PrimalPathSeparation.labels_eq_of_disjoint_walk data rotation
    (s.coreRoute.append p.reverse) (q.append t)
    (by intro x hx; rw [Walk.mem_support_append_iff] at hx; rcases hx with h | h
        · exact qavoid x h
        · exact tavoid x h)
    labels potential (s.dart 9 17 (by decide +kernel))
      (s.dart 13 15 (by decide +kernel)) rfl rfl
  exact s.separated_faces p outsideP labels potential equality

end Patch
end
end FourColor.StripConnectionGeometry
