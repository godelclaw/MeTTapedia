import MettapediaFourColor.StripSourceExtension
import Mettapedia.GraphTheory.FourColor.PrimalPathSeparation

/-!
# Two source chords protect the same outer ports

An exterior path from port two to port four or seven closes through the
D0099 core. Two actual facial triangles along edge 16--13 separate port
three from ports one, nine and ten. The paths and the exterior are unbounded.
-/

namespace FourColor.StripSixBarrierGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24WalkFaceParityCut GoertzelV24WalkCycleParity
open GoertzelV24OrbitFaceParityBoundary GoertzelV24PrimalCycleSpace
open SimpleGraphDartRotation TriangleStripAnchors

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
noncomputable section

def triangles : List (Fin 19 × Fin 19 × Fin 19) := [(3,16,13),(17,13,16)]
def target (long : Bool) : Fin 19 := if long then 7 else 4
def otherPort : Fin 3 → Fin 19 := ![1,9,10]

def returnRoute : (long : Bool) → input0099.graph.Walk 2 (target long)
  | false => .cons (by decide +kernel : input0099.graph.Adj 2 16)
      (.cons (by decide +kernel : input0099.graph.Adj 16 13)
        (.cons (by decide +kernel) .nil))
  | true => .cons (by decide +kernel : input0099.graph.Adj 2 16)
      (.cons (by decide +kernel : input0099.graph.Adj 16 13)
        (.cons (by decide +kernel : input0099.graph.Adj 13 14)
          (.cons (by decide +kernel : input0099.graph.Adj 14 11)
            (.cons (by decide +kernel) .nil))))

theorem route_support : ∀ long i, i ∈ (returnRoute long).support →
    i = 2 ∨ i = target long ∨ 11 ≤ i.val := by decide +kernel

def tailRoute : (i : Fin 3) → input0099.graph.Walk (otherPort i) 17
  | ⟨0,_⟩ => .cons (by change input0099.graph.Adj 1 18; decide +kernel)
      (.cons (by decide +kernel) .nil)
  | ⟨1,_⟩ => .cons (by change input0099.graph.Adj 9 17; decide +kernel) .nil
  | ⟨2,_⟩ => .cons (by change input0099.graph.Adj 10 17; decide +kernel) .nil

theorem tail_support : ∀ long i x, x ∈ (tailRoute i).support →
    (x = otherPort i ∨ 11 ≤ x.val) ∧ x ∉ (returnRoute long).support := by decide +kernel

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
def coreRoute (long : Bool) := (returnRoute long).map s.sourceHom
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

theorem separated_faces (long : Bool)
    (p : G.Walk (s.point 2) (s.point (target long)))
    (outside : ∀ x ∈ p.support, s.Exterior x)
    (labels : OrbitFace data.toRotationSystem → F2)
    (potential : orbitFaceParityBoundaryLinearMap data.toRotationSystem labels =
      walkEdgeParity ((s.coreRoute long).append p.reverse)) :
    labels (dartOrbitFace data.toRotationSystem (s.dart 3 16 (by decide +kernel))) ≠
      labels (dartOrbitFace data.toRotationSystem (s.dart 17 13 (by decide +kernel))) := by
  have absent : s(s.point 16,s.point 13) ∉ p.edges := fun h =>
    outside _ (p.fst_mem_support_of_mem_edges h) 16 (by decide) rfl
  have eqs : ∀ i j : Fin 19, s.point i = s.point j ↔ i = j :=
    fun _ _ => s.injective.eq_iff
  have crossing := congrFun potential
    (data.toRotationSystem.edgeOf (s.dart 16 13 (by decide +kernel)))
  rw [orbitFaceParityBoundaryLinearMap_apply_edgeOf data.toRotationSystem labels
    (s.dart 16 13 (by decide +kernel))] at crossing
  have parity : walkEdgeParity ((s.coreRoute long).append p.reverse)
      (data.toRotationSystem.edgeOf (s.dart 16 13 (by decide +kernel))) = 1 := by
    cases long
    · change (↑(List.count s(s.point 16,s.point 13)
        ([s(s.point 2,s.point 16),s(s.point 16,s.point 13),s(s.point 13,s.point 4)] ++
          p.reverse.edges)) : F2) = 1
      simp [Walk.edges_reverse,eqs,List.count_eq_zero.mpr absent]
    · change (↑(List.count s(s.point 16,s.point 13)
        ([s(s.point 2,s.point 16),s(s.point 16,s.point 13),s(s.point 13,s.point 14),
          s(s.point 14,s.point 11),s(s.point 11,s.point 7)] ++ p.reverse.edges)) : F2) = 1
      simp [Walk.edges_reverse,eqs,List.count_eq_zero.mpr absent]
  rw [parity] at crossing
  have different := (f2_add_eq_one_iff_ne _ _).mp crossing
  have f0 := s.face_labels labels 3 16 13 (by decide) (by decide +kernel) (by decide +kernel)
  have f1 := s.face_labels labels 17 13 16 (by decide) (by decide +kernel) (by decide +kernel)
  intro same
  exact different (f0.symm.trans (same.trans f1))

/-- Either chord separates the central port from the three retained ports. -/
theorem no_crossing_paths
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (long : Bool) (p : G.Walk (s.point 2) (s.point (target long)))
    (outsideP : ∀ x ∈ p.support, s.Exterior x)
    (i : Fin 3) (q : G.Walk (s.point 3) (s.point (otherPort i)))
    (outsideQ : ∀ x ∈ q.support, s.Exterior x)
    (disjoint : ∀ x ∈ q.support, x ∉ p.support) : False := by
  obtain ⟨labels,potential⟩ := exists_orbitFaceLabeling_eq_walkEdgeParity
    data dual connected euler ((s.coreRoute long).append p.reverse)
  have qavoid : ∀ x ∈ q.support, x ∉ ((s.coreRoute long).append p.reverse).support := by
    intro x hx hc
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hc
    rcases hc with hc | hc
    · change x ∈ ((returnRoute long).map s.sourceHom).support at hc
      rw [Walk.support_map,List.mem_map] at hc
      obtain ⟨a,ha,eq⟩ := hc
      rcases route_support long a ha with h | h | h
      · subst a; exact disjoint x hx (eq ▸ p.start_mem_support)
      · subst a; exact disjoint x hx (eq ▸ p.end_mem_support)
      · exact outsideQ x hx a h eq.symm
    · exact disjoint x hx hc
  let t : G.Walk (s.point (otherPort i)) (s.point 17) := (tailRoute i).map s.sourceHom
  have tavoid : ∀ x ∈ t.support, x ∉ ((s.coreRoute long).append p.reverse).support := by
    intro x hx hc
    simp only [t,Walk.support_map,List.mem_map] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨kind,distinct⟩ := tail_support long i a ha
    rw [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hc
    rcases hc with hc | hc
    · change s.sourceHom a ∈ ((returnRoute long).map s.sourceHom).support at hc
      rw [Walk.support_map,List.mem_map] at hc
      obtain ⟨b,hb,eq⟩ := hc
      exact distinct ((s.injective eq) ▸ hb)
    · rcases kind with rfl | core
      · exact disjoint _ q.end_mem_support hc
      · exact outsideP _ hc a core rfl
  have equality := PrimalPathSeparation.labels_eq_of_disjoint_walk data rotation
    ((s.coreRoute long).append p.reverse) (q.append t)
    (by intro x hx; rw [Walk.mem_support_append_iff] at hx; rcases hx with h | h
        · exact qavoid x h
        · exact tavoid x h)
    labels potential (s.dart 3 16 (by decide +kernel))
      (s.dart 17 13 (by decide +kernel)) rfl rfl
  exact s.separated_faces long p outsideP labels potential equality

end Patch
end
end FourColor.StripSixBarrierGeometry
