import Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitch
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Spherical geometry of the three-switch matching cap

The matching-cap example carries a concrete bridgeless cubic sphere
rotation. All seventeen facial cycles have length five or six. The two
missing edges are disjoint and lie on one hexagonal face. The retained
edges come from a connected facial region with connected complement.
-/

namespace Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitchGeometry

open MatchingCapThreeSwitch GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge
open GoertzelV24CurvatureScope GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24TwoEdgeCutMinimality

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Dart := Fin 90
abbrev Face := Fin 17

def vertexOf : Dart → Vertex :=
  ![0, 1, 0, 2, 0, 3, 1, 4, 1, 5, 2, 6, 2, 7, 3, 8, 3, 9, 4, 9, 4, 10, 5, 6, 5, 11, 6, 12, 7, 8, 7, 13, 8, 14, 9, 15, 10, 16, 10, 17, 11, 17, 11, 18, 12, 18, 12, 19, 13, 19, 13, 20, 14, 20, 14, 21, 15, 16, 15, 21, 16, 22, 17, 23, 18, 24, 19, 25, 20, 26, 21, 27, 22, 23, 22, 28, 23, 24, 24, 29, 25, 26, 25, 29, 26, 27, 27, 28, 28, 29]

def edgeOf (d : Dart) : Edge := ⟨d.val / 2, by have := d.isLt; omega⟩

def flip : Equiv.Perm Dart where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62, 65, 64, 67, 66, 69, 68, 71, 70, 73, 72, 75, 74, 77, 76, 79, 78, 81, 80, 83, 82, 85, 84, 87, 86, 89, 88]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62, 65, 64, 67, 66, 69, 68, 71, 70, 73, 72, 75, 74, 77, 76, 79, 78, 81, 80, 83, 82, 85, 84, 87, 86, 89, 88]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def facePermutation : Equiv.Perm Dart where
  toFun := ![6, 2, 10, 4, 14, 0, 18, 8, 24, 1, 23, 12, 30, 3, 29, 16, 34, 5, 17, 20, 36, 7, 26, 9, 40, 22, 44, 11, 32, 13, 48, 28, 52, 15, 58, 19, 57, 38, 62, 21, 39, 42, 64, 25, 43, 46, 66, 27, 47, 50, 68, 31, 51, 54, 70, 33, 60, 35, 55, 56, 74, 37, 73, 41, 77, 45, 82, 49, 81, 53, 85, 59, 76, 61, 87, 72, 78, 63, 89, 65, 84, 67, 79, 80, 86, 69, 88, 71, 83, 75]
  invFun := ![5, 9, 1, 13, 3, 17, 0, 21, 7, 23, 2, 27, 11, 29, 4, 33, 15, 18, 6, 35, 19, 39, 25, 10, 8, 43, 22, 47, 31, 14, 12, 51, 28, 55, 16, 57, 20, 61, 37, 40, 24, 63, 41, 44, 26, 65, 45, 48, 30, 67, 49, 52, 32, 69, 53, 58, 59, 36, 34, 71, 56, 73, 38, 77, 42, 79, 46, 81, 50, 85, 54, 87, 75, 62, 60, 89, 72, 64, 76, 82, 83, 68, 66, 88, 80, 70, 84, 74, 86, 78]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rotation : RotationSystem Vertex Edge where
  D := Dart
  edgeOf := edgeOf
  vertOf := vertexOf
  alpha := flip
  rho := facePermutation * flip
  alpha_involutive := by decide +kernel
  alpha_fixfree := by decide +kernel
  edge_alpha := by decide +kernel
  edge_fiber_two := by decide +kernel
  vert_rho := by decide +kernel
  outer := 12
  no_self_loops := by decide +kernel

theorem endpoints_eq (e : Edge) : rotation.endpoints e = inc e := by
  revert e
  decide +kernel

theorem phi_eq : rotation.phi = facePermutation := by
  ext d
  change facePermutation (flip (flip d)) = facePermutation d
  rw [show flip (flip d) = d from rotation.alpha_involutive d]

theorem cubic : rotation.IsCubic := by
  change ∀ v : Vertex, (Finset.univ.filter fun d : Dart => vertexOf d = v).card = 3
  decide +kernel

theorem spherical : SphericalCubicMapData rotation := by
  refine ⟨cubic, ?_⟩
  change (30 : Int) - 45 + rotation.phi.partition.parts.card = 2
  rw [phi_eq]
  decide +kernel

theorem cyclic : VertexRotationCyclic rotation := by
  change ∀ d e : Dart, vertexOf d = vertexOf e → (facePermutation * flip).SameCycle d e
  decide +kernel

instance primalDecidableRel : DecidableRel (rotationPrimalGraph rotation).Adj := fun u v =>
  inferInstanceAs (Decidable (∃ d : Dart, vertexOf d = u ∧ vertexOf (flip d) = v))

instance deletedPrimalDecidableRel (e : Edge) :
    DecidableRel (edgeDeletedPrimalGraph rotation e).Adj := fun u v =>
  inferInstanceAs (Decidable (∃ d : Dart, edgeOf d ≠ e ∧ vertexOf d = u ∧ vertexOf (flip d) = v))

private theorem reachable_of_chain {W : Type*} (G : SimpleGraph W) (l : List W)
    (hc : l.IsChain G.Adj) {u v : W} (hu : u ∈ l) (hv : v ∈ l) : G.Reachable u v := by
  let : Trans G.Reachable G.Reachable G.Reachable := ⟨fun h k => h.trans k⟩
  have hr : l.IsChain G.Reachable := hc.imp fun _ _ h => h.reachable
  cases l with
  | nil => simp at hu
  | cons root rest =>
      have fromRoot (x : W) (hx : x ∈ root :: rest) : G.Reachable root x := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .refl _
        · exact hr.rel_cons hx
      exact (fromRoot u hu).symm.trans (fromRoot v hv)

private def rootPaths : Vertex → List Vertex :=
  ![[0], [0,1], [0,2], [0,3], [0,1,4], [0,1,5], [0,2,6], [0,2,7], [0,3,8], [0,3,9], [0,1,4,10], [0,1,5,11], [0,2,6,12], [0,2,7,13], [0,3,8,14], [0,3,9,15], [0,1,4,10,16], [0,1,4,10,17], [0,1,5,11,18], [0,2,6,12,19], [0,2,7,13,20], [0,3,8,14,21], [0,1,4,10,16,22], [0,1,4,10,17,23], [0,1,5,11,18,24], [0,2,6,12,19,25], [0,2,7,13,20,26], [0,3,8,14,21,27], [0,1,4,10,16,22,28], [0,1,5,11,18,24,29]]

private theorem rootPaths_certificate : ∀ v, (0 : Vertex) ∈ rootPaths v ∧
    v ∈ rootPaths v ∧ (rootPaths v).IsChain (rotationPrimalGraph rotation).Adj := by decide +kernel

theorem connected : (rotationPrimalGraph rotation).Connected := by
  apply ((rotationPrimalGraph rotation).connected_iff_exists_forall_reachable).mpr
  refine ⟨0, ?_⟩
  intro v
  obtain ⟨h0, hv, hc⟩ := rootPaths_certificate v
  exact reachable_of_chain _ _ hc h0 hv

private def alternatePaths : Edge → List Vertex :=
  ![[0,3,9,4,1], [0,1,5,6,2], [0,2,7,8,3], [1,0,3,9,4], [1,0,2,6,5], [2,0,1,5,6], [2,0,3,8,7], [3,0,2,7,8], [3,0,1,4,9], [4,1,0,3,9], [4,9,15,16,10], [5,1,0,2,6], [5,6,12,18,11], [6,5,11,18,12], [7,2,0,3,8], [7,8,14,20,13], [8,7,13,20,14], [9,4,10,16,15], [10,4,9,15,16], [10,16,22,23,17], [11,18,24,23,17], [11,5,6,12,18], [12,6,5,11,18], [12,6,2,7,13,19], [13,20,26,25,19], [13,7,8,14,20], [14,8,7,13,20], [14,20,26,27,21], [15,9,4,10,16], [15,9,3,8,14,21], [16,10,17,23,22], [17,10,16,22,23], [18,11,17,23,24], [19,13,20,26,25], [20,13,19,25,26], [21,14,20,26,27], [22,16,10,17,23], [22,23,24,29,28], [23,17,11,18,24], [24,23,22,28,29], [25,19,13,20,26], [25,26,27,28,29], [26,20,14,21,27], [27,26,25,29,28], [28,22,23,24,29]]

private theorem alternatePaths_certificate : ∀ d : Dart,
    vertexOf d ∈ alternatePaths (edgeOf d) ∧ vertexOf (flip d) ∈ alternatePaths (edgeOf d) ∧
      (alternatePaths (edgeOf d)).IsChain (edgeDeletedPrimalGraph rotation (edgeOf d)).Adj := by
  decide +kernel

theorem bridgeFree : EdgeBridgeFree rotation := by
  intro d
  obtain ⟨hu, hv, hc⟩ := alternatePaths_certificate d
  exact reachable_of_chain _ _ hc hu hv

/-- This is the same bridgeless spherical cubic class as in the source route. -/
theorem ambient : BridgelessSphericalCubicMapData rotation :=
  ⟨OrbitSphericalCubicMapData.ofSphericalCubicMapData rotation spherical,
    connected, cyclic, bridgeFree⟩

def faceRoot : Face → Dart := ![0,2,4,8,12,16,20,22,28,38,42,46,50,54,56,72,80]

def boundary : Face → Finset Edge :=
  ![{0,2,3,8,9}, {0,1,4,5,11}, {1,2,6,7,14}, {3,4,10,12,19,20}, {5,6,13,15,23,24}, {7,8,16,17,27,29}, {9,10,17,18,28}, {11,12,13,21,22}, {14,15,16,25,26}, {18,19,30,31,36}, {20,21,31,32,38}, {22,23,32,33,39,41}, {24,25,33,34,40}, {26,27,34,35,42}, {28,29,30,35,37,43}, {36,37,38,39,44}, {40,41,42,43,44}]

private def faceOf : Dart → Face :=
  ![0, 1, 1, 2, 2, 0, 0, 3, 3, 1, 1, 4, 4, 2, 2, 5, 5, 0, 0, 6, 6, 3, 7, 1, 3, 7, 7, 4, 8, 2, 4, 8, 8, 5, 5, 6, 6, 9, 9, 3, 3, 10, 10, 7, 7, 11, 11, 4, 4, 12, 12, 8, 8, 13, 13, 5, 14, 6, 5, 14, 14, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 15, 9, 14, 15, 15, 10, 15, 11, 16, 12, 11, 16, 16, 13, 16, 14, 16, 15]

private theorem faceOf_certificate : ∀ d : Dart,
    facePermutation.SameCycle d (faceRoot (faceOf d)) ∧
      ∀ f : Face, facePermutation.SameCycle d (faceRoot f) → f = faceOf d := by
  decide +kernel

/-- The seventeen indices enumerate every actual face cycle exactly once. -/
theorem face_partition_exact : ∀ d : Dart, ∃! f : Face, rotation.phi.SameCycle d (faceRoot f) := by
  rw [phi_eq]
  intro d
  exact ⟨faceOf d, (faceOf_certificate d).1, (faceOf_certificate d).2⟩

theorem boundary_eq (f : Face) : rotation.faceEdges (faceRoot f) = boundary f := by
  unfold RotationSystem.faceEdges RotationSystem.faceOrbit
  rw [phi_eq]
  revert f
  decide +kernel

def dual : SimpleGraph Face where
  Adj f g := f ≠ g ∧ (boundary f ∩ boundary g).Nonempty
  symm := ⟨by rintro f g ⟨hne, hm⟩; exact ⟨hne.symm, by rwa [Finset.inter_comm]⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance dualDecidableRel : DecidableRel dual.Adj := fun f g =>
  inferInstanceAs (Decidable (f ≠ g ∧ (boundary f ∩ boundary g).Nonempty))

def selected : Finset Face := Finset.univ \ {4,7,12}

def connectedRegion (S : Finset Face) : Prop := (dual.induce (S : Set Face)).Connected

instance regionConnectedDecidable (S : Finset Face) : Decidable (connectedRegion S) := by
  unfold connectedRegion
  infer_instance

theorem connected_sides : connectedRegion selected ∧ connectedRegion selectedᶜ := by decide +kernel

/-- The old incidence witness is exactly the union of the selected actual faces. -/
theorem retained_edges : selected.biUnion boundary = old := by decide +kernel

/-- Every actual facial cycle has five or six distinct boundary edges. -/
theorem face_lengths (f : Face) :
    (rotation.faceEdges (faceRoot f)).card = 5 ∨
      (rotation.faceEdges (faceRoot f)).card = 6 := by
  rw [boundary_eq]
  revert f
  decide +kernel

/-- The same bounds count actual darts of the facial cycles. -/
theorem face_dart_lengths (f : Face) :
    (rotation.faceOrbit (faceRoot f)).card = 5 ∨
      (rotation.faceOrbit (faceRoot f)).card = 6 := by
  unfold RotationSystem.faceOrbit
  rw [phi_eq]
  revert f
  decide +kernel

/-- The closure is a genuine matching of two edges on one hexagonal face. -/
theorem cofacial_matching_cap :
    Finset.univ \ old = ({13, 24} : Finset Edge) ∧
      Disjoint (rotation.endpoints 13) (rotation.endpoints 24) ∧
      (13 : Edge) ∈ rotation.faceEdges (faceRoot 4) ∧
      (24 : Edge) ∈ rotation.faceEdges (faceRoot 4) ∧
      (rotation.faceEdges (faceRoot 4)).card = 6 := by
  rw [endpoints_eq, endpoints_eq, boundary_eq]
  decide +kernel

/-- The obstruction applies to the literal endpoints of this checked sphere. -/
theorem no_two_switch_extension_on_rotation
    {C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3)}
    (p : KempeChainCertificate.History base C) (hlen : p.length ≤ 2) :
    ¬ ∃ d : Edge → Fin 3, GoertzelV24ForkInterfaceSupport.Proper rotation.endpoints Finset.univ d ∧
      ∀ x ∈ old, d x = C x := by
  rw [show rotation.endpoints = inc from funext endpoints_eq]
  exact no_repair_with_two_switches p hlen

/-- The same source rotation has a reconstructed colouring after three switches. -/
theorem three_switch_extension_on_rotation :
    ∃ C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3),
      (∃ p : KempeChainCertificate.History base C, p.length = 3) ∧
      ∃ d : Edge → Fin 3, GoertzelV24ForkInterfaceSupport.Proper rotation.endpoints Finset.univ d ∧
        ∀ x ∈ old, d x = C x := by
  rw [show rotation.endpoints = inc from funext endpoints_eq]
  exact repaired_history_extends

end Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitchGeometry
