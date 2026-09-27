import Mettapedia.GraphTheory.FourColor.LockedKempeOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Spherical geometry of the locked Kempe patch

The eighteen edges in the orbit obstruction carry a concrete cubic sphere
rotation. Its eight actual facial cycles are indexed explicitly. Both sides
of the old and enlarged face regions are connected, and adding face 5 adds
exactly edge {3,9} to the retained incidence graph.
-/

namespace Mettapedia.GraphTheory.FourColor.LockedKempeOrbitGeometry

open LockedKempeOrbit GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge
open GoertzelV24CurvatureScope GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24TwoEdgeCutMinimality

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Dart := Fin 36
abbrev Face := Fin 8

def vertexOf : Dart → Vertex :=
  ![0,4,0,7,0,8,1,3,1,6,1,7,2,3,2,5,2,7,3,9,4,6,4,10,5,9,5,11,6,10,8,10,8,11,9,11]

def edgeOf (d : Dart) : Edge := ⟨d.val / 2, by have := d.isLt; omega⟩

def flip : Equiv.Perm Dart where
  toFun := ![1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14,17,16,19,18,21,20,23,22,25,24,27,26,29,28,31,30,33,32,35,34]
  invFun := ![1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14,17,16,19,18,21,20,23,22,25,24,27,26,29,28,31,30,33,32,35,34]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def facePermutation : Equiv.Perm Dart where
  toFun := ![20,4,17,0,30,2,13,8,28,10,3,6,18,16,26,12,11,14,25,7,9,22,29,1,34,15,33,24,31,21,23,32,35,5,27,19]
  invFun := ![3,23,5,10,1,33,11,19,7,20,9,16,15,6,17,25,13,2,12,35,0,29,21,30,27,18,14,34,8,22,4,28,31,26,24,32]
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
  outer := 8
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
  change (12 : Int) - 18 + rotation.phi.partition.parts.card = 2
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
  ![[0], [0,7,1], [0,7,2], [0,7,1,3], [0,4], [0,7,2,5],
    [0,4,6], [0,7], [0,8], [0,8,11,9], [0,4,10], [0,8,11]]

private theorem rootPaths_certificate : ∀ v, (0 : Vertex) ∈ rootPaths v ∧
    v ∈ rootPaths v ∧ (rootPaths v).IsChain (rotationPrimalGraph rotation).Adj := by decide +kernel

theorem connected : (rotationPrimalGraph rotation).Connected := by
  apply ((rotationPrimalGraph rotation).connected_iff_exists_forall_reachable).mpr
  refine ⟨0, ?_⟩
  intro v
  obtain ⟨h0, hv, hc⟩ := rootPaths_certificate v
  exact reachable_of_chain _ _ hc h0 hv

private def alternatePaths : Edge → List Vertex :=
  ![[0,8,10,4], [0,4,6,1,7], [0,4,10,8], [1,7,2,3], [1,7,0,4,6], [1,3,2,7],
    [2,5,9,3], [2,3,9,5], [2,3,1,7], [3,2,5,9], [4,10,6], [4,6,10],
    [5,11,9], [5,9,11], [6,4,10], [8,0,4,10], [8,0,7,2,5,11], [9,5,11]]

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

def faceRoot : Face → Dart := ![0,4,2,6,8,12,22,24]

def boundary : Face → Finset Edge :=
  ![{0,1,4,5,10}, {0,2,11,15}, {1,2,7,8,13,16}, {3,5,6,8},
    {3,4,9,14,15,16,17}, {6,7,9,12}, {10,11,14}, {12,13,17}]

private def faceOf : Dart → Face :=
  ![0,1,2,0,1,2,3,4,4,0,0,3,5,3,2,5,3,2,5,4,0,6,6,1,7,5,2,7,4,6,1,4,4,2,7,4]

private theorem faceOf_certificate : ∀ d : Dart,
    facePermutation.SameCycle d (faceRoot (faceOf d)) ∧
      ∀ f : Face, facePermutation.SameCycle d (faceRoot f) → f = faceOf d := by
  decide +kernel

/-- The eight indices enumerate every actual face cycle exactly once. -/
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

def selected : Finset Face := {0,1,2,3,7}
def selectedNext : Finset Face := insert 5 selected

def connectedRegion (S : Finset Face) : Prop := (dual.induce (S : Set Face)).Connected

instance regionConnectedDecidable (S : Finset Face) : Decidable (connectedRegion S) := by
  unfold connectedRegion
  infer_instance

theorem connected_sides : connectedRegion selected ∧ connectedRegion selectedᶜ ∧
    connectedRegion selectedNext ∧ connectedRegion selectedNextᶜ := by decide +kernel

theorem retained_edges : selected.biUnion boundary = old ∧
    selectedNext.biUnion boundary = enlarged ∧ enlarged \ old = {9} := by decide +kernel

theorem added_face_new : (5 : Face) ∉ selected := by decide +kernel

/-- The obstruction holds on the actual endpoints of the checked sphere
rotation, for every strict future edge set and every finite physical history. -/
theorem no_history_strict_extension_on_rotation
    {C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3)}
    (p : KempeChainCertificate.History base C) {S : Finset Edge} (hS : old ⊂ S) :
    ¬ ∃ d : Edge → Fin 3, GoertzelV24ForkInterfaceSupport.Proper rotation.endpoints S d ∧
      ∀ x ∈ old, d x = C x := by
  rw [show rotation.endpoints = inc from funext endpoints_eq]
  exact no_history_strict_extension p hS

theorem global_source_proper :
    GoertzelV24ForkInterfaceSupport.Proper rotation.endpoints Finset.univ globalAssignment := by
  rw [show rotation.endpoints = inc from funext endpoints_eq]
  exact global_proper

end Mettapedia.GraphTheory.FourColor.LockedKempeOrbitGeometry
