import MettapediaFourColor.StripPhaseObstruction
import MettapediaFourColor.GraphDiskEuler

/-! # The phase obstruction has a kernel-certified planar disk exterior -/

namespace FourColor.StripPhaseDisk

open SimpleGraph StripPhaseObstruction KempeBoundarySplit

set_option maxRecDepth 10000

def star : Fin 23 → List (Fin 23) :=
  ![[1,2,19,16,22,14,11,15,20,10],
    [0,2],
    [0,1,3,19],
    [2,4,22,16,19],
    [3,5,6,7,21,22],
    [4,6],
    [4,5,7],
    [4,6,8,18,17,12,13,21],
    [7,9,15,18],
    [8,10,20,15],
    [0,20,9],
    [0,14,13,15],
    [7,17,15,13],
    [7,12,15,11,14,22,21],
    [0,22,13,11],
    [0,11,13,12,17,18,8,9,20],
    [0,19,3,22],
    [7,18,15,12],
    [7,8,15,17],
    [0,2,3,16],
    [0,15,9,10],
    [4,7,13,22],
    [0,16,3,4,21,13,14]]

theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_adjacent : ∀ u v, v ∈ star u ↔ exterior.Adj u v := by decide +kernel
theorem row_nonempty : ∀ v, star v ≠ [] := by decide +kernel

def rows : GraphRotationRows.Rows exterior := ⟨star, row_nodup, row_adjacent⟩
def rotation := rows.rotation (⟨(0,1), by decide +kernel⟩ : exterior.Dart)

theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

def tour : List (Fin 23) := [0,1,2,3,4,5,6,7,8,9,10,20,15,11,13,12,17,18,17,12,13,14,22,16,19,16,22,21,22,14,13,11,15,20,10,9,8,7,6,5,4,3,2,1,0]

theorem tour_chain : tour.IsChain exterior.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 23, v ∈ tour := by decide +kernel

theorem connected : exterior.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 23) : exterior.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem covered : Function.Surjective (fun d : exterior.Dart => d.fst) := by
  intro v
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil (star v) (row_nonempty v)
  exact ⟨⟨(v,w), (row_adjacent v w).mp hw⟩,rfl⟩

theorem dart_count : Nat.card exterior.Dart = 110 := by
  rw [rows.dart_count]
  decide +kernel

theorem boundary_edges : ∀ i : Fin 11, exterior.Adj (ports i) (ports (i+1)) := by
  decide +kernel

def boundaryDart (i : Fin 11) : exterior.Dart := ⟨(ports i,ports (i+1)),boundary_edges i⟩
def ring : List exterior.Dart := List.ofFn boundaryDart
def ringPairs : List (Fin 23 × Fin 23) := List.ofFn (fun i => (ports i,ports (i+1)))

theorem mem_ring_iff (d : exterior.Dart) : d ∈ ring ↔ d.toProd ∈ ringPairs := by
  have eq : ring.map Dart.toProd = ringPairs := by simp [ring, ringPairs, boundaryDart]
  rw [← eq, List.mem_map]
  exact ⟨fun h => ⟨d,h,rfl⟩, fun ⟨a,ha,h⟩ => Dart.toProd_injective h ▸ ha⟩

def step (p : Fin 23 × Fin 23) : Fin 23 × Fin 23 := (p.2,rows.next p.2 p.1)

theorem face_check : ∀ u v, exterior.Adj u v → (u,v) ∉ ringPairs →
    step (step (step (u,v))) = (u,v) := by decide +kernel

theorem triangles : ∀ d : exterior.Dart, d ∉ ring → rotation.toRotationSystem.phi
    (rotation.toRotationSystem.phi (rotation.toRotationSystem.phi d)) = d := by
  intro d hd
  apply Dart.ext
  change step (step (step d.toProd)) = d.toProd
  exact face_check d.fst d.snd d.adj ((mem_ring_iff d).not.mp hd)

theorem boundary : IsCyclicChain (fun a b => b = rotation.toRotationSystem.phi a) ring := by
  change IsCyclicChain (fun a b : exterior.Dart => b = rotation.vertexRotation a.symm)
    (boundaryDart 0 :: [boundaryDart 1,boundaryDart 2,boundaryDart 3,boundaryDart 4,
      boundaryDart 5,boundaryDart 6,boundaryDart 7,boundaryDart 8,boundaryDart 9,boundaryDart 10])
  rw [isCyclicChain_cons]
  decide +kernel

theorem distinct : ring.Nodup := by decide +kernel
theorem ordered : ring.map (fun d => d.fst) = List.ofFn ports := by decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  GraphDiskEuler.planar rotation cyclic connected covered ring (by decide +kernel)
    boundary distinct triangles (by rw [Nat.card_fin, dart_count]; decide +kernel)

/-- This exact physical exterior supplies the abstract joint closure used
by the source-repair calculus; no closure hypothesis is assumed. -/
theorem closed : KempeClosed (GraphTrace exterior (List.ofFn ports)) := by
  have h := PlanarGraphBoundaryClosure.rotation_closed rotation cyclic planar
    ring boundary distinct triangles
  rwa [ordered] at h

end FourColor.StripPhaseDisk
