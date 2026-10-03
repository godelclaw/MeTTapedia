import MettapediaFourColor.ResidualExteriorDiskRows
import MettapediaFourColor.GraphDiskEuler

/-! # The retained exterior is an exact planar triangulated disk -/

namespace FourColor.ResidualExteriorDisk

open SimpleGraph KempeDetachExample KempeBoundarySplit

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def port (i : Fin 11) : Fin 155 := ports.get i

theorem boundary_edges : ∀ i : Fin 11, graph.Adj (port i) (port (i + 1)) := by
  decide +kernel

def boundaryDart (i : Fin 11) : graph.Dart :=
  ⟨(port i, port (i + 1)), boundary_edges i⟩

def ring : List graph.Dart := List.ofFn boundaryDart
def ringPairs : List (Fin 155 × Fin 155) := List.ofFn (fun i => (port i, port (i + 1)))

theorem mem_ring_iff (d : graph.Dart) : d ∈ ring ↔ d.toProd ∈ ringPairs := by
  have eq : ring.map Dart.toProd = ringPairs := by simp [ring, ringPairs, boundaryDart]
  rw [← eq, List.mem_map]
  exact ⟨fun h => ⟨d, h, rfl⟩, fun ⟨a, ha, h⟩ => Dart.toProd_injective h ▸ ha⟩

def step (p : Fin 155 × Fin 155) : Fin 155 × Fin 155 :=
  (p.2, rows.next p.2 p.1)

def Triangular (u v : Fin 155) : Prop :=
  (u,v) ∉ ringPairs → step (step (step (u,v))) = (u,v)

instance (u v) : Decidable (Triangular u v) := inferInstanceAs (Decidable (_ → _))

theorem face_check : edges.all (fun e => decide
    (Triangular e.1 e.2 ∧ Triangular e.2 e.1)) = true := by decide +kernel

theorem triangles : ∀ d : graph.Dart, d ∉ ring → rotation.toRotationSystem.phi
    (rotation.toRotationSystem.phi (rotation.toRotationSystem.phi d)) = d := by
  intro d hd
  apply Dart.ext
  change step (step (step d.toProd)) = d.toProd
  exact on_edges Triangular
    (fun e he => of_decide_eq_true (List.all_eq_true.mp face_check e he))
    d.fst d.snd d.adj ((mem_ring_iff d).not.mp hd)

theorem boundary : IsCyclicChain (fun a b => b = rotation.toRotationSystem.phi a) ring := by
  change IsCyclicChain (fun a b : graph.Dart => b = rotation.vertexRotation a.symm)
    (boundaryDart 0 :: [boundaryDart 1, boundaryDart 2,
    boundaryDart 3, boundaryDart 4, boundaryDart 5, boundaryDart 6,
    boundaryDart 7, boundaryDart 8, boundaryDart 9, boundaryDart 10])
  rw [isCyclicChain_cons]
  decide +kernel

theorem distinct : ring.Nodup := by decide +kernel
theorem ordered : ring.map (fun d => d.fst) = ports := by decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  GraphDiskEuler.planar rotation cyclic connected covered ring (by decide +kernel)
    boundary distinct triangles (by
      rw [Nat.card_fin, dart_count]
      decide +kernel)

/-- The actual exterior graph supplies the complete joint closure relation.
There is no planar-geometry or closure hypothesis left in this instance. -/
theorem closed : KempeClosed (GraphTrace graph ports) := by
  have h := PlanarGraphBoundaryClosure.rotation_closed rotation cyclic planar
    ring boundary distinct triangles
  rwa [ordered] at h

end FourColor.ResidualExteriorDisk
