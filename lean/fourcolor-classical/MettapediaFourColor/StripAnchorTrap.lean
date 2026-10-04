import MettapediaFourColor.StripAnchoredExtension
import MettapediaFourColor.GraphDiskEuler
import Mettapedia.GraphTheory.Kempe.PhaseBoundary
import Mettapedia.GraphTheory.Kempe.SeparatedChains

/-!
# A physical trap for preserving joint one-hole choices

A twelve-vertex planar disk exterior admits four joint anchor choices with
one omitted core vertex, but no complete D0099 colouring. Every fixed-pair
phase either merely permutes the palette, or remains blocked with fewer
one-hole choices. Two switches using different pairs nevertheless extend.
The low-degree exterior is not asserted to satisfy minimal-counterexample
hypotheses. D0099 attribution is inherited from the source modules.
-/

namespace FourColor.StripAnchorTrap

open Color SimpleGraph StripResponseSummary StripAnchoredExtension
open KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 10000

def star : Fin 12 → List (Fin 12) :=
  ![[1,10],
    [0,2,11,10],
    [1,3,11],
    [2,4,11],
    [3,5,6,7,10,11],
    [4,6],
    [4,5,7],
    [4,6,8,10],
    [7,9,10],
    [8,10],
    [0,1,11,4,7,8,9],
    [1,2,3,4,10]]

theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel
theorem row_nonempty : ∀ v, star v ≠ [] := by decide +kernel

def exterior : SimpleGraph (Fin 12) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def rows : GraphRotationRows.Rows exterior := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,1),by decide +kernel⟩ : exterior.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

def tour : List (Fin 12) := [0,1,2,3,4,5,6,7,8,9,10,11,1,0]
theorem tour_nonempty : tour ≠ [] := by decide +kernel
theorem tour_chain : tour.IsChain exterior.Adj := by decide +kernel
theorem tour_covers : ∀ v, v ∈ tour := by decide +kernel

theorem connected : exterior.Connected := by
  let p := Walk.ofSupport tour tour_nonempty tour_chain
  have reach (v : Fin 12) : exterior.Reachable (tour.head tour_nonempty) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem covered : Function.Surjective (fun d : exterior.Dart => d.fst) := by
  intro v
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil (star v) (row_nonempty v)
  exact ⟨⟨(v,w),hw⟩,rfl⟩

def port (i : Fin 11) : Fin 12 := i.castLE (by decide)
theorem boundary_edges : ∀ i, exterior.Adj (port i) (port (i+1)) := by decide +kernel
def boundaryDart (i : Fin 11) : exterior.Dart := ⟨(port i,port (i+1)),boundary_edges i⟩
def ring := List.ofFn boundaryDart
def ringPairs := List.ofFn (fun i => (port i,port (i+1)))

theorem mem_ring_iff (d : exterior.Dart) : d ∈ ring ↔ d.toProd ∈ ringPairs := by
  have eq : ring.map Dart.toProd = ringPairs := by
    simp [ring,ringPairs,boundaryDart]
  rw [← eq,List.mem_map]
  exact ⟨fun h => ⟨d,h,rfl⟩,fun ⟨a,ha,h⟩ => Dart.toProd_injective h ▸ ha⟩

def faceStep (p : Fin 12 × Fin 12) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u v, exterior.Adj u v → (u,v) ∉ ringPairs →
    faceStep (faceStep (faceStep (u,v))) = (u,v) := by decide +kernel

theorem triangles : ∀ d : exterior.Dart, d ∉ ring →
    rotation.toRotationSystem.phi (rotation.toRotationSystem.phi
      (rotation.toRotationSystem.phi d)) = d := by
  intro d hd
  apply Dart.ext
  exact face_check d.fst d.snd d.adj ((mem_ring_iff d).not.mp hd)

theorem boundary : IsCyclicChain
    (fun a b => b = rotation.toRotationSystem.phi a) ring := by
  change IsCyclicChain (fun a b : exterior.Dart => b = rotation.vertexRotation a.symm)
    (boundaryDart 0 :: [boundaryDart 1,boundaryDart 2,boundaryDart 3,boundaryDart 4,
      boundaryDart 5,boundaryDart 6,boundaryDart 7,boundaryDart 8,boundaryDart 9,boundaryDart 10])
  rw [isCyclicChain_cons]
  decide +kernel

theorem distinct : ring.Nodup := by decide +kernel
theorem dart_count : Nat.card exterior.Dart = 44 := by rw [rows.dart_count]; decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  GraphDiskEuler.planar rotation cyclic connected covered ring (by decide +kernel)
    boundary distinct triangles (by rw [Nat.card_fin,dart_count]; decide +kernel)

def values : Fin 3 → Fin 12 → Color
  | 0 => ![c0,c1,c3,c2,c1,c3,c2,c3,c0,c3,c2,c0]
  | 1 => ![c1,c0,c3,c2,c0,c3,c2,c3,c0,c3,c2,c1]
  | 2 => ![c1,c0,c3,c2,c0,c3,c2,c1,c0,c3,c2,c1]

theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel

def state (s : Fin 3) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
def read (c : Fin 12 → Color) : Boundary := fun i => c (port i)

theorem base_profile : ¬ Full (read (values 0)) ∧ (choices (read (values 0))).card = 4 := by
  decide +kernel

def pair : Fin 6 → Color × Color := ![(c0,c1),(c0,c2),(c0,c3),(c1,c2),(c1,c3),(c2,c3)]
def roots : Fin 6 → Fin 4 → Fin 12
  | 0 => ![0,8,0,0]
  | 1 => ![0,6,0,0]
  | 2 => ![0,2,5,7]
  | 3 => ![1,1,1,1]
  | 4 => ![1,4,9,1]
  | 5 => ![2,5,2,2]

def label : Fin 6 → Fin 12 → Fin 4
  | 0 => ![0,0,0,0,0,0,0,0,1,0,0,0]
  | 1 => ![0,0,0,0,0,0,1,0,0,0,0,0]
  | 2 => ![0,0,1,0,0,2,0,3,3,3,0,1]
  | 3 => ![0,0,0,0,0,0,0,0,0,0,0,0]
  | 4 => ![0,0,0,0,1,1,0,1,0,2,0,0]
  | 5 => ![0,0,0,0,0,1,1,1,0,1,1,0]

def routeList : Fin 6 → Fin 12 → List (Fin 12)
  | 0 => ![[0],[0,1],[2],[3],[0,1,11,4],[5],[6],[7],[8],[9],[10],[0,1,11]]
  | 1 => ![[0],[1],[2],[0,10,11,3],[4],[5],[6],[7],[0,10,8],[9],[0,10],[0,10,11]]
  | 2 => ![[0],[1],[2],[3],[4],[5],[6],[7],[7,8],[7,8,9],[10],[2,11]]
  | 3 => ![[0],[1],[2],[1,10,4,3],[1,10,4],[5],[1,10,4,6],[7],[8],[9],[1,10],[11]]
  | 4 => ![[0],[1],[1,2],[3],[4],[4,5],[6],[4,7],[8],[9],[10],[11]]
  | 5 => ![[0],[1],[2],[2,3],[4],[5],[5,6],[5,6,7],[8],[5,6,7,10,9],[5,6,7,10],[11]]

def Active (s : Fin 6) (v : Fin 12) : Prop :=
  state 0 v = (pair s).1 ∨ state 0 v = (pair s).2
instance (s v) : Decidable (Active s v) := inferInstanceAs (Decidable (_ ∨ _))

theorem route_nonempty : ∀ s j, routeList s j ≠ [] := by decide +kernel
theorem route_chain : ∀ s j, (routeList s j).IsChain exterior.Adj := by decide +kernel
theorem route_head : ∀ s j, Active s j →
    (routeList s j).head (route_nonempty s j) = roots s (label s j) := by decide +kernel
theorem route_last : ∀ s j,
    (routeList s j).getLast (route_nonempty s j) = j := by decide +kernel
theorem route_active : ∀ s j, Active s j → ∀ x ∈ routeList s j, Active s x := by decide +kernel

theorem routes (s : Fin 6) (j : Fin 12) (h : Active s j) :
    ∃ p : exterior.Walk (roots s (label s j)) j, ∀ x ∈ p.support, Active s x := by
  let p := (Walk.ofSupport (routeList s j) (route_nonempty s j) (route_chain s j)).copy
    (route_head s j h) (route_last s j)
  refine ⟨p, ?_⟩
  intro x hx
  exact route_active s j h x (by simpa [p] using hx)

def answer (s : Fin 6) (bits : Fin 4 → Bool) (v : Fin 12) : Color :=
  if bits (label s v) then Equiv.swap (pair s).1 (pair s).2 (values 0 v) else values 0 v

def Orbit (c : Fin 12 → Color) : Prop := ∃ g : Equiv.Perm Color, ∀ v, c v = g (values 0 v)
instance (c) : Decidable (Orbit c) := by unfold Orbit; infer_instance

theorem answer_barrier : ∀ s bits,
    Orbit (answer s bits) ∨ (¬ Full (read (answer s bits)) ∧
      (choices (read (answer s bits))).card < 4) := by decide +kernel

end FourColor.StripAnchorTrap
