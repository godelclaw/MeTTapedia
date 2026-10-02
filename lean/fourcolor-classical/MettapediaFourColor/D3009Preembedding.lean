import MettapediaFourColor.D3009Construction
import MettapediaFourColor.D3009Boundary
import MettapediaFourColor.LocalPreembedding
import MettapediaFourColor.ActualDualLocalGeometry

/-!
# The recognised wheel as an injective disk

The actual twenty-one-vertex occurrence determines every source dart by its
ordered endpoints. Its complete core rotations give a preembedding of the
same Y/H construction used by the colouring semantics. Vertex injectivity
preserves dart identity and edge reflection, hence the disk used for repair.
No colouring certificate or ambient Four Colour theorem is used here.
-/

namespace FourColor.D3009Preembedding

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open D3009Construction Hypermap FaithfulKernelEmbedding

set_option maxRecDepth 32768

theorem source_edge : ∀ d : Fin 94,
    D3009Wheel.input.graph.Adj (vertex d) (vertex (table.map.edge d)) := by
  decide +kernel

theorem source_plain : table.map.Plain := by constructor <;> decide +kernel

theorem endpoints_injective : Function.Injective (fun d : Fin 94 =>
    (vertex d, vertex (table.map.edge d))) := by decide +kernel

theorem same_face_iff (d e : Fin 94) :
    table.map.CFace d e ↔ vertex d = vertex e := by
  constructor
  · exact congr_of_sameCycle faces.vertex_face
  · intro eq
    apply (faces.same_face d).trans
    change table.map.CFace (representative (vertex d)) e
    rw [eq]
    exact (faces.same_face e).symm

theorem kernel_iff (d : Fin 94) :
    table.map.Kernel ring.reverse d ↔ 13 ≤ (vertex d).val := by
  simp only [Hypermap.Kernel, Hypermap.Fband, same_face_iff]
  revert d
  decide +kernel

theorem source_position : ∀ (i : Fin 8) (d : Fin 94),
    vertex d = i.natAdd 13 → ∃ p : Fin (D3009Wheel.degree i),
      vertex (table.map.edge d) = D3009Boundary.fullSpoke i p ∧
      vertex (table.map.face d) = i.natAdd 13 ∧
      vertex (table.map.edge (table.map.face d)) =
        D3009Boundary.fullSpoke i (D3009Boundary.nextPos i p) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Enumerate the eight complete source stars, independently of the ambient map.
theorem source_cycles : ∀ (i : Fin 8) (d : Fin 94), vertex d = i.natAdd 13 →
    IsCyclicChain (fun u v => v = table.map.face u)
      (ConfigurationFaceGraph.faceCycle table.map d (D3009Wheel.degree i)) ∧
    (ConfigurationFaceGraph.faceCycle table.map d (D3009Wheel.degree i)).Nodup ∧
    ConfigurationFaceGraph.faceCycle table.map d (D3009Wheel.degree i) ≠ [] ∧
    (ConfigurationFaceGraph.faceCycle table.map d (D3009Wheel.degree i)).headD d = d := by
  unfold IsCyclicChain
  decide +kernel

theorem source_arity (i : Fin 8) (d : Fin 94) (hi : vertex d = i.natAdd 13) :
    table.map.arity d = D3009Wheel.degree i := by
  obtain ⟨hc, hn, he, hh⟩ := source_cycles i d hi
  have eq := ConfigurationFaceGraph.faceCycle_eq_orbit (M := table.map)
    d (D3009Wheel.degree i) hc hn he hh
  have len := congrArg List.length eq
  simpa [ConfigurationFaceGraph.faceCycle, length_orbitList, Hypermap.arity] using len.symm

theorem core_label {d : Fin 94} (hk : table.map.Kernel ring.reverse d) :
    ∃ i : Fin 8, vertex d = i.natAdd 13 := by
  have bound := (kernel_iff d).mp hk
  refine ⟨⟨(vertex d).val - 13, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

theorem numbered_ring : (cfring config).map realization.numbering = ring.reverse := by
  change ((cfmap config).cpring.reverse).map realization.numbering = _
  rw [List.map_reverse, realization.ring, D3009Construction.cpring]

theorem numbered_kernel (d : (cfmap config).Dart) :
    table.map.Kernel ring.reverse (realization.numbering d) ↔
      (cfmap config).map.Kernel (cfring config) d := by
  rw [← numbered_ring, ← realization.map_eq]
  exact kernel_relabel _ _ _ _

theorem numbered_edge (d : (cfmap config).Dart) :
    realization.numbering ((cfmap config).map.edge d) =
      table.map.edge (realization.numbering d) := by
  rw [← realization.map_eq, relabel_edge]

theorem numbered_face (d : (cfmap config).Dart) :
    realization.numbering ((cfmap config).map.face d) =
      table.map.face (realization.numbering d) := by
  rw [← realization.map_eq, relabel_face]

theorem numbered_arity (d : (cfmap config).Dart) :
    table.map.arity (realization.numbering d) = (cfmap config).map.arity d := by
  rw [← realization.map_eq, arity_relabel]

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  {rotation : Data G} (r : D3009Boundary.Occurrence rotation)

def dart (d : Fin 94) : G.Dart :=
  ⟨(r.hom (vertex d), r.hom (vertex (table.map.edge d))), r.hom.map_adj (source_edge d)⟩

theorem dart_edge (d : Fin 94) :
    dart r (table.map.edge d) = (DualGraphQuery.map rotation).edge (dart r d) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change r.hom (vertex (table.map.edge (table.map.edge d))) = _
    rw [source_plain.edge_edge]
    rfl

theorem dart_face {d : Fin 94} (hk : table.map.Kernel ring.reverse d) :
    dart r (table.map.face d) = (DualGraphQuery.map rotation).face (dart r d) := by
  obtain ⟨i, hi⟩ := core_label hk
  obtain ⟨p, hp, hf, hn⟩ := source_position i d hi
  obtain ⟨a, b, step⟩ := r.turn i p
  have first : dart r d =
      (⟨(r.hom (i.natAdd 13), r.hom (D3009Boundary.fullSpoke i p)), a⟩ : G.Dart) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg r.hom hi) (congrArg r.hom hp)
  have second : dart r (table.map.face d) =
      (⟨(r.hom (i.natAdd 13),
        r.hom (D3009Boundary.fullSpoke i (D3009Boundary.nextPos i p))), b⟩ : G.Dart) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg r.hom hf) (congrArg r.hom hn)
  change _ = rotation.vertexRotation _
  rw [first, second]
  exact step.symm

theorem dart_injective : Function.Injective (dart r) := by
  intro d e eq
  apply endpoints_injective
  exact Prod.ext (r.injective (congrArg (fun z : G.Dart => z.fst) eq))
    (r.injective (congrArg (fun z : G.Dart => z.snd) eq))

def reading (d : (cfmap config).Dart) : G.Dart := dart r (realization.numbering d)

theorem reading_edge (d : (cfmap config).Dart) :
    reading r ((cfmap config).map.edge d) = (DualGraphQuery.map rotation).edge (reading r d) := by
  unfold reading
  rw [numbered_edge, dart_edge]

theorem reading_injective : Function.Injective (reading r) :=
  (dart_injective r).comp realization.numbering.injective

variable [Finite V] (cyclic : rotation.IsVertexwiseCyclic)

include cyclic in
theorem preembedding : Preembedding (cfmap config).map (DualGraphQuery.map rotation)
    (reading r) {z | (cfmap config).map.Kernel (cfring config) z} := by
  apply LocalPreembedding.of_radius2 embeddable.base.base.base.base.plain
    (fun _ => kernel_face) embeddable.kernel
  · exact reading_edge r
  · intro d hd
    change dart r (realization.numbering ((cfmap config).map.face d)) = _
    rw [numbered_face]
    exact dart_face r ((numbered_kernel d).mpr hd)
  · intro d hd
    obtain ⟨i, hi⟩ := core_label ((numbered_kernel d).mpr hd)
    rw [← numbered_arity, source_arity i _ hi,
      DualGraphQuery.arity_eq_degree rotation cyclic]
    change G.degree (r.hom (vertex (realization.numbering d))) = _
    rw [hi, r.degree_eq]

omit [Finite V] in
theorem faithful : FaithfulKernel (cfmap config).map (DualGraphQuery.map rotation)
    (cfring config) (reading r) := by
  refine ⟨fun _ _ _ _ eq => reading_injective r eq, ?_⟩
  intro d e _ _ eq
  exact reading_injective r ((reading_edge r d).trans eq)

include cyclic in
theorem disk_injective (tri : ExceptionalOverlap.Triangular rotation) :
    Function.Injective (embdd (cfmap config).map (DualGraphQuery.map rotation)
      (cfring config) (reading r)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact FaithfulKernelEmbedding.disk_injective embeddable (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ tri) (preembedding r cyclic) (faithful r)

end FourColor.D3009Preembedding
