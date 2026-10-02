import MettapediaFourColor.TwoFiveWheelConstruction
import MettapediaFourColor.WheelBoundaryLayouts
import MettapediaFourColor.LocalPreembedding
import MettapediaFourColor.ActualDualLocalGeometry

/-!
# One actual disk embedding argument for all two-five placements

Each exact twelve-port construction is read through the complete occurrence.
The same source-position and full-star laws preserve the dart map and arities;
vertex injectivity supplies a faithful kernel and injective repair disk.
The parameter is the position of the second five, retaining the original
centre, marked neighbour and complete boundary in every instance.
-/

namespace FourColor.TwoFiveWheelPreembedding

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open TwoFiveWheelConstruction Hypermap FaithfulKernelEmbedding

set_option maxRecDepth 32768

variable (p : Fin 6)

theorem source_edge : ∀ d : Fin 90,
    (TwoFiveWheelData.input p).graph.Adj ((vertex p) d) ((vertex p) ((table p).map.edge d)) := by
  revert p; decide +kernel

theorem source_plain : (table p).map.Plain := by constructor <;> revert p <;> decide +kernel

theorem endpoints_injective : Function.Injective (fun d : Fin 90 =>
    ((vertex p) d, (vertex p) ((table p).map.edge d))) := by revert p; decide +kernel

theorem same_face_iff (d e : Fin 90) :
    (table p).map.CFace d e ↔ (vertex p) d = (vertex p) e := by
  constructor
  · exact congr_of_sameCycle (faces p).vertex_face
  · intro eq
    apply ((faces p).same_face d).trans
    change (table p).map.CFace ((representative p) ((vertex p) d)) e
    rw [eq]
    exact ((faces p).same_face e).symm

theorem kernel_iff (d : Fin 90) :
    (table p).map.Kernel (ring p).reverse d ↔ 12 ≤ ((vertex p) d).val := by
  simp only [Hypermap.Kernel, Hypermap.Fband, (same_face_iff p)]
  revert p d
  decide +kernel

theorem source_position : ∀ (i : Fin 8) (d : Fin 90),
    (vertex p) d = i.natAdd 12 → ∃ q : Fin ((WheelBoundaryLayouts.degree p) i),
      (vertex p) ((table p).map.edge d) = (WheelBoundaryLayouts.fullSpoke p) i q ∧
      (vertex p) ((table p).map.face d) = i.natAdd 12 ∧
      (vertex p) ((table p).map.edge ((table p).map.face d)) =
        (WheelBoundaryLayouts.fullSpoke p) i ((WheelBoundaryCompletion.nextPos (WheelBoundaryLayouts.twoFive p)) i q) := by
  revert p; decide +kernel

set_option maxHeartbeats 24000000 in
-- Enumerate the eight complete source stars, independently of the ambient map.
theorem source_cycles : ∀ (i : Fin 8) (d : Fin 90), (vertex p) d = i.natAdd 12 →
    IsCyclicChain (fun u v => v = (table p).map.face u)
      (ConfigurationFaceGraph.faceCycle (table p).map d ((WheelBoundaryLayouts.degree p) i)) ∧
    (ConfigurationFaceGraph.faceCycle (table p).map d ((WheelBoundaryLayouts.degree p) i)).Nodup ∧
    ConfigurationFaceGraph.faceCycle (table p).map d ((WheelBoundaryLayouts.degree p) i) ≠ [] ∧
    (ConfigurationFaceGraph.faceCycle (table p).map d ((WheelBoundaryLayouts.degree p) i)).headD d = d := by
  unfold IsCyclicChain
  revert p; decide +kernel

theorem source_arity (i : Fin 8) (d : Fin 90) (hi : (vertex p) d = i.natAdd 12) :
    (table p).map.arity d = (WheelBoundaryLayouts.degree p) i := by
  obtain ⟨hc, hn, he, hh⟩ := (source_cycles p) i d hi
  have eq := ConfigurationFaceGraph.faceCycle_eq_orbit (M := (table p).map)
    d ((WheelBoundaryLayouts.degree p) i) hc hn he hh
  have len := congrArg List.length eq
  simpa [ConfigurationFaceGraph.faceCycle, length_orbitList, Hypermap.arity] using len.symm

theorem core_label {d : Fin 90} (hk : (table p).map.Kernel (ring p).reverse d) :
    ∃ i : Fin 8, (vertex p) d = i.natAdd 12 := by
  have bound := ((kernel_iff p) d).mp hk
  refine ⟨⟨((vertex p) d).val - 12, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

theorem numbered_ring : (cfring (config p)).map (realization p).numbering = (ring p).reverse := by
  change ((cfmap (config p)).cpring.reverse).map (realization p).numbering = _
  rw [List.map_reverse, (realization p).ring, TwoFiveWheelConstruction.cpring]

theorem numbered_kernel (d : (cfmap (config p)).Dart) :
    (table p).map.Kernel (ring p).reverse ((realization p).numbering d) ↔
      (cfmap (config p)).map.Kernel (cfring (config p)) d := by
  rw [← (numbered_ring p), ← (realization p).map_eq]
  exact kernel_relabel _ _ _ _

theorem numbered_edge (d : (cfmap (config p)).Dart) :
    (realization p).numbering ((cfmap (config p)).map.edge d) =
      (table p).map.edge ((realization p).numbering d) := by
  rw [← (realization p).map_eq, relabel_edge]

theorem numbered_face (d : (cfmap (config p)).Dart) :
    (realization p).numbering ((cfmap (config p)).map.face d) =
      (table p).map.face ((realization p).numbering d) := by
  rw [← (realization p).map_eq, relabel_face]

theorem numbered_arity (d : (cfmap (config p)).Dart) :
    (table p).map.arity ((realization p).numbering d) = (cfmap (config p)).map.arity d := by
  rw [← (realization p).map_eq, arity_relabel]

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  {rotation : Data G} (r : WheelBoundaryCompletion.Occurrence (WheelBoundaryLayouts.twoFive p) rotation)

def dart (d : Fin 90) : G.Dart :=
  ⟨(r.hom ((vertex p) d), r.hom ((vertex p) ((table p).map.edge d))), r.hom.map_adj ((source_edge p) d)⟩

theorem dart_edge (d : Fin 90) :
    (dart p) r ((table p).map.edge d) = (DualGraphQuery.map rotation).edge ((dart p) r d) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change r.hom ((vertex p) ((table p).map.edge ((table p).map.edge d))) = _
    rw [(source_plain p).edge_edge]
    rfl

theorem dart_face {d : Fin 90} (hk : (table p).map.Kernel (ring p).reverse d) :
    (dart p) r ((table p).map.face d) = (DualGraphQuery.map rotation).face ((dart p) r d) := by
  obtain ⟨i, hi⟩ := (core_label p) hk
  obtain ⟨q, hp, hf, hn⟩ := (source_position p) i d hi
  obtain ⟨a, b, step⟩ := r.turn i q
  have first : (dart p) r d =
      (⟨(r.hom (i.natAdd 12), r.hom ((WheelBoundaryLayouts.fullSpoke p) i q)), a⟩ : G.Dart) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg r.hom hi) (congrArg r.hom hp)
  have second : (dart p) r ((table p).map.face d) =
      (⟨(r.hom (i.natAdd 12),
        r.hom ((WheelBoundaryLayouts.fullSpoke p) i ((WheelBoundaryCompletion.nextPos (WheelBoundaryLayouts.twoFive p)) i q))), b⟩ : G.Dart) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg r.hom hf) (congrArg r.hom hn)
  change _ = rotation.vertexRotation _
  rw [first, second]
  exact step.symm

theorem dart_injective : Function.Injective ((dart p) r) := by
  intro d e eq
  apply (endpoints_injective p)
  exact Prod.ext (r.injective (congrArg (fun z : G.Dart => z.fst) eq))
    (r.injective (congrArg (fun z : G.Dart => z.snd) eq))

def reading (d : (cfmap (config p)).Dart) : G.Dart := (dart p) r ((realization p).numbering d)

theorem reading_edge (d : (cfmap (config p)).Dart) :
    (reading p) r ((cfmap (config p)).map.edge d) = (DualGraphQuery.map rotation).edge ((reading p) r d) := by
  unfold reading
  rw [(numbered_edge p), (dart_edge p)]

theorem reading_injective : Function.Injective ((reading p) r) :=
  ((dart_injective p) r).comp (realization p).numbering.injective

variable [Finite V] (cyclic : rotation.IsVertexwiseCyclic)

include cyclic in
theorem preembedding : Preembedding (cfmap (config p)).map (DualGraphQuery.map rotation)
    ((reading p) r) {z | (cfmap (config p)).map.Kernel (cfring (config p)) z} := by
  apply LocalPreembedding.of_radius2 (embeddable p).base.base.base.base.plain
    (fun _ => kernel_face) (embeddable p).kernel
  · exact (reading_edge p) r
  · intro d hd
    change (dart p) r ((realization p).numbering ((cfmap (config p)).map.face d)) = _
    rw [(numbered_face p)]
    exact (dart_face p) r (((numbered_kernel p) d).mpr hd)
  · intro d hd
    obtain ⟨i, hi⟩ := (core_label p) (((numbered_kernel p) d).mpr hd)
    rw [← (numbered_arity p), (source_arity p) i _ hi,
      DualGraphQuery.arity_eq_degree rotation cyclic]
    change G.degree (r.hom ((vertex p) ((realization p).numbering d))) = _
    rw [hi, r.degree_eq]
    rfl

omit [Finite V] in
theorem faithful : FaithfulKernel (cfmap (config p)).map (DualGraphQuery.map rotation)
    (cfring (config p)) ((reading p) r) := by
  refine ⟨fun _ _ _ _ eq => (reading_injective p) r eq, ?_⟩
  intro d e _ _ eq
  exact (reading_injective p) r (((reading_edge p) r d).trans eq)

include cyclic in
theorem disk_injective (tri : ExceptionalOverlap.Triangular rotation) :
    Function.Injective (embdd (cfmap (config p)).map (DualGraphQuery.map rotation)
      (cfring (config p)) ((reading p) r)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact FaithfulKernelEmbedding.disk_injective (embeddable p) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ tri) ((preembedding p) r cyclic) ((faithful p) r)

end FourColor.TwoFiveWheelPreembedding
