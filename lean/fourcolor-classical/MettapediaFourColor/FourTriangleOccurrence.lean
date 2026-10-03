import MettapediaFourColor.FourTriangleConstruction
import MettapediaFourColor.LocalPreembedding
import MettapediaFourColor.ActualDualLocalGeometry

/-!
# Actual occurrences of both four-triangle patches

The same proof transports either complete source presentation into an ambient
rotation system. Complete core stars retain the specified orientation and
all degrees. Core vertices are distinct and cannot capture boundary labels;
distinct boundary labels may coincide. This suffices for a faithful kernel
and injective reconstruction disk.

Completion of these hypotheses from the four internal triangles alone is a
separate geometric obligation.
-/

namespace FourColor.FourTriangleOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FourTriangleConstruction Hypermap
open FaithfulKernelEmbedding

set_option maxRecDepth 32768

variable (p : Fin 2)

theorem source_edge : ∀ d : Fin 70,
    (FourTriangleCore.input p).graph.Adj ((vertex p) d)
      ((vertex p) ((table p).map.edge d)) := by revert p; decide +kernel

theorem source_plain : (table p).map.Plain := by constructor <;> revert p <;> decide +kernel

theorem same_face_iff (d e : Fin 70) :
    (table p).map.CFace d e ↔ (vertex p) d = (vertex p) e := by
  constructor
  · exact congr_of_sameCycle (faces p).vertex_face
  · intro eq
    apply ((faces p).same_face d).trans
    change (table p).map.CFace ((representative p) ((vertex p) d)) e
    rw [eq]
    exact ((faces p).same_face e).symm

theorem kernel_iff (d : Fin 70) :
    (table p).map.Kernel (ring p).reverse d ↔ 10 ≤ ((vertex p) d).val := by
  simp only [Hypermap.Kernel, Hypermap.Fband, (same_face_iff p)]
  revert p d
  decide +kernel

theorem source_cycles : ∀ d : Fin 70,
    IsCyclicChain (fun u v => v = (table p).map.face u)
      (ConfigurationFaceGraph.faceCycle (table p).map d ((degree p) ((vertex p) d))) ∧
    (ConfigurationFaceGraph.faceCycle (table p).map d ((degree p) ((vertex p) d))).Nodup ∧
    (ConfigurationFaceGraph.faceCycle (table p).map d ((degree p) ((vertex p) d))) ≠ [] ∧
    (ConfigurationFaceGraph.faceCycle (table p).map d ((degree p) ((vertex p) d))).headD d = d := by
  unfold IsCyclicChain
  revert p
  decide +kernel

theorem source_arity (d : Fin 70) : (table p).map.arity d = (degree p) ((vertex p) d) := by
  obtain ⟨hc, hn, he, hh⟩ := (source_cycles p) d
  have eq := ConfigurationFaceGraph.faceCycle_eq_orbit (M := (table p).map)
    d ((degree p) ((vertex p) d)) hc hn he hh
  have len := congrArg List.length eq
  simpa [ConfigurationFaceGraph.faceCycle, length_orbitList, Hypermap.arity] using len.symm

theorem numbered_ring : (cfring (config p)).map (realization p).numbering = (ring p).reverse := by
  change ((cfmap (config p)).cpring.reverse).map (realization p).numbering = _
  rw [List.map_reverse, (realization p).ring, FourTriangleConstruction.cpring]

theorem numbered_kernel (d : (cfmap (config p)).Dart) :
    (table p).map.Kernel (ring p).reverse ((realization p).numbering d) ↔
      (cfmap (config p)).map.Kernel (cfring (config p)) d := by
  rw [← (numbered_ring p), ← (realization p).map_eq]
  exact kernel_relabel _ _ _ _

theorem numbered_edge (d : (cfmap (config p)).Dart) :
    (realization p).numbering ((cfmap (config p)).map.edge d) =
      (table p).map.edge ((realization p).numbering d) := by
  rw [← (realization p).map_eq, Hypermap.relabel_edge]

theorem numbered_face (d : (cfmap (config p)).Dart) :
    (realization p).numbering ((cfmap (config p)).map.face d) =
      (table p).map.face ((realization p).numbering d) := by
  rw [← (realization p).map_eq, Hypermap.relabel_face]

theorem numbered_arity (d : (cfmap (config p)).Dart) :
    (table p).map.arity ((realization p).numbering d) = (cfmap (config p)).map.arity d := by
  rw [← (realization p).map_eq, arity_relabel]

variable {V : Type*} {G : SimpleGraph V}

def dart (f : (FourTriangleCore.input p).graph →g G) (d : Fin 70) : G.Dart :=
  ⟨(f ((vertex p) d), f ((vertex p) ((table p).map.edge d))), f.map_adj ((source_edge p) d)⟩

theorem dart_edge (f : (FourTriangleCore.input p).graph →g G) (d : Fin 70) :
    (dart p) f ((table p).map.edge d) = ((dart p) f d).symm := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change f ((vertex p) ((table p).map.edge ((table p).map.edge d))) = _
    rw [(source_plain p).edge_edge]
    rfl

variable [G.LocallyFinite]

/-- A geometric reading of all source edges, complete core rotations and
degrees. Boundary labels may identify with each other, but not with the core. -/
structure Occurrence (rotation : Data G) where
  hom : (FourTriangleCore.input p).graph →g G
  turn : ∀ d : Fin 70, 10 ≤ ((vertex p) d).val →
    rotation.vertexRotation ((dart p) hom d) = (dart p) hom ((table p).map.face d)
  degree_eq : ∀ v : Fin 16, 10 ≤ v.val → G.degree (hom v) = (degree p) v
  core_injective : Set.InjOn hom {v | 10 ≤ v.val}
  outside : ∀ p v : Fin 16, p.val < 10 → 10 ≤ v.val → hom p ≠ hom v

variable [Finite V] {rotation : Data G} (r : Occurrence p rotation)
  (cyclic : rotation.IsVertexwiseCyclic)

def reading (d : (cfmap (config p)).Dart) : G.Dart := (dart p) r.hom ((realization p).numbering d)

omit [Finite V] in
theorem reading_edge (d : (cfmap (config p)).Dart) :
    (reading p) r ((cfmap (config p)).map.edge d) =
      (DualGraphQuery.map rotation).edge ((reading p) r d) := by
  unfold reading
  rw [(numbered_edge p), (dart_edge p)]
  rfl

include cyclic

theorem preembedding : Preembedding (cfmap (config p)).map (DualGraphQuery.map rotation)
    ((reading p) r) {z | (cfmap (config p)).map.Kernel (cfring (config p)) z} := by
  apply LocalPreembedding.of_radius2 (embeddable p).base.base.base.base.plain
    (fun _ => kernel_face) (embeddable p).kernel
  · exact (reading_edge p) r
  · intro d hd
    change (dart p) r.hom ((realization p).numbering ((cfmap (config p)).map.face d)) =
      rotation.vertexRotation ((dart p) r.hom ((realization p).numbering d))
    rw [(numbered_face p)]
    exact (r.turn _ (((kernel_iff p) _).mp (((numbered_kernel p) d).mpr hd))).symm
  · intro d hd
    rw [DualGraphQuery.arity_eq_degree rotation cyclic, ← (numbered_arity p), (source_arity p)]
    exact r.degree_eq _ (((kernel_iff p) _).mp (((numbered_kernel p) d).mpr hd))

theorem kernel_injective : Set.InjOn ((reading p) r)
    {z | (cfmap (config p)).map.Kernel (cfring (config p)) z} := by
  intro d hd e he eq
  have v : (vertex p) ((realization p).numbering d) = (vertex p) ((realization p).numbering e) :=
    r.core_injective (((kernel_iff p) _).mp (((numbered_kernel p) d).mpr hd))
      (((kernel_iff p) _).mp (((numbered_kernel p) e).mpr he))
      (congrArg (fun z : G.Dart => z.fst) eq)
  have face := ((same_face_iff p) _ _).mpr v
  rw [← (realization p).map_eq] at face
  have face' := (Hypermap.sameCycle_relabel (realization p).numbering
    (cfmap (config p)).map.face d e).mp face
  exact cface_inj_embed ((preembedding p) r cyclic) hd face' eq

/-- No global boundary injection is assumed. Arity and the retained complete
rotations prevent local collisions; exterior labels cannot be captured by the core. -/
theorem faithful : FaithfulKernel (cfmap (config p)).map (DualGraphQuery.map rotation)
    (cfring (config p)) ((reading p) r) := by
  refine ⟨(kernel_injective p) r cyclic, ?_⟩
  intro d e hd he eq
  have de : (reading p) r ((cfmap (config p)).map.edge d) = (reading p) r e :=
    ((reading_edge p) r d).trans eq
  have hk : (cfmap (config p)).map.Kernel (cfring (config p)) ((cfmap (config p)).map.edge d) := by
    apply ((numbered_kernel p) _).mp
    rw [(kernel_iff p)]
    by_contra low
    have bound : ((vertex p) ((realization p).numbering
        ((cfmap (config p)).map.edge d))).val < 10 := by omega
    exact r.outside _ _ bound (((kernel_iff p) _).mp (((numbered_kernel p) e).mpr he))
      (congrArg (fun z : G.Dart => z.fst) de)
  exact (kernel_injective p) r cyclic hk he de

theorem disk_injective (tri : ExceptionalOverlap.Triangular rotation) :
    Function.Injective (embdd (cfmap (config p)).map (DualGraphQuery.map rotation)
      (cfring (config p)) ((reading p) r)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact FaithfulKernelEmbedding.disk_injective (embeddable p) (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ tri) ((preembedding p) r cyclic) ((faithful p) r cyclic)

end FourColor.FourTriangleOccurrence
