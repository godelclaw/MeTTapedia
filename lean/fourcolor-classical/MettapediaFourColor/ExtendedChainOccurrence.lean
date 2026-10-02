import MettapediaFourColor.ExtendedChainCompletion
import MettapediaFourColor.LocalPreembedding
import MettapediaFourColor.ActualDualLocalGeometry

/-!
# Complete cyclic-star occurrences of the nine-port chain

The source vertices determine actual darts. Five complete cyclic stars and
their degrees supply the preembedding. Only core vertices must be distinct;
different boundary labels may coincide outside the core. Facewise injectivity
then preserves the joint kernel witness needed for disk reconstruction.
-/

namespace FourColor.ExtendedChainOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearChainData Hypermap
open FaithfulKernelEmbedding

set_option maxRecDepth 32768

abbrev config := cf007
abbrev table := table007
abbrev vertex := vertex007
abbrev representative := representative007
abbrev degree := degree007
abbrev ring := ring007
abbrev faces := faces007
abbrev realization := realization007

theorem embeddable : (cfmap config).map.Embeddable (cfring config) :=
  embeddable_cfquiz (by decide +kernel)

theorem source_edge : ∀ d : Fin 60,
    input0006.graph.Adj (vertex d) (vertex (table.map.edge d)) := by decide +kernel

theorem source_plain : table.map.Plain := by constructor <;> decide +kernel

theorem same_face_iff (d e : Fin 60) :
    table.map.CFace d e ↔ vertex d = vertex e := by
  constructor
  · exact congr_of_sameCycle faces.vertex_face
  · intro eq
    apply (faces.same_face d).trans
    change table.map.CFace (representative (vertex d)) e
    rw [eq]
    exact (faces.same_face e).symm

theorem kernel_iff (d : Fin 60) :
    table.map.Kernel ring.reverse d ↔ 9 ≤ (vertex d).val := by
  simp only [Hypermap.Kernel, Hypermap.Fband, same_face_iff]
  revert d
  decide +kernel

theorem source_cycles : ∀ d : Fin 60,
    IsCyclicChain (fun u v => v = table.map.face u)
      (ConfigurationFaceGraph.faceCycle table.map d (degree (vertex d))) ∧
    (ConfigurationFaceGraph.faceCycle table.map d (degree (vertex d))).Nodup ∧
    (ConfigurationFaceGraph.faceCycle table.map d (degree (vertex d))) ≠ [] ∧
    (ConfigurationFaceGraph.faceCycle table.map d (degree (vertex d))).headD d = d := by
  unfold IsCyclicChain
  decide +kernel

theorem source_arity (d : Fin 60) : table.map.arity d = degree (vertex d) := by
  obtain ⟨hc, hn, he, hh⟩ := source_cycles d
  have eq := ConfigurationFaceGraph.faceCycle_eq_orbit (M := table.map)
    d (degree (vertex d)) hc hn he hh
  have len := congrArg List.length eq
  simpa [ConfigurationFaceGraph.faceCycle, length_orbitList, Hypermap.arity] using len.symm

theorem numbered_ring : (cfring config).map realization.numbering = ring.reverse := by
  change ((cfmap config).cpring.reverse).map realization.numbering = _
  rw [List.map_reverse, realization.ring, cpring007]

theorem numbered_kernel (d : (cfmap config).Dart) :
    table.map.Kernel ring.reverse (realization.numbering d) ↔
      (cfmap config).map.Kernel (cfring config) d := by
  rw [← numbered_ring, ← realization.map_eq]
  exact kernel_relabel _ _ _ _

theorem numbered_edge (d : (cfmap config).Dart) :
    realization.numbering ((cfmap config).map.edge d) =
      table.map.edge (realization.numbering d) := by
  rw [← realization.map_eq, Hypermap.relabel_edge]

theorem numbered_face (d : (cfmap config).Dart) :
    realization.numbering ((cfmap config).map.face d) =
      table.map.face (realization.numbering d) := by
  rw [← realization.map_eq, Hypermap.relabel_face]

theorem numbered_arity (d : (cfmap config).Dart) :
    table.map.arity (realization.numbering d) = (cfmap config).map.arity d := by
  rw [← realization.map_eq, arity_relabel]

variable {V : Type*} {G : SimpleGraph V}

def dart (f : input0006.graph →g G) (d : Fin 60) : G.Dart :=
  ⟨(f (vertex d), f (vertex (table.map.edge d))), f.map_adj (source_edge d)⟩

theorem dart_edge (f : input0006.graph →g G) (d : Fin 60) :
    dart f (table.map.edge d) = (dart f d).symm := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change f (vertex (table.map.edge (table.map.edge d))) = _
    rw [source_plain.edge_edge]
    rfl

variable [G.LocallyFinite]

/-- A geometric reading of all source edges, complete core rotations and
degrees. Boundary labels may identify with each other, but not with the core. -/
structure Occurrence (rotation : Data G) where
  hom : input0006.graph →g G
  turn : ∀ d : Fin 60, 9 ≤ (vertex d).val →
    rotation.vertexRotation (dart hom d) = dart hom (table.map.face d)
  degree_eq : ∀ v : Fin 14, 9 ≤ v.val → G.degree (hom v) = degree v
  core_injective : Set.InjOn hom {v | 9 ≤ v.val}
  outside : ∀ p v : Fin 14, p.val < 9 → 9 ≤ v.val → hom p ≠ hom v

variable [Finite V] {rotation : Data G} (r : Occurrence rotation)
  (cyclic : rotation.IsVertexwiseCyclic)

def reading (d : (cfmap config).Dart) : G.Dart := dart r.hom (realization.numbering d)

omit [Finite V] in
theorem reading_edge (d : (cfmap config).Dart) :
    reading r ((cfmap config).map.edge d) = (DualGraphQuery.map rotation).edge (reading r d) := by
  unfold reading
  rw [numbered_edge, dart_edge]
  rfl

include cyclic

theorem preembedding : Preembedding (cfmap config).map (DualGraphQuery.map rotation)
    (reading r) {z | (cfmap config).map.Kernel (cfring config) z} := by
  apply LocalPreembedding.of_radius2 embeddable.base.base.base.base.plain
    (fun _ => kernel_face) embeddable.kernel
  · exact reading_edge r
  · intro d hd
    change dart r.hom (realization.numbering ((cfmap config).map.face d)) =
      rotation.vertexRotation (dart r.hom (realization.numbering d))
    rw [numbered_face]
    exact (r.turn _ ((kernel_iff _).mp ((numbered_kernel d).mpr hd))).symm
  · intro d hd
    rw [DualGraphQuery.arity_eq_degree rotation cyclic, ← numbered_arity, source_arity]
    exact r.degree_eq _ ((kernel_iff _).mp ((numbered_kernel d).mpr hd))

theorem kernel_injective : Set.InjOn (reading r)
    {z | (cfmap config).map.Kernel (cfring config) z} := by
  intro d hd e he eq
  have v : vertex (realization.numbering d) = vertex (realization.numbering e) :=
    r.core_injective ((kernel_iff _).mp ((numbered_kernel d).mpr hd))
      ((kernel_iff _).mp ((numbered_kernel e).mpr he))
      (congrArg (fun z : G.Dart => z.fst) eq)
  have face := (same_face_iff _ _).mpr v
  rw [← realization.map_eq] at face
  have face' := (Hypermap.sameCycle_relabel realization.numbering
    (cfmap config).map.face d e).mp face
  exact cface_inj_embed (preembedding r cyclic) hd face' eq

/-- No global boundary injection is assumed. Arity and the retained complete
rotations prevent local collisions; exterior labels cannot be captured by the core. -/
theorem faithful : FaithfulKernel (cfmap config).map (DualGraphQuery.map rotation)
    (cfring config) (reading r) := by
  refine ⟨kernel_injective r cyclic, ?_⟩
  intro d e hd he eq
  have de : reading r ((cfmap config).map.edge d) = reading r e :=
    (reading_edge r d).trans eq
  have hk : (cfmap config).map.Kernel (cfring config) ((cfmap config).map.edge d) := by
    apply (numbered_kernel _).mp
    rw [kernel_iff]
    by_contra low
    have bound : (vertex (realization.numbering ((cfmap config).map.edge d))).val < 9 := by omega
    exact r.outside _ _ bound ((kernel_iff _).mp ((numbered_kernel e).mpr he))
      (congrArg (fun z : G.Dart => z.fst) de)
  exact kernel_injective r cyclic hk he de

theorem disk_injective (tri : ExceptionalOverlap.Triangular rotation) :
    Function.Injective (embdd (cfmap config).map (DualGraphQuery.map rotation)
      (cfring config) (reading r)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact FaithfulKernelEmbedding.disk_injective embeddable (DualGraphQuery.plain _)
    (DualGraphQuery.cubic _ tri) (preembedding r cyclic) (faithful r cyclic)

end FourColor.ExtendedChainOccurrence
