import MettapediaFourColor.ExceptionalDartReading
import MettapediaFourColor.LocalPreembedding

/-!
# The joint exceptional reading is an actual preembedding

The exact Y/H source numbering transports the completed cyclic stars and
edge map to the reference configuration carrier. The same function carries
the local faithfulness witness; no independent choice of an embedding is
made between recognition and reconstruction.
-/

namespace FourColor.ExceptionalPreembedding

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation Hypermap
open ExceptionalCore ExceptionalCoreOrientation ExceptionalOverlap
open ExceptionalConstruction FaithfulKernelEmbedding

theorem numbered_ring : (cfring config).map realization.numbering = ring.reverse := by
  change ((cfmap config).cpring.reverse).map realization.numbering = _
  rw [List.map_reverse, realization.ring, ExceptionalConstruction.cpring]

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

variable {V : Type*} [Finite V] {G : SimpleGraph V} [G.LocallyFinite]
  {rotation : Data G} (r : JointReading rotation)
  (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)

def reading (d : (cfmap config).Dart) : G.Dart :=
  ExceptionalDartReading.reading r tri cyclic (realization.numbering d)

/-- All preembedding fields use the explicit endpoint reading of the same
nineteen source vertices, including the full eleven-port boundary. -/
theorem preembedding :
    Preembedding (cfmap config).map (DualGraphQuery.map rotation) (reading r tri cyclic)
      {z | (cfmap config).map.Kernel (cfring config) z} := by
  apply LocalPreembedding.of_radius2 embeddable.base.base.base.base.plain
    (fun _ => kernel_face) embeddable.kernel
  · intro d
    change ExceptionalDartReading.reading r tri cyclic
      (realization.numbering ((cfmap config).map.edge d)) = _
    rw [numbered_edge]
    exact ExceptionalDartReading.edge r tri cyclic _
  · intro d hd
    change ExceptionalDartReading.reading r tri cyclic
      (realization.numbering ((cfmap config).map.face d)) = _
    rw [numbered_face]
    exact ExceptionalDartReading.face r tri cyclic ((numbered_kernel d).mpr hd)
  · intro d hd
    exact (ExceptionalDartReading.arity r tri cyclic ((numbered_kernel d).mpr hd)).trans
      (numbered_arity d)

/-- Source transport keeps the very same kernel identity and edge-reflection
witness used by the eventual disk-injectivity theorem. -/
theorem faithful
    (h : FaithfulKernel table.map (DualGraphQuery.map rotation) ring.reverse
      (ExceptionalDartReading.reading r tri cyclic)) :
    FaithfulKernel (cfmap config).map (DualGraphQuery.map rotation) (cfring config)
      (reading r tri cyclic) := by
  constructor
  · intro d hd e he eq
    exact realization.numbering.injective
      (h.injective ((numbered_kernel d).mpr hd) ((numbered_kernel e).mpr he) eq)
  · intro d e hd he eq
    apply realization.numbering.injective
    rw [numbered_edge]
    exact h.reflects_edge ((numbered_kernel d).mpr hd) ((numbered_kernel e).mpr he) eq

end FourColor.ExceptionalPreembedding
