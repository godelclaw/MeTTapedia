import MettapediaFourColor.PlanarGraphBoundaryClosure
import MettapediaFourColor.ResidualSeedRepairReconstruction

/-!
# Reconstruct the residual seed from planar exterior geometry

The exterior closure assumption in `whole_repair` is discharged by the
actual exterior rotation. Its facial boundary must read the same eleven
ports, in order; its other faces must be triangular. Both colour witnesses
are retained by the exact primal/dual bridge.

This is uniform in exterior size. Recognition of the disk geometry after
deletion and supply of the seed class are separate obligations.
-/

namespace FourColor.ResidualSeedRepairCertificate

open FiveTriangleCollapseObstruction KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

noncomputable section

/-- Exact planar exterior geometry supplies the closure needed to fill the
seven core vertices after a compatible exterior repair. -/
theorem whole_repair_of_planar_disk
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {W : Type} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {data : Data G} {s : ThreeBlockGeometry.Patch data}
    (e : ThreeBlockGeometry.ExteriorReading s H)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (exterior : Data H) (cyclic : exterior.IsVertexwiseCyclic)
    (planar : (SimpleGraphBridge.rotationHypermap exterior).Planar)
    (r : List H.Dart)
    (boundary : IsCyclicChain (fun a b => b = exterior.toRotationSystem.phi a) r)
    (distinct : r.Nodup)
    (triangles : ∀ d, d ∉ r → exterior.toRotationSystem.phi
      (exterior.toRotationSystem.phi (exterior.toRotationSystem.phi d)) = d)
    (ordered : r.map (fun d => d.fst) = (List.finRange 11).map e.ports)
    (C : H.Coloring Color)
    (initial : ∀ j, C (e.ports j) = ThreeBlockCore.word false false false j) :
    ∃ D : H.Coloring Color, ∃ K : G.Coloring Color,
      ∀ w, K (e.embedding w) = D w := by
  have closed := PlanarGraphBoundaryClosure.rotation_closed exterior cyclic planar
    r boundary distinct triangles
  rw [ordered] at closed
  exact whole_repair e covers stars closed C initial

end
end FourColor.ResidualSeedRepairCertificate
