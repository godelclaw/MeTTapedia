import MettapediaFourColor.GraphRotationRows
import MettapediaFourColor.SourceTait
import Mettapedia.GraphTheory.OrbitCountSplitting

/-!
# Planarity of a graph disk from its local faces and Euler counts

The reference quasicubic Euler formula, applied to the mirrored dual,
counts triangular inner faces symbolically. This avoids enumerating a
quadratic table of pairs belonging to the same face.
-/

namespace FourColor.GraphDiskEuler

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness GoertzelV24ConnectedMapEulerBound
open Mettapedia.GraphTheory.Hypermap.Reference
open SimpleGraphBridge PlanarGraphBoundaryClosure

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem primal_eq (data : Data G) : rotationPrimalGraph data.toRotationSystem = G := by
  ext u v
  constructor
  · rintro ⟨d, hu, hv⟩
    change d.fst = u at hu
    change d.snd = v at hv
    simpa only [← hu, ← hv] using d.adj
  · intro h
    exact ⟨⟨(u,v), h⟩, rfl, rfl⟩

theorem connected (data : Data G) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) : (rotationHypermap data).Connected := by
  have hc : (rotationPrimalGraph data.toRotationSystem).Connected :=
    (primal_eq data).symm ▸ conn
  have hr : VertexRotationCyclic data.toRotationSystem := by
    intro a b h
    exact (cyclic a.fst).2 rfl h.symm
  exact (compCount_preserved _).trans
    (hypermap_compCount_eq_one_of_primalConnected data.toRotationSystem hc hr)

theorem node_count (data : Data G) (cyclic : data.IsVertexwiseCyclic)
    (covered : Function.Surjective (fun d : G.Dart => d.fst)) :
    cycleCount (rotationHypermap data).node = Nat.card V := by
  rw [← orbitCount_eq_cycleCount]
  exact Mettapedia.GraphTheory.OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (fun d : G.Dart => d.fst) (rotationHypermap_cnode_iff data cyclic) covered

/-- The Euler balance is sufficient once the exact local disk faces,
vertex cycles and connectedness have been supplied. -/
theorem planar (data : Data G) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (covered : Function.Surjective (fun d : G.Dart => d.fst))
    (r : List G.Dart) (nonempty : r ≠ [])
    (boundary : IsCyclicChain (fun a b => b = data.toRotationSystem.phi a) r)
    (distinct : r.Nodup)
    (triangles : ∀ d, d ∉ r → data.toRotationSystem.phi
      (data.toRotationSystem.phi (data.toRotationSystem.phi d)) = d)
    (balance : 6 * (1 + Nat.card V) = Nat.card G.Dart + (2 * r.length + 12)) :
    (rotationHypermap data).Planar := by
  let H := rotationHypermap data
  have plain : H.Plain := by
    constructor
    · exact fun d => d.symm_symm
    · exact fun d => d.symm_ne
  have geo : (view H).UcyclePlainQuasicubicConnected r := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, distinct⟩, ?_⟩
    · exact (Hypermap.plain_mirror _).mpr ((Hypermap.plain_dual _).mpr plain)
    · constructor
      · exact triangles
      · intro d _
        exact face_ne H (rotationHypermap_edge data) (rotationHypermap_node_fst data) d
    · exact boundary
    · simpa only [view, Hypermap.connected_mirror, Hypermap.connected_dual]
        using connected data cyclic conn
  have counts : cycleCount H.node = Nat.card V := node_count data cyclic covered
  have hp := (Hypermap.quasicubic_Euler geo nonempty).mpr (by
    simpa only [view, Hypermap.mirror_face, Hypermap.dual_face, inv_inv, counts]
      using balance)
  exact (Hypermap.planar_dual _).mp ((Hypermap.planar_mirror _).mp hp)

end
end FourColor.GraphDiskEuler
