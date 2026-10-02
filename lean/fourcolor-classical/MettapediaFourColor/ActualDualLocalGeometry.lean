import MettapediaFourColor.ActualDualContract

/-!
# Geometry consumed by local exterior repair

The actual dual is plain, cubic and planar. These are precisely the ambient
geometric hypotheses used after local kernel faithfulness has been proved.
No conversion to reference dart-minimality is needed.
-/

namespace FourColor.DualGraphQuery

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalOverlap

variable {V : Type*} {G : SimpleGraph V} (rotation : Data G)

theorem plain : (map rotation).Plain := by
  constructor
  · exact SimpleGraph.Dart.symm_symm
  · intro d eq
    exact d.adj.ne (congrArg (fun e : G.Dart => e.fst) eq).symm

theorem cubic (tri : Triangular rotation) : (map rotation).Cubic := by
  have inv_node (d : G.Dart) : ((map rotation).node⁻¹) d =
      rotation.vertexRotation d.symm := by
    apply (map rotation).node.injective
    change (map rotation).node ((map rotation).node.symm d) = _
    rw [Equiv.apply_symm_apply]
    change d = (rotation.vertexRotation.symm (rotation.vertexRotation d.symm)).symm
    simp only [Equiv.symm_apply_apply, SimpleGraph.Dart.symm_symm]
  have power : (map rotation).node⁻¹ ^ 3 = 1 := by
    apply Equiv.ext
    intro d
    simpa only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      inv_node] using tri d
  have forward : (map rotation).node ^ 3 = 1 := by
    apply inv_injective
    rw [inv_one, ← inv_pow]
    exact power
  constructor
  · intro d _
    have h := congrArg (fun p : Equiv.Perm G.Dart => p d) forward
    simpa [pow_succ, Equiv.Perm.mul_apply] using h
  · intro d _ eq
    have h := congrArg (fun e : G.Dart => e.snd) eq
    change (rotation.vertexRotation.symm d).fst = d.snd at h
    have fst := rotation.vertexRotation_fst (rotation.vertexRotation.symm d)
    rw [Equiv.apply_symm_apply] at fst
    rw [← fst] at h
    exact d.adj.ne h

end FourColor.DualGraphQuery

namespace FourColor.ActualDualLocalGeometry

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24MinimalFaceIntersections

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

theorem planar :
    (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)).Planar := by
  change (DualGraphQuery.map (ActualDualRotation.data original.toRotationSystem
    minimal.facesTwoSided (pairwiseUniqueSharedInteriorEdges original minimal))).Planar
  rw [ActualDualContract.map_eq_source_relabel, Hypermap.planar_relabel]
  exact SourceConstruction.sourceMap_planar minimal.toBridgelessSphericalCubicMapData

end
end FourColor.ActualDualLocalGeometry
