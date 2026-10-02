import MettapediaFourColor.ContractTransport
import MettapediaFourColor.MinimalSingletonContract
import MettapediaFourColor.MinimalExceptionalEmbedding
import MettapediaFourColor.DualGraphQuery

/-!
# Contract witnesses on the actual facial dual

The dual query map is exactly the original source hypermap with its darts
relabeled. This equality transports actual singleton contract colourings
from graph-backed vertex minimality to the map used by local recognition.
-/

namespace FourColor.ActualDualContract

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationSystemPrimalGraphBacking GoertzelV24TwoEdgeCutMinimality
open ActualDualRotation

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u, u, u} V E) (two : OrbitFacesTwoSided RS)
  (unique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS) Finset.univ)

/-- All three permutations agree, including their orientation conventions. -/
theorem map_eq_source_relabel :
    DualGraphQuery.map (data RS two unique) =
      (SourceConstruction.sourceMap RS).relabel (darts RS two unique) := by
  let A := DualGraphQuery.map (data RS two unique)
  let B := (SourceConstruction.sourceMap RS).relabel (darts RS two unique)
  have he : A.edge = B.edge := by
    apply Equiv.ext
    intro z
    obtain ⟨d, rfl⟩ := (darts RS two unique).surjective z
    change (darts RS two unique d).symm =
      ((SourceConstruction.sourceMap RS).relabel (darts RS two unique)).edge
        (darts RS two unique d)
    rw [Hypermap.relabel_edge]
    exact (primalDartEquiv_alpha (dual RS two)
      (dual_endpoints_injective RS two unique) d).symm
  have hf : A.face = B.face := by
    apply Equiv.ext
    intro z
    obtain ⟨d, rfl⟩ := (darts RS two unique).surjective z
    change (data RS two unique).vertexRotation (darts RS two unique d) =
      ((SourceConstruction.sourceMap RS).relabel (darts RS two unique)).face
        (darts RS two unique d)
    rw [Hypermap.relabel_face]
    exact data_step RS two unique d
  have hn : A.node = B.node := by
    have h : A.node * A.face = B.node * A.face := by
      rw [A.node_mul_face_eq_edge_inv, hf, B.node_mul_face_eq_edge_inv, he]
    exact mul_right_cancel h
  exact Hypermap.ext he hn hf

variable {W : Type u} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- The exact map used by exceptional recognition has an actual colouring
for every singleton contract. No reference minimality hypothesis is added. -/
theorem singleton_colorable (d : (MinimalExceptionalEmbedding.graph original minimal).Dart) :
    (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)).CcColorable
      [d] := by
  let e := darts original.toRotationSystem minimal.facesTwoSided
    (GoertzelV24MinimalFaceIntersections.pairwiseUniqueSharedInteriorEdges original minimal)
  obtain ⟨k, hk⟩ := MinimalSingletonContract.colorable original minimal (e.symm d)
  rw [show MinimalExceptionalEmbedding.rotation original minimal =
    data original.toRotationSystem minimal.facesTwoSided
      (GoertzelV24MinimalFaceIntersections.pairwiseUniqueSharedInteriorEdges original minimal)
    from rfl, map_eq_source_relabel]
  refine ⟨k ∘ e.symm, ?_⟩
  simpa only [List.map_cons, List.map_nil, Equiv.apply_symm_apply] using
    Hypermap.ccColoring_push (SourceConstruction.sourceMap original.toRotationSystem)
      e [e.symm d] k hk

/-- An ordinary dual colouring would reconstruct a forbidden original Tait
colouring. This distinguishes a starting contract witness from a solution. -/
theorem not_colorable :
    ¬ (DualGraphQuery.map
      (MinimalExceptionalEmbedding.rotation original minimal)).FourColorable := by
  intro h
  rw [show MinimalExceptionalEmbedding.rotation original minimal =
    data original.toRotationSystem minimal.facesTwoSided
      (GoertzelV24MinimalFaceIntersections.pairwiseUniqueSharedInteriorEdges original minimal)
    from rfl, map_eq_source_relabel] at h
  obtain ⟨k, hk⟩ := h
  have hs := (Hypermap.coloring_relabel _ _ k).mp hk
  exact minimal.notColorable
    ⟨SourceConstruction.taitColoring minimal.spherical.cubic minimal.vertexRotationCyclic hs,
      SourceConstruction.taitColoring_nonzero minimal.spherical.cubic
        minimal.vertexRotationCyclic hs⟩

end
end FourColor.ActualDualContract
