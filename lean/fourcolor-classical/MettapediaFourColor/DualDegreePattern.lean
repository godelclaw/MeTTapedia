import MettapediaFourColor.PentagonalDiamondFaceReduction
import MettapediaFourColor.GraphColoringBridge
import MettapediaFourColor.HypermapTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr

/-!
# Degree patterns transported to actual dual face patterns

An exact dart equivalence exchanging vertex rotation with face traversal
retains complete degrees and cyclic neighbour order. A degree-five vertex
with three consecutive degree-five neighbours therefore supplies the
existing pentagonal-diamond exclusion in the dual. No occurrence supply
or minimality of either map is assumed by the representation bridge.
-/

namespace FourColor.DualDegreePattern

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24OrbitCountCongr GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  (primal : Data G) (dual : Data H) (darts : G.Dart ≃ H.Dart)
  (face_step : ∀ d, dual.toRotationSystem.phi (darts d) =
    darts (primal.vertexRotation d))

include face_step in
theorem face_power (n : ℕ) (d : G.Dart) :
    (dual.toRotationSystem.phi ^ n) (darts d) =
      darts ((primal.vertexRotation ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, ih, face_step]

include face_step in
/-- Complete dual face length equals complete primal degree. -/
theorem face_card (cyclic : primal.IsVertexwiseCyclic) (d : G.Dart) :
    (dual.toRotationSystem.faceOrbit (darts d)).card = G.degree d.fst := by
  classical
  have conj : (darts.symm.trans primal.vertexRotation).trans darts =
      dual.toRotationSystem.phi := by
    apply Equiv.ext
    intro y
    exact (face_step (darts.symm y)).symm.trans
      (congrArg dual.toRotationSystem.phi (darts.apply_symm_apply y))
  have fst_power (n : ℕ) (x : G.Dart) :
      ((primal.vertexRotation ^ n) x).fst = x.fst := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply,
        primal.vertexRotation_fst] using ih
  have same (x : G.Dart) : primal.vertexRotation.SameCycle d x ↔ x.fst = d.fst := by
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
      exact fst_power n d
    · intro hx
      exact (cyclic d.fst).2 rfl hx
  let fiber : Finset G.Dart := Finset.univ.filter fun x => x.fst = d.fst
  let e : {x // x ∈ fiber} ≃
      {x // x ∈ dual.toRotationSystem.faceOrbit (darts d)} :=
    darts.subtypeEquiv (fun x => by
      have h := sameCycle_conjEquiv_iff darts primal.vertexRotation d x
      rw [conj] at h
      rw [dual.toRotationSystem.mem_faceOrbit]
      simpa only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
        using (h.trans (same x)).symm)
  have hc : fiber.card = G.degree d.fst := by
    change ({x : G.Dart | x.fst = d.fst} : Finset G.Dart).card = _
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent d.fst _ _).symm
  have he : (dual.toRotationSystem.faceOrbit (darts d)).card = fiber.card := by
    simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm
  exact he.trans hc

variable (flip : ∀ d, darts d.symm = (darts d).symm)

include face_step flip in
/-- Exact duality preserves all three permutations, not only face sizes. -/
theorem hypermap_dual : SimpleGraphBridge.rotationHypermap dual =
    (SimpleGraphBridge.rotationHypermap primal).dual.relabel darts := by
  let A := SimpleGraphBridge.rotationHypermap dual
  let B := (SimpleGraphBridge.rotationHypermap primal).dual.relabel darts
  have he : A.edge = B.edge := by
    apply Equiv.ext
    intro y
    obtain ⟨d, rfl⟩ := darts.surjective y
    change (darts d).symm =
      ((SimpleGraphBridge.rotationHypermap primal).dual.relabel darts).edge (darts d)
    rw [Hypermap.relabel_edge]
    exact (flip d).symm
  have hf : A.face = B.face := by
    apply Equiv.ext
    intro y
    obtain ⟨d, rfl⟩ := darts.surjective y
    change dual.toRotationSystem.phi (darts d) =
      ((SimpleGraphBridge.rotationHypermap primal).dual.relabel darts).face (darts d)
    rw [Hypermap.relabel_face]
    exact face_step d
  have hn : A.node = B.node := by
    have h : A.node * A.face = B.node * A.face := by
      rw [A.node_mul_face_eq_edge_inv, hf, B.node_mul_face_eq_edge_inv, he]
    exact mul_right_cancel h
  exact Hypermap.ext he hn hf

include face_step flip in
theorem planar (h : (SimpleGraphBridge.rotationHypermap primal).Planar) :
    (SimpleGraphBridge.rotationHypermap dual).Planar := by
  rw [hypermap_dual primal dual darts face_step flip,
    Hypermap.planar_relabel, Hypermap.planar_dual]
  exact h

include face_step flip in
/-- The three neighbours occupy the same ordered positions after duality. -/
theorem diamond (cyclic : primal.IsVertexwiseCyclic) (root : G.Dart)
    (central : G.degree root.fst = 5)
    (neighbours : ∀ i : Fin 5, 1 ≤ i.val → i.val ≤ 3 →
      G.degree (((primal.vertexRotation ^ i.val) root).snd) = 5) :
    PentagonalDiamond.FaceLengths dual (darts root) := by
  refine ⟨(face_card primal dual darts face_step cyclic root).trans central, ?_⟩
  intro i hlo hhi
  unfold PentagonalCoronaGeometry.center
  rw [face_power primal dual darts face_step, ← flip]
  exact (face_card primal dual darts face_step cyclic _).trans (neighbours i hlo hhi)

include face_step flip in
/-- Only minimality in the dual is needed for the existing reduction consumer. -/
theorem not_in_minimal (cyclic : primal.IsVertexwiseCyclic) (root : G.Dart)
    (central : G.degree root.fst = 5)
    (neighbours : ∀ i : Fin 5, 1 ≤ i.val → i.val ≤ 3 →
      G.degree (((primal.vertexRotation ^ i.val) root).snd) = 5)
    (minimal : GraphBackedVertexMinimalTaitCounterexample dual) : False :=
  PentagonalDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
    dual (darts root)
    (diamond primal dual darts face_step flip cyclic root central neighbours) minimal

end
end FourColor.DualDegreePattern
