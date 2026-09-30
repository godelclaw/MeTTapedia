import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr

/-!
# Structural transport along exact dart and vertex equivalences

An exact relabelling preserves the class of connected bridgeless spherical
cubic maps. Edge identity is recovered from the involution, and facial cycles
from the edge and vertex permutations. This lets literal sewing certificates
transfer geometry as well as colourings.
-/

namespace Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport

open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationEdgeBridge GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitCountCongr

noncomputable section
variable {V E W F : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
  (S : RotationSystem V E) (T : RotationSystem W F)
  (d : S.D ≃ T.D) (v : V ≃ W)
  (ha : ∀ x, d (S.alpha x) = T.alpha (d x))
  (hv : ∀ x, v (S.vertOf x) = T.vertOf (d x))

private theorem edge_eq_iff (R : RotationSystem V E) (x y : R.D) :
    R.edgeOf x = R.edgeOf y ↔ x = y ∨ x = R.alpha y := by
  rw [← R.mem_dartsOn, R.dartsOn_eq_pair_of_mem (R.mem_dartsOn.mpr rfl)]
  simp

include ha in
theorem edge_eq_iff_map (x y : S.D) :
    S.edgeOf x = S.edgeOf y ↔ T.edgeOf (d x) = T.edgeOf (d y) := by
  rw [edge_eq_iff, edge_eq_iff, ← ha, d.injective.eq_iff, d.injective.eq_iff]

def primalIso : rotationPrimalGraph S ≃g rotationPrimalGraph T where
  toEquiv := v
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨z, hz, hza⟩
      obtain ⟨a, rfl⟩ := d.surjective z
      refine ⟨a, v.injective ((hv a).trans hz), ?_⟩
      apply v.injective
      rw [hv, ha]
      exact hza
    · rintro ⟨a, rfl, rfl⟩
      exact ⟨d a, (hv a).symm, (ha a ▸ hv (S.alpha a)).symm⟩

include d v hv in
theorem cubic (h : S.IsCubic) : T.IsCubic := by
  intro w
  obtain ⟨x, rfl⟩ := v.surjective w
  let e : {a // a ∈ S.dartsAt x} ≃ {b // b ∈ T.dartsAt (v x)} :=
    d.subtypeEquiv (fun a => by
      simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hv]
      exact v.injective.eq_iff.symm)
  have hc := Fintype.card_congr e
  have hc' : (T.dartsAt (v x)).card = (S.dartsAt x).card := by
    simpa only [Fintype.card_coe] using hc.symm
  exact hc'.trans (h x)

include d v ha hv in
theorem bridgeFree (h : EdgeBridgeFree S) : EdgeBridgeFree T := by
  intro b
  obtain ⟨a, rfl⟩ := d.surjective b
  have mapped := reachable_map_of_adj_eq_or_adj v
    (source := edgeDeletedPrimalGraph S (S.edgeOf a))
    (target := edgeDeletedPrimalGraph T (T.edgeOf (d a))) (by
      rintro x y ⟨z, hz, rfl, rfl⟩
      refine Or.inr ⟨d z, ?_, (hv z).symm, ?_⟩
      · exact fun he => hz ((edge_eq_iff_map S T d ha z a).mpr he)
      · rw [← ha, ← hv]) (h a)
  simpa only [hv, ha] using mapped

variable (hr : ∀ x, d (S.rho x) = T.rho (d x))

include hr in
theorem rho_conjugate : (d.symm.trans S.rho).trans d = T.rho := by
  apply Equiv.ext
  intro x
  exact (hr (d.symm x)).trans (congrArg T.rho (d.apply_symm_apply x))

include d v hv hr in
theorem rotationCyclic (h : VertexRotationCyclic S) : VertexRotationCyclic T := by
  intro b c hbc
  obtain ⟨x, rfl⟩ := d.surjective b
  obtain ⟨y, rfl⟩ := d.surjective c
  rw [← rho_conjugate S T d hr, sameCycle_conjEquiv_iff]
  apply h
  apply v.injective
  simpa only [hv] using hbc

include ha hr in
theorem phi_commute (x : S.D) : d (S.phi x) = T.phi (d x) := by
  simp only [RotationSystem.phi_apply, hr, ha]

include ha hr in
/-- Exact dart transport preserves each actual face length. -/
theorem faceOrbit_card (x : S.D) : (S.faceOrbit x).card = (T.faceOrbit (d x)).card := by
  have hc : (d.symm.trans S.phi).trans d = T.phi := by
    apply Equiv.ext
    intro y
    exact (phi_commute S T d ha hr (d.symm y)).trans
      (congrArg T.phi (d.apply_symm_apply y))
  let e : {y // y ∈ S.faceOrbit x} ≃ {y // y ∈ T.faceOrbit (d x)} :=
    d.subtypeEquiv (fun y => by
      rw [S.mem_faceOrbit, T.mem_faceOrbit, ← hc, sameCycle_conjEquiv_iff])
  simpa only [Fintype.card_coe] using Fintype.card_congr e

def faceEquiv : OrbitFace S ≃ OrbitFace T := by
  have hc : (d.symm.trans S.phi).trans d = T.phi := by
    apply Equiv.ext
    intro x
    exact (phi_commute S T d ha hr (d.symm x)).trans
      (congrArg T.phi (d.apply_symm_apply x))
  exact Quotient.congr d (fun x y => by
    change S.phi.SameCycle x y ↔ T.phi.SameCycle (d x) (d y)
    rw [← hc, sameCycle_conjEquiv_iff])

include d v ha hv hr in
/-- All four geometric fields follow from the same exact relabelling. -/
theorem mapClass (h : BridgelessSphericalCubicMapData S) :
    BridgelessSphericalCubicMapData T where
  spherical := {
    cubic := cubic S T d v hv h.spherical.cubic
    euler := by
      have he : Fintype.card E = Fintype.card F := by
        have hd := Fintype.card_congr d
        rw [S.card_darts_eq_twice_card_edges, T.card_darts_eq_twice_card_edges] at hd
        omega
      rw [← Fintype.card_congr v, ← he, ← Fintype.card_congr (faceEquiv S T d ha hr)]
      exact h.spherical.euler }
  primalConnected := (primalIso S T d v ha hv).connected_iff.mp h.primalConnected
  vertexRotationCyclic := rotationCyclic S T d v hv hr h.vertexRotationCyclic
  edgeBridgeFree := bridgeFree S T d v ha hv h.edgeBridgeFree

end
end Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport
