import MettapediaFourColor.ExceptionalCoreOrientation

/-!
# Completing actual vertex stars across facial seams

Rotation powers enumerate an actual vertex star. Its degree supplies the
period, while triangular closure identifies the two readings of an exterior
corner on opposite ends of an edge. These laws retain actual darts and do
not assume that boundary labels have distinct images.
-/

namespace FourColor.FacialStarCompletion

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

omit [G.LocallyFinite] in
theorem pow_fst (d : G.Dart) (n : ℕ) :
    ((rotation.vertexRotation ^ n) d).fst = d.fst := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, rotation.vertexRotation_fst, ih]

omit [G.LocallyFinite] in
/-- The preceding corner at one end is the succeeding corner at the other. -/
theorem across_edge (tri : Triangular rotation) (d : G.Dart) :
    (rotation.vertexRotation.symm d).snd = (rotation.vertexRotation d.symm).snd := by
  have h := congrArg (fun e : G.Dart => e.fst)
    (tri (rotation.vertexRotation.symm d).symm)
  simp only [SimpleGraph.Dart.symm_symm, Equiv.apply_symm_apply,
    rotation.vertexRotation_fst] at h
  exact h.symm

variable [Finite V]

theorem pow_degree (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart) :
    (rotation.vertexRotation ^ G.degree d.fst) d = d := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let fiber : Finset G.Dart := Finset.univ.filter fun e => e.fst = d.fst
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic d.fst
  have hcard : fiber.card = G.degree d.fst := by
    change ({e : G.Dart | e.fst = d.fst} : Finset G.Dart).card = G.degree d.fst
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent d.fst _ _).symm
  have h := hc.pow_card_apply (show d ∈ fiber by simp [fiber])
  simpa only [hcard] using h

theorem pow_pred (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart) :
    (rotation.vertexRotation ^ (G.degree d.fst - 1)) d =
      rotation.vertexRotation.symm d := by
  have pos : 0 < G.degree d.fst := d.adj.degree_pos_left
  apply rotation.vertexRotation.injective
  rw [Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ']
  rw [Nat.sub_add_cancel pos, pow_degree rotation cyclic]

/-- Every actual outgoing dart occurs within the degree-long rotation. -/
theorem covers (cyclic : rotation.IsVertexwiseCyclic) (base d : G.Dart)
    (same : d.fst = base.fst) :
    ∃ n < G.degree base.fst, (rotation.vertexRotation ^ n) base = d := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let fiber : Finset G.Dart := Finset.univ.filter fun e => e.fst = base.fst
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic base.fst
  have hcard : fiber.card = G.degree base.fst := by
    change ({e : G.Dart | e.fst = base.fst} : Finset G.Dart).card = G.degree base.fst
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent base.fst _ _).symm
  obtain ⟨n, hn, he⟩ := hc.exists_pow_eq
    (show base ∈ fiber by simp [fiber]) (show d ∈ fiber by simp [fiber, same])
  exact ⟨n, hcard ▸ hn, he⟩

end FourColor.FacialStarCompletion
