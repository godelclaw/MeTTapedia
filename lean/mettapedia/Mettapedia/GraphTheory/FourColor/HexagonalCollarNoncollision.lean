import Mettapedia.GraphTheory.FourColor.HexagonalCollar

/-!
# Hexagonal collars cannot identify candidate vertices

The old complete boundary and hexagonal face closure force every candidate
star outside the old side. Same-type identifications contradict the cubic
star. A mixed identification propagates by reflection of the cyclic indices;
reducing their distance reaches a fixed point of edge reversal. Consequently
the collar construction needs no separate candidate-distinctness premise.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab

open ZigzagRing PhysicalForkCodeFaces GoertzelV24RotationCutDartDecomposition
open Fin.NatCast

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {inner : V → Prop} (S : ZigzagSlab RS k inner)

theorem collarInput_outside (i : Fin k) :
    ¬ S.inner' (RS.vertOf (S.collarInput i)) := (S.outPort i).2

theorem collarInput_injective : Function.Injective S.collarInput := by
  intro i j h
  have he := congrArg RS.alpha h
  simp only [collarInput, RS.alpha_involutive] at he
  exact Sum.inr.inj (Sum.inr.inj (S.ι_inj he))

variable (hC : Cubic3 RS) (hS : S.RotationCompatible) (hh : S.HexagonalSeam)

include hC hS hh

theorem collarMiddle_ne_output (i j : Fin k) :
    S.collarMiddle i ≠ S.ι (.inr (.inr j)) := by
  intro h
  have he := S.collar_second_edge hC hS hh i
  rw [h, hS] at he
  change RS.alpha (S.ι (.inl (.inl (j, true)))) = _ at he
  rw [S.alpha_interior] at he
  have hin := S.slab_inner' (.inl (flip k (.inl (j, true))))
  rw [he, RS.vert_rho, RS.vert_rho] at hin
  exact S.collarInput_outside (i + 1) hin

/-- Complete old boundary maps exclude a return into the old side, without
assuming that different new candidate vertices are distinct. -/
theorem collarMiddle_outside (i : Fin k) :
    ¬ S.inner' (RS.vertOf (S.collarMiddle i)) := by
  intro hi
  let b : BoundaryDart RS S.inner' := ⟨⟨S.collarMiddle i, hi⟩, by
    simpa only [collarMiddle, RS.alpha_involutive, RS.vert_rho] using
      S.collarInput_outside i⟩
  obtain ⟨j, hj⟩ := S.outPort_surjective b
  exact S.collarMiddle_ne_output hC hS hh i j
    (congrArg (fun b : BoundaryDart RS S.inner' => b.1.1) hj).symm

theorem collarInput_ne_rotate (i j : Fin k) :
    S.collarInput i ≠ RS.rho (S.collarInput j) := by
  intro h
  have he := congrArg RS.alpha h
  change RS.alpha (RS.alpha (S.ι (.inr (.inr i)))) = S.collarMiddle j at he
  rw [RS.alpha_involutive] at he
  exact S.collarMiddle_ne_output hC hS hh j i he.symm

theorem collarInput_vertex_injective :
    Function.Injective (fun i => RS.vertOf (S.collarInput i)) := by
  intro i j h
  rcases hC.fiber (S.collarInput i) (S.collarInput j) h.symm with he | he | he
  · exact S.collarInput_injective he.symm
  · exact (S.collarInput_ne_rotate hC hS hh j i he).elim
  · have hr := congrArg RS.rho he
    rw [hC.cube] at hr
    exact (S.collarInput_ne_rotate hC hS hh i j hr.symm).elim

omit hC hS hh in
theorem collarMiddle_injective : Function.Injective S.collarMiddle := by
  intro i j h
  apply S.collarInput_injective
  apply RS.rho.injective
  simpa only [collarMiddle, RS.alpha_involutive] using congrArg RS.alpha h

theorem collarMiddle_ne_rotate (i j : Fin k) :
    S.collarMiddle i ≠ RS.rho (S.collarMiddle j) := by
  intro h
  have he : RS.rho (S.collarInput i) =
      RS.rho (RS.rho (S.collarInput (j + 1))) := by
    calc
      RS.rho (S.collarInput i) = RS.alpha (S.collarMiddle i) := by
        simp only [collarMiddle, RS.alpha_involutive]
      _ = RS.alpha (RS.rho (S.collarMiddle j)) := congrArg RS.alpha h
      _ = _ := S.collar_second_edge hC hS hh j
  exact S.collarInput_ne_rotate hC hS hh i (j + 1) (RS.rho.injective he)

theorem collarMiddle_vertex_injective :
    Function.Injective (fun i => RS.vertOf (S.collarMiddle i)) := by
  intro i j h
  rcases hC.fiber (S.collarMiddle i) (S.collarMiddle j) h.symm with he | he | he
  · exact S.collarMiddle_injective he.symm
  · exact (S.collarMiddle_ne_rotate hC hS hh j i he).elim
  · have hr := congrArg RS.rho he
    rw [hC.cube] at hr
    exact (S.collarMiddle_ne_rotate hC hS hh i j hr.symm).elim

/-- A putative mixed collision has only one possible oriented star slot. -/
theorem collarMixed_slot (i j : Fin k)
    (h : RS.vertOf (S.collarMiddle j) = RS.vertOf (S.collarInput i)) :
    S.collarMiddle j = RS.rho (S.collarInput i) := by
  rcases hC.fiber (S.collarInput i) (S.collarMiddle j) h with he | he | he
  · have ho : ¬ S.inner' (RS.vertOf (RS.alpha (S.collarMiddle j))) := by
      simpa only [collarMiddle, RS.alpha_involutive, RS.vert_rho] using
        S.collarInput_outside j
    apply (ho ?_).elim
    rw [he]
    simpa only [collarInput, RS.alpha_involutive] using S.slab_inner' (.inr (.inr i))
  · exact he
  · have hn := S.collar_second_edge hC hS hh j
    rw [he, hC.cube] at hn
    have hin : S.inner' (RS.vertOf (RS.alpha (S.collarInput i))) := by
      simpa only [collarInput, RS.alpha_involutive] using S.slab_inner' (.inr (.inr i))
    rw [hn, RS.vert_rho, RS.vert_rho] at hin
    exact (S.collarInput_outside (j + 1) hin).elim

omit hC hS hh in
theorem collarReflection_symm (i j : Fin k)
    (h : S.collarMiddle j = RS.rho (S.collarInput i)) :
    S.collarMiddle i = RS.rho (S.collarInput j) := by
  have he := congrArg RS.alpha h
  simpa only [collarMiddle, RS.alpha_involutive] using he.symm

/-- A mixed identification propagates in opposite directions around the
two candidate types. -/
theorem collarReflection_step (i j : Fin k)
    (h : S.collarMiddle j = RS.rho (S.collarInput i)) :
    S.collarMiddle (j - 1) = RS.rho (S.collarInput (i + 1)) := by
  have hs := S.collarReflection_symm i j h
  have hi := S.collar_second_edge hC hS hh i
  rw [hs] at hi
  have hj := congrArg RS.alpha (S.collar_second_edge hC hS hh (j - 1))
  simp only [RS.alpha_involutive, sub_add_cancel] at hj
  exact RS.rho.injective (hj.trans hi)

/-- Repeated reflection reaches equal or adjacent indices, where the alleged
identification makes an edge its own reverse. No parity of the width is assumed. -/
theorem collarReflection_impossible (i j : Fin k) :
    S.collarMiddle j ≠ RS.rho (S.collarInput i) := by
  have hn : ∀ n : ℕ, ∀ a : Fin k,
      S.collarMiddle (a + (↑n : Fin k)) ≠ RS.rho (S.collarInput a) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      intro a h
      simp only [Nat.cast_zero, add_zero] at h
      exact RS.alpha_fixfree (RS.rho (S.collarInput a)) h
    | one =>
      intro a h
      simp only [Nat.cast_one] at h
      have hs := S.collarReflection_symm a (a + 1) h
      have he := S.collar_second_edge hC hS hh a
      rw [hs] at he
      exact RS.alpha_fixfree (RS.rho (RS.rho (S.collarInput (a + 1)))) he
    | more n ih _ =>
      intro a h
      have hs := S.collarReflection_step hC hS hh a (a + (↑(n + 2) : Fin k)) h
      apply ih (a + 1)
      have htwo : (2 : Fin k) - 1 = 1 := by
        rw [← one_add_one_eq_two, add_sub_cancel_right]
      convert hs using 1
      simp [Nat.cast_add, add_sub_assoc, add_comm, add_left_comm, htwo]
  simpa only [Fin.cast_val_eq_self, add_sub_cancel] using hn (j - i).val i

/-- Hexagonal face closure itself excludes every candidate-vertex collision. -/
theorem collarVertex_injective : Function.Injective S.collarVertex := by
  intro v w h
  cases v with
  | inl i =>
    cases w with
    | inl j => exact congrArg Sum.inl (S.collarInput_vertex_injective hC hS hh h)
    | inr j =>
      exact (S.collarReflection_impossible hC hS hh i j
        (S.collarMixed_slot hC hS hh i j h.symm)).elim
  | inr i =>
    cases w with
    | inl j =>
      exact (S.collarReflection_impossible hC hS hh j i
        (S.collarMixed_slot hC hS hh j i h)).elim
    | inr j => exact congrArg Sum.inr (S.collarMiddle_vertex_injective hC hS hh h)

/-- The successor now requires face conditions only; its distinct vertices
and complete ordered interfaces are constructed. -/
def hexagonalNextRow (hs : S.CollarShortFaces) : ZigzagSlab RS k S.inner' :=
  S.nextRow hC hS hh (S.collarVertex_injective hC hS hh) hs

theorem hexagonalNextRow_rotation (hs : S.CollarShortFaces) :
    (S.hexagonalNextRow hC hS hh hs).RotationCompatible :=
  S.nextRow_rotation hC hS hh (S.collarVertex_injective hC hS hh) hs

/-- The geometry-derived row transports the full compatible colouring
relation, with no separate vertex-distinctness hypothesis. -/
theorem hexagonalNextRow_support (hs : S.CollarShortFaces) (y : Fin k → Color) :
    let T := S.hexagonalNextRow hC hS hh hs
    (fun b => y (T.outEquiv.symm b)) ∈ sideSupport RS T.inner' ↔
      ∃ x : Fin k → Color, (fun b => x (S.outEquiv.symm b)) ∈ sideSupport RS S.inner' ∧
        Step k x y :=
  S.nextRow_support hC hS hh (S.collarVertex_injective hC hS hh) hs y

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab
