import Mettapedia.GraphTheory.FourColor.DualTruncateFaceCoverFrame
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# Recovering a source from a marked target frame

The marked faces determine a matching and the cyclic order of its three
dart slots. The target edge involution then supplies both the source edge
flip and the source face permutation. Source vertices and edges are their
actual permutation orbits. Reconstruction preserves alpha, rho and vertex
identity exactly; an already constructed source is not an input.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateInverse

open DualTruncateFaceCoverFrame GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness GoertzelV24OrbitFaceTwoSided
open GoertzelV24PermutationOrbitSurgery

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {W F : Type u} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
  (T : RotationSystem.{u,u,u} W F)

structure Data where
  frame : Frame T
  marked : OrbitFace T → Prop
  mark : ∀ x, marked (dartOrbitFace T (frame.dart x)) ↔ x.2 = 2

def fromCover (hc : T.IsCubic) (hcyc : VertexRotationCyclic T)
    (c : Cover T) : Data T where
  frame := DualTruncateFaceCoverFrame.fromCover T hc hcyc c
  marked := c.marked
  mark := fromCover_marked_iff T hc hcyc c

variable (d : Data T)

def pulledAlpha (x : W × Fin 3) : W × Fin 3 :=
  d.frame.dart.symm (T.alpha (d.frame.dart x))

@[simp] theorem pulledAlpha_map (x : W × Fin 3) :
    d.frame.dart (pulledAlpha T d x) = T.alpha (d.frame.dart x) :=
  d.frame.dart.apply_symm_apply _

@[simp] theorem pulledAlpha_involutive (x : W × Fin 3) :
    pulledAlpha T d (pulledAlpha T d x) = x := by
  simp only [pulledAlpha, Equiv.apply_symm_apply, T.alpha_involutive,
    Equiv.symm_apply_apply]

theorem phi_frame (x : W × Fin 3) :
    T.phi (d.frame.dart x) =
      d.frame.dart ((pulledAlpha T d x).1, (pulledAlpha T d x).2 + 1) := by
  rw [RotationSystem.phi_apply, ← pulledAlpha_map, d.frame.turn]

theorem pulled_mark (x : W × Fin 3) :
    (pulledAlpha T d x).2 = 2 ↔ x.2 + 1 = 2 := by
  have hf := dartOrbitFace_phi_eq T (T.alpha (d.frame.dart x))
  have he : dartOrbitFace T (T.alpha (d.frame.dart x)) =
      dartOrbitFace T (d.frame.dart (x.1, x.2 + 1)) := by
    calc
      _ = dartOrbitFace T (T.phi (T.alpha (d.frame.dart x))) := hf.symm
      _ = dartOrbitFace T (T.rho (d.frame.dart x)) := by
        rw [RotationSystem.phi_apply, T.alpha_involutive]
      _ = _ := congrArg (dartOrbitFace T) (d.frame.turn x)
  rw [← d.mark, pulledAlpha_map, he]
  exact d.mark _

theorem pulled_next_mark (x : W × Fin 3) :
    (pulledAlpha T d x).2 + 1 = 2 ↔ x.2 = 2 := by
  have h := d.mark ((pulledAlpha T d x).1, (pulledAlpha T d x).2 + 1)
  rw [← phi_frame, dartOrbitFace_phi_eq] at h
  exact h.symm.trans (d.mark x)

def flipSlot (i : Fin 3) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 2 else 1

private theorem flipSlot_characterization : ∀ i j : Fin 3,
    (j = 2 ↔ i + 1 = 2) → (j + 1 = 2 ↔ i = 2) → j = flipSlot i := by
  decide +kernel

/-- The geometric mark forces all three slot transitions of alpha. -/
theorem pulled_slot (x : W × Fin 3) :
    (pulledAlpha T d x).2 = flipSlot x.2 := by
  exact flipSlot_characterization x.2 (pulledAlpha T d x).2
    (pulled_mark T d x) (pulled_next_mark T d x)

def alphaFun (v : W) : W := (pulledAlpha T d (v, 0)).1
def phiFun (v : W) : W := (pulledAlpha T d (v, 1)).1
def phiInvFun (v : W) : W := (pulledAlpha T d (v, 2)).1

theorem pulled_zero (v : W) : pulledAlpha T d (v, 0) = (alphaFun T d v, 0) :=
  Prod.ext rfl (by simpa [flipSlot] using pulled_slot T d (v, 0))

theorem pulled_one (v : W) : pulledAlpha T d (v, 1) = (phiFun T d v, 2) :=
  Prod.ext rfl (by simpa [flipSlot] using pulled_slot T d (v, 1))

theorem pulled_two (v : W) : pulledAlpha T d (v, 2) = (phiInvFun T d v, 1) :=
  Prod.ext rfl (by simpa [flipSlot] using pulled_slot T d (v, 2))

theorem alphaFun_involutive (v : W) : alphaFun T d (alphaFun T d v) = v := by
  have h := pulledAlpha_involutive T d (v, 0)
  rw [pulled_zero, pulled_zero] at h
  exact congrArg Prod.fst h

theorem phi_left_inv (v : W) : phiInvFun T d (phiFun T d v) = v := by
  have h := pulledAlpha_involutive T d (v, 1)
  rw [pulled_one, pulled_two] at h
  exact congrArg Prod.fst h

theorem phi_right_inv (v : W) : phiFun T d (phiInvFun T d v) = v := by
  have h := pulledAlpha_involutive T d (v, 2)
  rw [pulled_two, pulled_one] at h
  exact congrArg Prod.fst h

def sourceAlpha : Equiv.Perm W where
  toFun := alphaFun T d
  invFun := alphaFun T d
  left_inv := alphaFun_involutive T d
  right_inv := alphaFun_involutive T d

def sourcePhi : Equiv.Perm W where
  toFun := phiFun T d
  invFun := phiInvFun T d
  left_inv := phi_left_inv T d
  right_inv := phi_right_inv T d

def sourceRho : Equiv.Perm W := sourcePhi T d * sourceAlpha T d

@[simp] theorem sourceAlpha_involutive (v : W) :
    sourceAlpha T d (sourceAlpha T d v) = v := alphaFun_involutive T d v

theorem sourceAlpha_fixfree (v : W) : sourceAlpha T d v ≠ v := by
  intro h
  apply T.alpha_fixfree (d.frame.dart (v, 0))
  have he := pulledAlpha_map T d (v, 0)
  rw [pulled_zero] at he
  change d.frame.dart (sourceAlpha T d v, 0) = _ at he
  simpa only [h] using he.symm

theorem phi_zero (v : W) :
    T.phi (d.frame.dart (v, 0)) = d.frame.dart (sourceAlpha T d v, 1) := by
  rw [phi_frame, pulled_zero]
  rfl

theorem phi_one (v : W) :
    T.phi (d.frame.dart (v, 1)) = d.frame.dart (sourcePhi T d v, 0) := by
  rw [phi_frame, pulled_one]
  rfl

theorem phi_sq_zero (v : W) :
    (T.phi ^ 2) (d.frame.dart (v, 0)) = d.frame.dart (sourceRho T d v, 0) := by
  rw [pow_two, Equiv.Perm.mul_apply, phi_zero, phi_one]
  rfl

theorem pow_zero (n : ℕ) (v : W) :
    (T.phi ^ (2 * n)) (d.frame.dart (v, 0)) =
      d.frame.dart ((sourceRho T d ^ n) v, 0) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, phi_sq_zero, ih,
      pow_succ, Equiv.Perm.mul_apply]

/-- Distinct target facial sides rule out loops in the recovered source. -/
theorem source_loopless (htwo : OrbitFacesTwoSided T) (v : W) :
    ¬(sourceRho T d).SameCycle v (sourceAlpha T d v) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have htarget : T.phi.SameCycle (d.frame.dart (v, 0))
      (d.frame.dart (sourceAlpha T d v, 0)) := by
    refine ⟨(2 * n : ℕ), ?_⟩
    rw [zpow_natCast, pow_zero, hn]
  have he := pulledAlpha_map T d (v, 0)
  rw [pulled_zero] at he
  change d.frame.dart (sourceAlpha T d v, 0) = T.alpha (d.frame.dart (v, 0)) at he
  rw [he] at htarget
  exact htwo (d.frame.dart (v, 0)) (Quotient.sound htarget)

abbrev SourceVertex := Quotient (Equiv.Perm.SameCycle.setoid (sourceRho T d))
abbrev SourceEdge := Quotient (Equiv.Perm.SameCycle.setoid (sourceAlpha T d))

theorem sourceAlpha_sameCycle_iff (v w : W) :
    (sourceAlpha T d).SameCycle v w ↔ w = v ∨ w = sourceAlpha T d v := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp : ∀ n : ℕ, (sourceAlpha T d ^ n) v = v ∨
        (sourceAlpha T d ^ n) v = sourceAlpha T d v := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · exact Or.inr (congrArg (sourceAlpha T d) h)
        · exact Or.inl ((congrArg (sourceAlpha T d) h).trans
            (sourceAlpha_involutive T d v))
    simpa only [hn] using hp n
  · rintro (rfl | rfl)
    · exact .refl _ _
    · exact ⟨1, by simp⟩

/-- The source is constructed from actual target permutations and their
orbits. No source graph or source colouring is supplied. -/
abbrev source (htwo : OrbitFacesTwoSided T) :
    RotationSystem.{u,u,u} (SourceVertex T d) (SourceEdge T d) where
  D := W
  edgeOf := Quotient.mk _
  vertOf := Quotient.mk _
  alpha := sourceAlpha T d
  rho := sourceRho T d
  alpha_involutive := alphaFun_involutive T d
  alpha_fixfree := sourceAlpha_fixfree T d
  edge_alpha v := Quotient.sound (Mettapedia.GraphTheory.EquivPermSameCycle.step_right _ v).symm
  edge_fiber_two := by
    intro edge
    obtain ⟨v, rfl⟩ := Quotient.exists_rep edge
    have he : (Finset.univ.filter fun w =>
        Quotient.mk (Equiv.Perm.SameCycle.setoid (sourceAlpha T d)) w =
          Quotient.mk (Equiv.Perm.SameCycle.setoid (sourceAlpha T d)) v) =
        {v, sourceAlpha T d v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq,
        Finset.mem_insert, Finset.mem_singleton]
      change (sourceAlpha T d).SameCycle w v ↔ w = v ∨ w = sourceAlpha T d v
      rw [Equiv.Perm.sameCycle_comm, sourceAlpha_sameCycle_iff]
    rw [he]
    simp [(sourceAlpha_fixfree T d v).symm]
  vert_rho v := Quotient.sound (Mettapedia.GraphTheory.EquivPermSameCycle.step_right _ v).symm
  outer := T.vertOf T.outer
  no_self_loops v h := source_loopless T d htwo v (Quotient.exact h)

theorem source_rotationCyclic (htwo : OrbitFacesTwoSided T) :
    VertexRotationCyclic (source T d htwo) := by
  intro v w h
  exact Quotient.exact h

theorem source_phi (htwo : OrbitFacesTwoSided T) :
    (source T d htwo).phi = sourcePhi T d := by
  apply Equiv.ext
  intro v
  change sourcePhi T d (sourceAlpha T d (sourceAlpha T d v)) = sourcePhi T d v
  rw [sourceAlpha_involutive]

theorem adapter_alpha (htwo : OrbitFacesTwoSided T)
    (x : (DualTruncateColoring.rotation (source T d htwo)).D) :
    d.frame.dart ((DualTruncateColoring.rotation (source T d htwo)).alpha x) =
      T.alpha (d.frame.dart x) := by
  rcases x with ⟨v, i⟩
  fin_cases i
  · have hm := pulledAlpha_map T d (v, 0)
    rw [pulled_zero] at hm
    exact hm
  · have hm := pulledAlpha_map T d (v, 1)
    rw [pulled_one] at hm
    change d.frame.dart ((source T d htwo).phi v, 2) = _
    rw [source_phi]
    exact hm
  · have hm := pulledAlpha_map T d (v, 2)
    rw [pulled_two] at hm
    change d.frame.dart ((source T d htwo).phi.symm v, 1) = _
    rw [source_phi]
    exact hm

theorem adapter_vertex (htwo : OrbitFacesTwoSided T)
    (x : (DualTruncateColoring.rotation (source T d htwo)).D) :
    (DualTruncateColoring.rotation (source T d htwo)).vertOf x = T.vertOf (d.frame.dart x) :=
  (d.frame.vertex x).symm

theorem adapter_rho (htwo : OrbitFacesTwoSided T)
    (x : (DualTruncateColoring.rotation (source T d htwo)).D) :
    d.frame.dart ((DualTruncateColoring.rotation (source T d htwo)).rho x) =
      T.rho (d.frame.dart x) := (d.frame.turn x).symm

end
end Mettapedia.GraphTheory.FourColor.DualTruncateInverse
