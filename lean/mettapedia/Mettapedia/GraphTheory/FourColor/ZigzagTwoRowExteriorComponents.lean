import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowWiringGeometry
import Mettapedia.GraphTheory.FourColor.OpenTangleFaceReturnConnectivity

/-!
# Boundary order recognizes the two exterior components

When all components meet ports, opposite cyclic returns connect every
port on each end. Labels constant on interior edges then distinguish
exactly two connected shores. No shore-connectivity field is supplied.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring.Geometry

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph BoundarySmallCutProfile
open BoundaryConnectivity OpenTanglePortReplacement OpenTangleFaceReturnConnectivity
open SmallCutConnectedBridgeless
open Fin.NatCast

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (k : ℕ) [NeZero k]
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin k ⊕ Fin k))

/-- Labels record separation; computed return and port visibility prove
connectivity within each label. -/
def twoShores_of_return (shore : V → Bool)
    (edge : ∀ e, shore ((sideMultigraph O).fst e) = shore ((sideMultigraph O).snd e))
    (left : ∀ i, shore (O.boundaryVert (.inl i)) = false)
    (right : ∀ i, shore (O.boundaryVert (.inr i)) = true)
    (visible : PortVisible (sideMultigraph O) O.boundaryVert)
    (hr : returnCode O = (boundaryPerm k)⁻¹) : TwoShores k O := by
  have hlstep (i : Fin k) : (sideMultigraph O).Reach
      (O.boundaryVert (.inl i)) (O.boundaryVert (.inl (i + 1))) := by
    have h := return_reach O (.inl (i + 1))
    rw [hr] at h
    change (sideMultigraph O).Reach (O.boundaryVert (.inl (i + 1)))
      (O.boundaryVert (.inl (i + 1 - 1))) at h
    rw [add_sub_cancel_right] at h
    exact reach_symm h
  have hrstep (i : Fin k) : (sideMultigraph O).Reach
      (O.boundaryVert (.inr i)) (O.boundaryVert (.inr (i + 1))) := by
    have h := return_reach O (.inr i)
    rw [hr] at h
    exact h
  have hl0 (n : ℕ) : (sideMultigraph O).Reach
      (O.boundaryVert (.inl 0)) (O.boundaryVert (.inl (n : Fin k))) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
      simpa only [Multigraph.Reach, Nat.cast_add, Nat.cast_one] using ih.trans (hlstep (n : Fin k))
  have hr0 (n : ℕ) : (sideMultigraph O).Reach
      (O.boundaryVert (.inr 0)) (O.boundaryVert (.inr (n : Fin k))) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
      simpa only [Multigraph.Reach, Nat.cast_add, Nat.cast_one] using ih.trans (hrstep (n : Fin k))
  have hl (i j : Fin k) : (sideMultigraph O).Reach
      (O.boundaryVert (.inl i)) (O.boundaryVert (.inl j)) := by
    simpa only [Multigraph.Reach, Fin.cast_val_eq_self] using (reach_symm (hl0 i.val)).trans (hl0 j.val)
  have hr' (i j : Fin k) : (sideMultigraph O).Reach
      (O.boundaryVert (.inr i)) (O.boundaryVert (.inr j)) := by
    simpa only [Multigraph.Reach, Fin.cast_val_eq_self] using (reach_symm (hr0 i.val)).trans (hr0 j.val)
  refine ⟨shore, edge, left, right, ?_⟩
  intro u v huv
  obtain ⟨b, hb⟩ := visible u
  obtain ⟨c, hc⟩ := visible v
  have hbu := constant_on_path (sideMultigraph O) shore (fun _ => False)
    (fun e _ => edge e) hb
  have hcv := constant_on_path (sideMultigraph O) shore (fun _ => False)
    (fun e _ => edge e) hc
  have hbc : shore (O.boundaryVert b) = shore (O.boundaryVert c) :=
    hbu.symm.trans (huv.trans hcv)
  have hp : (sideMultigraph O).Reach (O.boundaryVert b) (O.boundaryVert c) := by
    rcases b with i | i <;> rcases c with j | j
    · exact hl i j
    · rw [left, right] at hbc; cases hbc
    · rw [right, left] at hbc; cases hbc
    · exact hr' i j
  exact hb.trans (hp.trans (reach_symm hc))

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring.Geometry
