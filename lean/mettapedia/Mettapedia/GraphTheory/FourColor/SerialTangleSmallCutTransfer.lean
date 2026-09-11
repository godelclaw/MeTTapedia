import Mettapedia.GraphTheory.FourColor.OpenTangleCutDartSum
import Mettapedia.GraphTheory.FourColor.BoundarySmallCutTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleCountSupport

/-!
# Small-cut transfer for the literal serial tangle

The same serial constructor used by the boundary-colouring composition
theorem has an exact structural-state update. The proof counts darts of
the actual edge involution; it does not replace the tangle by a simple
graph that might collapse parallel edges.
-/

namespace Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open BoundarySmallCutProfile BoundarySmallCutTransfer OpenTangleCutDartSum
open TwoSidedOpenTangleData
open GoertzelV24RotationSpliceConstructor

noncomputable section

variable {V W I J L P R : Type*}

/-- Forget only the distinction between left and right boundary darts. -/
def asOpen (T : TwoSidedOpenTangleData V I L R) : OpenTangleData V I (L ⊕ R) where
  interiorVert := T.interiorVert
  boundaryVert := Sum.elim T.leftVert T.rightVert
  interiorAlpha := T.interiorAlpha
  interiorAlpha_involutive := T.interiorAlpha_involutive
  interiorAlpha_fixfree := T.interiorAlpha_fixfree
  rho := T.rho
  vert_rho := by
    have h : openTangleVertOf T.interiorVert (Sum.elim T.leftVert T.rightVert) =
        twoSidedOpenTangleVertOf T.interiorVert T.leftVert T.rightVert := by
      funext d; rcases d with d | (d | d) <;> rfl
    intro d
    rw [h]
    exact T.vert_rho d
  interior_no_self_loops := T.interior_no_self_loops
  outer := T.outer

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype P] [DecidableEq P]
  (A : TwoSidedOpenTangleData V I L P) (B : TwoSidedOpenTangleData W J P R)

theorem cutSize_serial (s : V → Bool) (t : W → Bool) :
    cutSize (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P)))) (Sum.elim s t) =
      cutSize (sideMultigraph (asOpen A)) s + cutSize (sideMultigraph (asOpen B)) t +
        ∑ p, bit (s (A.rightVert p)) (t (B.leftVert p)) := by
  have h := twice_cutSize (asOpen (A.serialCompose B (Equiv.refl P))) (Sum.elim s t)
  conv at h =>
    rhs
    simp only [Fintype.sum_sum_type, asOpen, serialCompose, serialInteriorAlpha,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, serialOutputVertOf,
      MatchedSeam.seamSwap_left, MatchedSeam.seamSwap_right,
      Equiv.refl_symm, Equiv.refl_apply, Sum.elim_inl, Sum.elim_inr]
  have hA := twice_cutSize (asOpen A) s
  have hB := twice_cutSize (asOpen B) t
  conv at hA => rhs; dsimp [asOpen]
  conv at hB => rhs; dsimp [asOpen]
  have hs : (∑ p, bit (t (B.leftVert p)) (s (A.rightVert p))) =
      ∑ p, bit (s (A.rightVert p)) (t (B.leftVert p)) := by
    apply Finset.sum_congr rfl
    intro p _
    exact bit_symm _ _
  rw [hs] at h
  omega

theorem state_serial (s : V → Bool) (t : W → Bool) :
    state (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P))))
        (asOpen (A.serialCompose B (Equiv.refl P))).boundaryVert (Sum.elim s t) =
      composeState (state (sideMultigraph (asOpen A)) (asOpen A).boundaryVert s)
        (state (sideMultigraph (asOpen B)) (asOpen B).boundaryVert t) := by
  classical
  unfold state composeState
  congr 1
  · funext p; cases p <;> rfl
  · simp only [Sum.exists, Sum.elim_inl, Sum.elim_inr, Bool.decide_or]
  · simp only [Sum.exists, Sum.elim_inl, Sum.elim_inr, Bool.decide_or]
  · apply Fin.ext
    dsimp only
    rw [cutSize_serial]
    exact (cap_add _ _ _).symm

/-- Exact realized profiles for the constructor whose colour acceptance
is characterized by `serialCompose_acceptsBoundaryWords_iff`. -/
theorem profile_serial :
    profile (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P))))
        (asOpen (A.serialCompose B (Equiv.refl P))).boundaryVert =
      composeProfile (profile (sideMultigraph (asOpen A)) (asOpen A).boundaryVert)
        (profile (sideMultigraph (asOpen B)) (asOpen B).boundaryVert) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨state (sideMultigraph (asOpen A)) (asOpen A).boundaryVert (s ∘ Sum.inl),
      ⟨_, rfl⟩, state (sideMultigraph (asOpen B)) (asOpen B).boundaryVert (s ∘ Sum.inr),
      ⟨_, rfl⟩, ?_⟩
    rw [← state_serial]
    congr 1
    funext v; cases v <;> rfl
  · rintro ⟨a, ⟨s, rfl⟩, b, ⟨t, rfl⟩, rfl⟩
    exact ⟨Sum.elim s t, state_serial A B s t⟩

end
end Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer
