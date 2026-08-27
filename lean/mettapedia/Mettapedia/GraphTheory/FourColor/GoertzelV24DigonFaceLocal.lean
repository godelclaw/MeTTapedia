import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoDoorOrbit

/-!
# The local face calculation at a cubic digon

The topological-looking part of digon suppression reduces to one finite
orbit calculation.  Suppose the first face step crosses from one parallel
edge to the other.  At the opposite endpoint the next step either closes
the two-cycle or leaves through the third dart.  In the latter case, the
exterior facial walk can return through only one of two attachment darts.
Two-sidedness excludes the attachment edge through which it left, forcing
the walk to return through the other attachment.  The resulting face would
then contain both darts of the first parallel edge, contradicting
two-sidedness again.  Hence the second step must close the digon.

This file proves exactly that local statement.  It does not yet manufacture
the six named darts from a parallel pair in an arbitrary rotation system;
that representation adapter is kept separate from the orbit argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DigonFaceLocal

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TwoDoorOrbit

variable {D : Type*} [Fintype D]

/-- Two distinct quotient faces on the dart sides are equivalently a
prohibition on the two darts lying in one face-permutation orbit. -/
theorem not_sameCycle_of_dartOrbitFace_ne
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (dart : RS.D) :
    ¬ RS.phi.SameCycle dart (RS.alpha dart) := by
  intro hsame
  exact htwoSided dart (Quotient.sound hsame)

omit [Fintype D] in
/-- The local contradiction behind the exact digon face.

`q₁ → p₂` is the first step across the prospective digon.  The next step
either closes at `q₁` or exits through `qᵦ`.  The two-door conclusion says
that the exterior orbit from `qᵦ` contains `a'` or `b'`; two-sidedness of
the `b` attachment excludes `b'`.  Since `a' → p₁`, the non-closing branch
would put `q₁` and `p₁` on one face, contradicting two-sidedness of the first
parallel edge. -/
theorem second_step_closes_of_twoDoors
    (φ : Perm D) (p₁ p₂ q₁ qᵦ a' b' : D)
    (hfirst : φ q₁ = p₂)
    (hsecond : φ p₂ = q₁ ∨ φ p₂ = qᵦ)
    (hdoors : φ.SameCycle qᵦ a' ∨ φ.SameCycle qᵦ b')
    (hbTwoSided : ¬ φ.SameCycle qᵦ b')
    (haReturn : φ a' = p₁)
    (he₁TwoSided : ¬ φ.SameCycle q₁ p₁) :
    φ p₂ = q₁ := by
  rcases hsecond with hclose | hexit
  · exact hclose
  exfalso
  have hq₁p₂ : φ.SameCycle q₁ p₂ := by
    simpa [hfirst] using
      (sameCycle_apply_right.2 (SameCycle.refl φ q₁))
  have hp₂qᵦ : φ.SameCycle p₂ qᵦ := by
    simpa [hexit] using
      (sameCycle_apply_right.2 (SameCycle.refl φ p₂))
  have hqᵦa' : φ.SameCycle qᵦ a' := hdoors.resolve_right hbTwoSided
  have ha'p₁ : φ.SameCycle a' p₁ := by
    simpa [haReturn] using
      (sameCycle_apply_right.2 (SameCycle.refl φ a'))
  exact he₁TwoSided (((hq₁p₂.trans hp₂qᵦ).trans hqᵦa').trans ha'p₁)

/-- Version of `second_step_closes_of_twoDoors` in which the two-door
conclusion is derived from an explicit Boolean side invariant. -/
theorem second_step_closes_of_twoDoorSide
    (φ : Perm D) (side : D → Bool) (p₁ p₂ q₁ qᵦ a' b' : D)
    (hfirst : φ q₁ = p₂)
    (hsecond : φ p₂ = q₁ ∨ φ p₂ = qᵦ)
    (hstep : ∀ x, x ≠ a' → x ≠ b' →
      side x ≠ side qᵦ → side (φ x) = side x)
    (hcross : side (φ qᵦ) ≠ side qᵦ)
    (hbTwoSided : ¬ φ.SameCycle qᵦ b')
    (haReturn : φ a' = p₁)
    (he₁TwoSided : ¬ φ.SameCycle q₁ p₁) :
    φ p₂ = q₁ := by
  apply second_step_closes_of_twoDoors φ p₁ p₂ q₁ qᵦ a' b'
    hfirst hsecond
  · exact sameCycle_firstDoor_or_secondDoor φ side qᵦ a' b' hstep hcross
  · exact hbTwoSided
  · exact haReturn
  · exact he₁TwoSided

omit [Fintype D] in
/-- A literal two-cycle has no further points in its permutation orbit. -/
theorem sameCycle_iff_eq_or_eq_of_twoCycle
    (φ : Perm D) {left right point : D}
    (hleft : φ left = right) (hright : φ right = left) :
    φ.SameCycle left point ↔ point = left ∨ point = right := by
  have hinvLeft : φ.symm left = right := by
    rw [← hright, Equiv.symm_apply_apply]
  have hinvRight : φ.symm right = left := by
    rw [← hleft, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨power, rfl⟩
    exact zpow_induction_left (g := φ)
      (P := fun permutation =>
        permutation left = left ∨ permutation left = right)
      (Or.inl rfl)
      (fun permutation h => by
        rcases h with h | h
        · exact Or.inr (by simp [Perm.mul_apply, h, hleft])
        · exact Or.inl (by simp [Perm.mul_apply, h, hright]))
      (fun permutation h => by
        rcases h with h | h
        · exact Or.inr (by simp [Perm.mul_apply, h, hinvLeft])
        · exact Or.inl (by simp [Perm.mul_apply, h, hinvRight]))
      power
  · intro hpoint
    rcases hpoint with hpoint | hpoint
    · subst point
      exact SameCycle.refl φ left
    · subst point
      simpa [hleft] using
        (sameCycle_apply_right.2 (SameCycle.refl φ left))

omit [Fintype D] in
/-- Complete a three-cycle once its first step and its three-point carrier
are known.  This is the small permutation fact used to turn a cubic vertex
rotation into one of its two possible orientations. -/
theorem complete_threeCycle
    (σ : Perm D) (first second third : D)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsame : σ.SameCycle first third)
    (hcube : σ (σ (σ first)) = first)
    (hstep : σ first = second)
    (hcarrier : σ second = first ∨ σ second = second ∨ σ second = third) :
    σ second = third ∧ σ third = first := by
  have hsecond : σ second = third := by
    rcases hcarrier with hback | hfixed | hthird
    · exfalso
      have horbit :=
        (sameCycle_iff_eq_or_eq_of_twoCycle σ hstep hback).1 hsame
      exact horbit.elim hfirstThird.symm hsecondThird.symm
    · have hsame' : σ.SameCycle second first := by
        have hraw := sameCycle_apply_right.2 (SameCycle.refl σ first)
        have hfirstCycleSecond : σ.SameCycle first second := by
          simpa [hstep] using hraw
        exact hfirstCycleSecond.symm
      exact False.elim (hfirstSecond (hsame'.eq_of_left hfixed).symm)
    · exact hthird
  refine ⟨hsecond, ?_⟩
  simpa [hstep, hsecond] using hcube

/-- The side-invariant form packages both conclusions consumed by digon
suppression: the two local darts map to one another, and therefore their
face orbit contains exactly those two darts. -/
theorem exact_twoCycle_of_twoDoorSide
    (φ : Perm D) (side : D → Bool) (p₁ p₂ q₁ qᵦ a' b' : D)
    (hfirst : φ q₁ = p₂)
    (hsecond : φ p₂ = q₁ ∨ φ p₂ = qᵦ)
    (hstep : ∀ x, x ≠ a' → x ≠ b' →
      side x ≠ side qᵦ → side (φ x) = side x)
    (hcross : side (φ qᵦ) ≠ side qᵦ)
    (hbTwoSided : ¬ φ.SameCycle qᵦ b')
    (haReturn : φ a' = p₁)
    (he₁TwoSided : ¬ φ.SameCycle q₁ p₁) :
    φ q₁ = p₂ ∧ φ p₂ = q₁ ∧
      ∀ point, φ.SameCycle q₁ point ↔ point = q₁ ∨ point = p₂ := by
  have hclose := second_step_closes_of_twoDoorSide φ side
    p₁ p₂ q₁ qᵦ a' b' hfirst hsecond hstep hcross hbTwoSided
      haReturn he₁TwoSided
  exact ⟨hfirst, hclose,
    fun point => sameCycle_iff_eq_or_eq_of_twoCycle φ hfirst hclose⟩

end GoertzelV24DigonFaceLocal

end Mettapedia.GraphTheory.FourColor
