import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCycleBoundarySupport
import Mathlib.GroupTheory.Perm.Fin

/-!
# The boundary derivative of a coloured facial cycle

For a cyclically ordered sequence of nonzero Klein colours, the boundary word
of the corresponding one-port-per-vertex cycle is the discrete derivative

    b i = x i + x (i + 1).

This file proves the generic algebraic fact behind the facial-cycle support
count: two cycle colourings have the same derivative exactly up to one constant
Klein translation.  In particular, the derivative is injective at every
colouring which uses all three Tait colours.

The theorem is deliberately independent of planarity and of a particular
cycle length.  The separate six-port module remains the literal physical
bridge for the first checked instance.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialCycleBoundaryDerivative

open GoertzelV24RawNooseCountPumping

/-- A proper cyclic edge-colouring on 'n + 1' labelled positions. -/
structure ProperCycleEdgeColoring (n : ℕ) where
  edgeColor : Fin (n + 1) → TaitColor
  adjacent_ne : ∀ i, edgeColor i ≠ edgeColor (finRotate (n + 1) i)

@[ext]
theorem ProperCycleEdgeColoring.ext {n : ℕ}
    {x y : ProperCycleEdgeColoring n}
    (h : x.edgeColor = y.edgeColor) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The port word obtained by taking the Klein derivative around the cycle. -/
def boundaryDerivative {n : ℕ}
    (x : ProperCycleEdgeColoring n) : CutWord (Fin (n + 1)) :=
  fun i =>
    ⟨(x.edgeColor i).1 + (x.edgeColor (finRotate (n + 1) i)).1, by
      apply add_ne_zero_of_ne
      intro h
      exact x.adjacent_ne i (Subtype.ext h)⟩

/-- Cancellation in the exponent-two Klein colour group, written in the form
used by the derivative calculation. -/
theorem crossSum_eq_of_sum_eq {a b c d : Color} (h : a + b = c + d) :
    b + d = a + c := by
  calc
    b + d = (a + a) + (b + d) := by rw [color_add_self, zero_add]
    _ = (a + b) + (a + d) := by ac_rfl
    _ = (c + d) + (a + d) := by rw [h]
    _ = c + (a + (d + d)) := by ac_rfl
    _ = c + a := by rw [color_add_self, add_zero]
    _ = a + c := add_comm _ _

/-- Adding a colour twice cancels. -/
theorem add_self_add_eq (a b : Color) : a + (a + b) = b := by
  rw [← add_assoc, color_add_self, zero_add]

/-- Equality of boundary derivatives says that the translation difference is
preserved by one cyclic successor step. -/
theorem translationDifference_step {n : ℕ}
    {x y : ProperCycleEdgeColoring n}
    (hderivative : boundaryDerivative x = boundaryDerivative y)
    (i : Fin (n + 1)) :
    (x.edgeColor (finRotate (n + 1) i)).1 +
        (y.edgeColor (finRotate (n + 1) i)).1 =
      (x.edgeColor i).1 + (y.edgeColor i).1 := by
  have h := congrArg (fun word => (word i).1) hderivative
  change
    (x.edgeColor i).1 + (x.edgeColor (finRotate (n + 1) i)).1 =
      (y.edgeColor i).1 + (y.edgeColor (finRotate (n + 1) i)).1 at h
  exact crossSum_eq_of_sum_eq h

/-- **Derivative fibre theorem.**  Equal boundary derivatives differ by one
constant Klein translation at every cycle position. -/
theorem exists_translation_of_boundaryDerivative_eq {n : ℕ}
    {x y : ProperCycleEdgeColoring n}
    (hderivative : boundaryDerivative x = boundaryDerivative y) :
    ∃ c : Color, ∀ i,
      (y.edgeColor i).1 = (x.edgeColor i).1 + c := by
  let c : Color := (x.edgeColor 0).1 + (y.edgeColor 0).1
  refine ⟨c, ?_⟩
  intro i
  induction i using Fin.induction with
  | zero =>
      exact (add_self_add_eq _ _).symm
  | succ i ih =>
      have hstep := translationDifference_step hderivative i.castSucc
      have hrotate :
          finRotate (n + 1) i.castSucc = i.succ := by
        simpa using (finRotate_of_lt i.isLt)
      rw [hrotate] at hstep
      calc
        (y.edgeColor i.succ).1 =
            (x.edgeColor i.succ).1 +
              ((x.edgeColor i.succ).1 + (y.edgeColor i.succ).1) := by
                exact (add_self_add_eq _ _).symm
        _ = (x.edgeColor i.succ).1 +
              ((x.edgeColor i.castSucc).1 +
                (y.edgeColor i.castSucc).1) := by rw [hstep]
        _ = (x.edgeColor i.succ).1 + c := by
              rw [ih]
              rw [add_self_add_eq]

/-- Conversely, one constant Klein translation does not change the boundary
derivative. -/
theorem boundaryDerivative_eq_of_translation {n : ℕ}
    {x y : ProperCycleEdgeColoring n} {c : Color}
    (htranslation : ∀ i,
      (y.edgeColor i).1 = (x.edgeColor i).1 + c) :
    boundaryDerivative x = boundaryDerivative y := by
  funext i
  apply Subtype.ext
  change
    (x.edgeColor i).1 + (x.edgeColor (finRotate (n + 1) i)).1 =
      (y.edgeColor i).1 + (y.edgeColor (finRotate (n + 1) i)).1
  rw [htranslation i, htranslation (finRotate (n + 1) i)]
  calc
    (x.edgeColor i).1 + (x.edgeColor (finRotate (n + 1) i)).1 =
        (x.edgeColor i).1 + (x.edgeColor (finRotate (n + 1) i)).1 +
          (c + c) := by rw [color_add_self, add_zero]
    _ = ((x.edgeColor i).1 + c) +
          ((x.edgeColor (finRotate (n + 1) i)).1 + c) := by ac_rfl

/-- Two proper cycle colourings have the same boundary derivative exactly
when they differ by a constant Klein translation. -/
theorem boundaryDerivative_eq_iff_exists_translation {n : ℕ}
    {x y : ProperCycleEdgeColoring n} :
    boundaryDerivative x = boundaryDerivative y ↔
      ∃ c : Color, ∀ i,
        (y.edgeColor i).1 = (x.edgeColor i).1 + c := by
  constructor
  · exact exists_translation_of_boundaryDerivative_eq
  · rintro ⟨c, hc⟩
    exact boundaryDerivative_eq_of_translation hc

/-- A cyclic edge-colouring uses the full three-colour Tait alphabet. -/
def UsesAllTaitColors {n : ℕ} (x : ProperCycleEdgeColoring n) : Prop :=
  ∀ colour : TaitColor, ∃ i, x.edgeColor i = colour

/-- On a cycle colouring which uses all three nonzero colours, the boundary
derivative has a singleton fibre. -/
theorem eq_of_boundaryDerivative_eq_of_usesAll {n : ℕ}
    {x y : ProperCycleEdgeColoring n}
    (hfull : UsesAllTaitColors x)
    (hderivative : boundaryDerivative x = boundaryDerivative y) :
    x = y := by
  rcases exists_translation_of_boundaryDerivative_eq hderivative with ⟨c, hc⟩
  have hc0 : c = 0 := by
    by_contra hcne
    let colour : TaitColor := ⟨c, hcne⟩
    rcases hfull colour with ⟨i, hi⟩
    have hy := hc i
    have hxi : (x.edgeColor i).1 = c := congrArg Subtype.val hi
    rw [hxi] at hy
    have hy0 : (y.edgeColor i).1 = 0 := by
      simpa using hy
    exact (y.edgeColor i).2 hy0
  apply ProperCycleEdgeColoring.ext
  funext i
  apply Subtype.ext
  simpa [hc0] using (hc i).symm

/-- The universal numerical separation used by the facial-cycle obstruction:
for n at least four, even the smaller cycle-support formula exceeds the
largest possible colouring count of a connected smaller cubic tree tangle. -/
theorem treeColouringUpper_lt_cycleSupportLower {n : ℕ} (hn : 4 ≤ n) :
    3 * 2 ^ (n - 2) < 2 ^ n - 2 := by
  have hpowLower : 2 ^ 2 ≤ 2 ^ (n - 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hnSplit : n = (n - 2) + 2 := by omega
  rw [hnSplit, pow_add]
  norm_num at hpowLower ⊢
  omega

end GoertzelV24FacialCycleBoundaryDerivative

end Mettapedia.GraphTheory.FourColor
