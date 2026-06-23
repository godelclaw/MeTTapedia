import Mettapedia.Computability.PNP.SideChannelResolutionObstruction
import Init.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# P vs NP crux: weighted advantage algebra

This module isolates the raw doubled-advantage definition and its exact
relationship with weighted correctness on the support.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

/-- Twice the success advantage over chance for a weighted classifier. -/
def doubledAdvantage
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  2 * weightedCorrectMass u y w h - weightedTotalMass w

/-- The total mass splits into correct and incorrect mass. -/
theorem weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedTotalMass w =
      weightedCorrectMass u y w h + weightedIncorrectMass u y w h := by
  classical
  unfold weightedTotalMass weightedCorrectMass weightedIncorrectMass
  simpa [incorrect_iff_not_correct] using
    (Fintype.sum_subtype_add_sum_subtype (Correct u y h) w).symm

/-- If every positive-weight point is classified correctly, the incorrect mass
vanishes. -/
theorem weightedIncorrectMass_eq_zero_of_supportwise_correct
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hcorrect : ∀ x, 0 < w x → Correct u y h x) :
    weightedIncorrectMass u y w h = 0 := by
  unfold weightedIncorrectMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxw : 0 < w x.1
  · exact False.elim (x.2 (hcorrect x.1 hxw))
  · exact Nat.eq_zero_of_not_pos hxw

/-- If every positive-weight point is classified correctly, then all supported
mass is correct mass. -/
theorem weightedCorrectMass_eq_weightedTotalMass_of_supportwise_correct
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hcorrect : ∀ x, 0 < w x → Correct u y h x) :
    weightedCorrectMass u y w h = weightedTotalMass w := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w h + weightedIncorrectMass u y w h :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w h
  have hzero :
      weightedIncorrectMass u y w h = 0 :=
    weightedIncorrectMass_eq_zero_of_supportwise_correct
      u y w h hcorrect
  omega

/-- Conversely, if the correct mass is the whole supported mass, then every
positive-weight point is classified correctly. -/
theorem supportwise_correct_of_weightedCorrectMass_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hperfect : weightedCorrectMass u y w h = weightedTotalMass w) :
    ∀ x, 0 < w x → Correct u y h x := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w h + weightedIncorrectMass u y w h :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w h
  have hzero : weightedIncorrectMass u y w h = 0 := by
    omega
  intro x hxw
  by_contra hbad
  let x' : {x : α // Incorrect u y h x} := ⟨x, hbad⟩
  have hle' :
      w x'.1 ≤ ∑ y : {x : α // Incorrect u y h x}, w y.1 := by
    exact
      Finset.single_le_sum
        (f := fun y : {x : α // Incorrect u y h x} => w y.1)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ x')
  have hle : w x ≤ weightedIncorrectMass u y w h := by
    simpa [weightedIncorrectMass, x'] using hle'
  rw [hzero] at hle
  omega

/-- Supportwise perfect correctness already forces the doubled advantage to be
the whole support mass. -/
theorem doubledAdvantage_eq_weightedTotalMass_of_supportwise_correct
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hcorrect : ∀ x, 0 < w x → Correct u y h x) :
    doubledAdvantage u y w h = weightedTotalMass w := by
  unfold doubledAdvantage
  rw [weightedCorrectMass_eq_weightedTotalMass_of_supportwise_correct
    u y w h hcorrect]
  omega

/-- The same exact doubled-advantage identity follows directly from exact total
correctness. -/
theorem doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hperfect : weightedCorrectMass u y w h = weightedTotalMass w) :
    doubledAdvantage u y w h = weightedTotalMass w := by
  unfold doubledAdvantage
  omega

/-- Spending the whole supported mass as doubled advantage already forces exact
supported correctness. -/
theorem weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hadv : doubledAdvantage u y w h = weightedTotalMass w) :
    weightedCorrectMass u y w h = weightedTotalMass w := by
  unfold doubledAdvantage at hadv
  omega

/-- Exact supported correctness is equivalent to spending the whole supported
mass as doubled advantage. -/
theorem weightedCorrectMass_eq_weightedTotalMass_iff_doubledAdvantage_eq_weightedTotalMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) :
    weightedCorrectMass u y w h = weightedTotalMass w ↔
      doubledAdvantage u y w h = weightedTotalMass w := by
  constructor
  · intro hperfect
    exact
      doubledAdvantage_eq_weightedTotalMass_of_weightedCorrectMass_eq_weightedTotalMass
        u y w h hperfect
  · intro hadv
    exact
      weightedCorrectMass_eq_weightedTotalMass_of_doubledAdvantage_eq_weightedTotalMass
        u y w h hadv

end

end Mettapedia.Computability.PNP
