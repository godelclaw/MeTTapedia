import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginMassSplits

/-!
# Weighted feature-fiber margin: balanced obstruction

Fiber-balanced visible surfaces force exact zero doubled advantage and make any positive margin expose a fiber imbalance.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α] [DecidableEq U] [Fintype U]

/-- If every visible fiber has balanced `true` and `false` weight, then every
classifier on those visible features has exactly the same correct and incorrect
mass. -/
theorem weightedCorrectMass_eq_weightedIncorrectMass_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    weightedCorrectMass u y w h = weightedIncorrectMass u y w h := by
  rw [weightedCorrectMass_eq_sum_predictedTrue_trueMass_add_sum_predictedFalse_falseMass,
    weightedIncorrectMass_eq_sum_predictedTrue_falseMass_add_sum_predictedFalse_trueMass]
  congr 1
  · exact Finset.sum_congr rfl (fun v _ => hbal v)
  · exact Finset.sum_congr rfl (fun v _ => (hbal v).symm)

/-- Under the same fiber-balance hypothesis, every classifier on those visible
features has exact half weighted accuracy. -/
theorem two_mul_weightedCorrectMass_eq_weightedTotalMass_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    2 * weightedCorrectMass u y w h = weightedTotalMass w := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w h + weightedIncorrectMass u y w h :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass u y w h
  have heq :
      weightedCorrectMass u y w h = weightedIncorrectMass u y w h :=
    weightedCorrectMass_eq_weightedIncorrectMass_of_weightedFeatureFiberBalanced
      u y w h hbal
  omega

/-- Therefore the doubled advantage of any classifier on a fiber-balanced
visible surface is exactly zero. -/
theorem doubledAdvantage_eq_zero_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    doubledAdvantage u y w h = 0 := by
  unfold doubledAdvantage
  rw [two_mul_weightedCorrectMass_eq_weightedTotalMass_of_weightedFeatureFiberBalanced
    u y w h hbal]
  omega

/-- Fiber-balanced visible surfaces cannot support any positive doubled
advantage. -/
theorem not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    ¬ 0 < doubledAdvantage u y w h := by
  rw [doubledAdvantage_eq_zero_of_weightedFeatureFiberBalanced u y w h hbal]
  simp

/-- The same fiber-balance hypothesis blocks every strict half-accuracy claim
on the visible surface. -/
theorem not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v) :
    ¬ weightedTotalMass w < 2 * weightedCorrectMass u y w h := by
  rw [two_mul_weightedCorrectMass_eq_weightedTotalMass_of_weightedFeatureFiberBalanced
    u y w h hbal]
  simp

/-- Any positive doubled advantage on a finite visible surface must be witnessed
by at least one visible fiber with unequal `true` and `false` weighted mass. -/
theorem exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hadv : 0 < doubledAdvantage u y w h) :
    ∃ v : U,
      weightedFeatureFiberTrueMass u y w v ≠
        weightedFeatureFiberFalseMass u y w v := by
  by_contra hno
  have hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v := by
    intro v
    by_contra hneq
    exact hno ⟨v, hneq⟩
  exact
    (not_pos_doubledAdvantage_of_weightedFeatureFiberBalanced
      u y w h hbal) hadv

/-- Likewise, any strict-half weighted success on a finite visible surface must
already exhibit a visible fiber with unequal `true` and `false` weighted mass. -/
theorem exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool)
    (hadv : weightedTotalMass w < 2 * weightedCorrectMass u y w h) :
    ∃ v : U,
      weightedFeatureFiberTrueMass u y w v ≠
        weightedFeatureFiberFalseMass u y w v := by
  by_contra hno
  have hbal :
      ∀ v : U,
        weightedFeatureFiberTrueMass u y w v =
          weightedFeatureFiberFalseMass u y w v := by
    intro v
    by_contra hneq
    exact hno ⟨v, hneq⟩
  exact
    (not_total_lt_two_mul_weightedCorrectMass_of_weightedFeatureFiberBalanced
      u y w h hbal) hadv

end

end Mettapedia.Computability.PNP
