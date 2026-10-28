import Mettapedia.Computability.PNP.WeightedFeatureFiberMarginMajoritySums

/-!
# Weighted feature-fiber margin: majority criterion

Majority-classifier optimality and exact equivalence between positive visible margin and fiber imbalance.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α] [DecidableEq U] [Fintype U]

/-- The fiber-majority classifier never does worse than chance on a finite
visible surface. -/
theorem weightedIncorrectMass_le_weightedCorrectMass_of_weightedFeatureFiberMajorityClassifier
    (u : α → U) (y : α → Bool) (w : α → ℕ) :
    weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) ≤
      weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  classical
  rw [weightedIncorrectMass_eq_sum_if_weightedFeatureFiberMass,
    weightedCorrectMass_eq_sum_if_weightedFeatureFiberMass]
  refine Finset.sum_le_sum ?_
  intro v hv
  by_cases hlt :
      weightedFeatureFiberFalseMass u y w v <
        weightedFeatureFiberTrueMass u y w v
  · simp [weightedFeatureFiberMajorityClassifier, hlt, le_of_lt hlt]
  · have hle :
        weightedFeatureFiberTrueMass u y w v ≤
          weightedFeatureFiberFalseMass u y w v :=
      Nat.le_of_not_gt hlt
    simp [weightedFeatureFiberMajorityClassifier, hlt, hle]

/-- If some visible fiber carries unequal `true` and `false` mass, then the
fiber-majority classifier beats chance strictly. -/
theorem weightedIncorrectMass_lt_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ)
    (himb :
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v) :
    weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) <
      weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  classical
  rcases himb with ⟨v, hneq⟩
  rw [weightedIncorrectMass_eq_sum_if_weightedFeatureFiberMass,
    weightedCorrectMass_eq_sum_if_weightedFeatureFiberMass]
  have hle :
      ∀ z : U,
        (if weightedFeatureFiberMajorityClassifier u y w z = true
          then weightedFeatureFiberFalseMass u y w z
          else weightedFeatureFiberTrueMass u y w z)
          ≤
        (if weightedFeatureFiberMajorityClassifier u y w z = true
          then weightedFeatureFiberTrueMass u y w z
          else weightedFeatureFiberFalseMass u y w z) := by
    intro z
    by_cases hlt :
        weightedFeatureFiberFalseMass u y w z <
          weightedFeatureFiberTrueMass u y w z
    · simp [weightedFeatureFiberMajorityClassifier, hlt, le_of_lt hlt]
    · have hle :
          weightedFeatureFiberTrueMass u y w z ≤
            weightedFeatureFiberFalseMass u y w z :=
        Nat.le_of_not_gt hlt
      simp [weightedFeatureFiberMajorityClassifier, hlt, hle]
  have hstrict :
      (if weightedFeatureFiberMajorityClassifier u y w v = true
        then weightedFeatureFiberFalseMass u y w v
        else weightedFeatureFiberTrueMass u y w v)
        <
      (if weightedFeatureFiberMajorityClassifier u y w v = true
        then weightedFeatureFiberTrueMass u y w v
        else weightedFeatureFiberFalseMass u y w v) := by
    by_cases hlt :
        weightedFeatureFiberFalseMass u y w v <
          weightedFeatureFiberTrueMass u y w v
    · simp [weightedFeatureFiberMajorityClassifier, hlt]
    · have hlt' :
          weightedFeatureFiberTrueMass u y w v <
            weightedFeatureFiberFalseMass u y w v :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) hneq
      simp [weightedFeatureFiberMajorityClassifier, hlt, hlt']
  exact Finset.sum_lt_sum (fun z _ => hle z) ⟨v, Finset.mem_univ v, hstrict⟩

/-- Visible-fiber imbalance is already sufficient for a positive doubled
advantage: predict by weighted fiber-majority. -/
theorem pos_doubledAdvantage_of_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ)
    (himb :
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v) :
    0 < doubledAdvantage u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) +
          weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w (weightedFeatureFiberMajorityClassifier u y w)
  have hlt :
      weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) <
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedIncorrectMass_lt_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
      u y w himb
  unfold doubledAdvantage
  omega

/-- The same majority classifier then beats strict half weighted accuracy. -/
theorem total_lt_two_mul_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ)
    (himb :
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v) :
    weightedTotalMass w <
      2 * weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) := by
  have hsplit :
      weightedTotalMass w =
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) +
          weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedTotalMass_eq_weightedCorrectMass_add_weightedIncorrectMass
      u y w (weightedFeatureFiberMajorityClassifier u y w)
  have hlt :
      weightedIncorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) <
        weightedCorrectMass u y w (weightedFeatureFiberMajorityClassifier u y w) :=
    weightedIncorrectMass_lt_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
      u y w himb
  omega

/-- On a finite visible surface, positive doubled advantage exists exactly when
some visible fiber is weight-imbalanced. -/
theorem exists_pos_doubledAdvantage_iff_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ) :
    (∃ h : U → Bool, 0 < doubledAdvantage u y w h) ↔
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v := by
  constructor
  · rintro ⟨h, hadv⟩
    exact exists_weightedFeatureFiber_imbalance_of_pos_doubledAdvantage u y w h hadv
  · intro himb
    exact ⟨weightedFeatureFiberMajorityClassifier u y w,
      pos_doubledAdvantage_of_exists_weightedFeatureFiber_imbalance u y w himb⟩

/-- The strict-half weighted-success formulation has the same exact visible
fiber criterion. -/
theorem exists_total_lt_two_mul_weightedCorrectMass_iff_exists_weightedFeatureFiber_imbalance
    (u : α → U) (y : α → Bool) (w : α → ℕ) :
    (∃ h : U → Bool,
      weightedTotalMass w < 2 * weightedCorrectMass u y w h) ↔
      ∃ v : U,
        weightedFeatureFiberTrueMass u y w v ≠
          weightedFeatureFiberFalseMass u y w v := by
  constructor
  · rintro ⟨h, hadv⟩
    exact
      exists_weightedFeatureFiber_imbalance_of_total_lt_two_mul_weightedCorrectMass
        u y w h hadv
  · intro himb
    exact ⟨weightedFeatureFiberMajorityClassifier u y w,
      total_lt_two_mul_weightedCorrectMass_of_exists_weightedFeatureFiber_imbalance
        u y w himb⟩

end

end Mettapedia.Computability.PNP
