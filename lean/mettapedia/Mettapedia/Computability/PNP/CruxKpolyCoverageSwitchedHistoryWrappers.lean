import Mettapedia.Computability.PNP.ActualSwitchedHistoryBitVecBudgetObstruction

/-!
# PNP `Kpoly` coverage anchors: switched-history wrappers

Actual switched-history exact-visible and clocked-wrapper full-width interval obstructions.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: on bit-valued latent data, once the visible width
is at least `2`, every actual switched-history exact-visible wrapper whose
budget stays at or below the manuscript's full-width linear threshold is
already impossible under true fielded switching and surjectivity of the actual
switched family. -/
theorem kpolyCoverage_anchor_not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
    {Ω : Type u} [Fintype Ω] {n k s : ℕ} {Index : Type v} {Block : Type w}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ ActualSwitchedLocalInterface.SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items :=
  ActualSwitchedLocalInterface.not_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := T) (s := s) (hist := hist) (items := items) hfield hsurj hs hwidth

/-- Route-coverage anchor: the same full-width interval obstruction holds for
the actual switched-history clocked finite-learning wrapper. -/
theorem kpolyCoverage_anchor_not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
    {Ω : Type u} [Fintype Ω] {n k s clock : ℕ} {Index : Type v} {Block : Type w}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ ActualSwitchedLocalInterface.SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items :=
  ActualSwitchedLocalInterface.not_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_surjective_predict_of_le_fullWidthBudget
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items)
      hfield hsurj hs hwidth

/-- Route-coverage anchor: equivalently, any such actual switched-history
exact-visible wrapper already forces non-surjectivity of the actual switched
family on the full bit-valued exact visible surface. -/
theorem kpolyCoverage_anchor_not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_le_fullWidthBudget
    {Ω : Type u} [Fintype Ω] {n k s : ℕ} {Index : Type v} {Block : Type w}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : ActualSwitchedLocalInterface.SwitchedHistoryExactVisibleCompressionWrapper Ω T s hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict :=
  ActualSwitchedLocalInterface.not_surjective_predict_of_switchedHistoryExactVisibleCompressionWrapper_of_true_fieldedSwitching_of_le_fullWidthBudget
      (T := T) (s := s) (hist := hist) (items := items) hwrap hfield hs hwidth

/-- Route-coverage anchor: and likewise for the actual switched-history
clocked finite-learning wrapper on the same full-width interval. -/
theorem kpolyCoverage_anchor_not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_le_fullWidthBudget
    {Ω : Type u} [Fintype Ω] {n k s clock : ℕ} {Index : Type v} {Block : Type w}
    {T : ActualSwitchedLocalInterface (BitVec n) k Index Block}
    {hist : List (FiniteEvent Ω)} {items : List (V13FieldedStep Ω)}
    (hwrap : ActualSwitchedLocalInterface.SwitchedHistoryClockedKpolyFiniteLearningWrapper Ω T s clock hist items)
    (hfield : V13FieldSwitchingInstantiatedFrom hist items)
    (hs : s ≤ n + 2 * k + 1)
    (hwidth : 2 ≤ n + 2 * k) :
    ¬ Function.Surjective T.predictorFamily.predict :=
  ActualSwitchedLocalInterface.not_surjective_predict_of_switchedHistoryClockedKpolyFiniteLearningWrapper_of_true_fieldedSwitching_of_le_fullWidthBudget
      (T := T) (s := s) (clock := clock) (hist := hist) (items := items)
      hwrap hfield hs hwidth


end Mettapedia.Computability.PNP
