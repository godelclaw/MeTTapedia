import Mettapedia.Logic.TheoryModel.WeaknessMeasures
import Mettapedia.Enactive.GeneralizationOptimality

/-!
# Weakest correct is optimal, for any finite family of model classes

Michael Timothy Bennett's optimality theorem, stated for any candidates whose
model classes are finite sets of structures (`extension`).  An observation fixes the
structures already observed and the ones among them that must remain models; a
candidate is correct when its observed models are exactly those
(`Correct`).  Its unobserved models are its buffer (`buffer`), and for a
correct candidate the size of its model class is the admitted count plus the
size of its buffer (`card_eq_buffer_add`).

* **Uniform future** (Bennett 2023, Proposition 1): if every set of unobserved
  structures is equally likely to be required, a correct candidate's chance of
  admitting all of them is ordered exactly as the sizes of the model classes
  (`uniformFuture_le_iff`).
* **Exchangeable future** (Bennett, *The Wrong Razor*, Theorem A.12): if the
  number of required structures has any law and, given that number, every set of
  that size is equally likely, the chance of admitting them all is monotone in
  the size of the model class (`exchangeableSurvival_mono`).  The chance at a
  given size is the counted ratio of favourable draws (`survivalAt_eq_ratio`).
  Hence a weakest correct candidate is optimal (`weakestCorrect_optimal`), also
  against randomised selection (`randomised_le_weakest`).

For finite theories over a finite satisfaction relation the extension is the
model class and its size is Bennett's weakness (`theory_uniformFuture_le_iff`,
`theory_exchangeableSurvival_mono`).

Controls: under a law that requires nothing, every candidate survives
(`survival_pointMassZero`), so the exchangeable statement is monotone and not an
equivalence; and the statements compare correct candidates only.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.WeakestCorrect

open Finset
open Mettapedia.Enactive.GeneralizationOptimality
open Mettapedia.Logic.TheoryModel.WeaknessMeasures

universe uU uC uSent

section Extension

variable {U : Type uU} [Fintype U] [DecidableEq U] {Candidate : Type uC}

/-- An observation over finitely many structures: the structures already
observed, and those among them that must remain models. -/
structure Observation (U : Type uU) where
  seen : Finset U
  admitted : Finset U
  admitted_subset : admitted ⊆ seen

variable (extension : Candidate → Finset U)

/-- A candidate is correct for an observation when its models among the observed
structures are exactly the admitted ones. -/
def Correct (obs : Observation U) (candidate : Candidate) : Prop :=
  extension candidate ∩ obs.seen = obs.admitted

/-- The structures not yet observed. -/
def unseen (obs : Observation U) : Finset U :=
  univ \ obs.seen

/-- The unobserved models of a candidate. -/
def buffer (obs : Observation U) (candidate : Candidate) : Finset U :=
  extension candidate \ obs.seen

variable {extension}

theorem buffer_subset_unseen (obs : Observation U) (candidate : Candidate) :
    buffer extension obs candidate ⊆ unseen obs :=
  sdiff_subset_sdiff (subset_univ _) Subset.rfl

omit [Fintype U] in
/-- For a correct candidate, the size of its model class is the admitted count
plus the size of its buffer. -/
theorem card_eq_buffer_add {obs : Observation U} {candidate : Candidate}
    (correct : Correct extension obs candidate) :
    (extension candidate).card = (buffer extension obs candidate).card + obs.admitted.card := by
  rw [← correct]
  exact (card_sdiff_add_card_inter _ _).symm

omit [Fintype U] in
/-- Among correct candidates, comparing buffers is comparing model classes. -/
theorem buffer_card_le_iff {obs : Observation U} {left right : Candidate}
    (leftCorrect : Correct extension obs left) (rightCorrect : Correct extension obs right) :
    (buffer extension obs left).card ≤ (buffer extension obs right).card ↔
      (extension left).card ≤ (extension right).card := by
  rw [card_eq_buffer_add leftCorrect, card_eq_buffer_add rightCorrect, Nat.add_le_add_iff_right]

variable (extension)

/-- Bennett's uniform future: every set of unobserved structures is equally
likely to be required. -/
def uniformFuture (obs : Observation U) : UniformSubsetProblem Candidate U where
  domain := unseen obs
  coverage := buffer extension obs
  coverage_subset := buffer_subset_unseen obs

variable {extension}

/-- **Weakest correct is optimal under a uniform future**: the chance of
admitting every required structure is ordered exactly as the sizes of the model
classes. -/
theorem uniformFuture_le_iff {obs : Observation U} {left right : Candidate}
    (leftCorrect : Correct extension obs left) (rightCorrect : Correct extension obs right) :
    (uniformFuture extension obs).probability left ≤
        (uniformFuture extension obs).probability right ↔
      (extension left).card ≤ (extension right).card := by
  rw [UniformSubsetProblem.probability_le_iff_card_coverage_le]
  exact buffer_card_le_iff leftCorrect rightCorrect

variable (extension)

/-- The chance that `k` unobserved structures, drawn uniformly among the
`k`-element sets of unobserved structures, are all models of the candidate. -/
def survivalAt (obs : Observation U) (candidate : Candidate) (k : ℕ) : ℚ :=
  ((buffer extension obs candidate).card.choose k : ℚ) / ((unseen obs).card.choose k : ℚ)

variable {extension}

/-- The favourable draws are the `k`-element subsets of the buffer. -/
theorem filter_subset_buffer (obs : Observation U) (candidate : Candidate) (k : ℕ) :
    ((unseen obs).powersetCard k).filter (· ⊆ buffer extension obs candidate) =
      (buffer extension obs candidate).powersetCard k := by
  ext S
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨_, card⟩, inside⟩
    exact ⟨inside, card⟩
  · rintro ⟨inside, card⟩
    exact ⟨⟨inside.trans (buffer_subset_unseen obs candidate), card⟩, inside⟩

/-- `survivalAt` is the ratio of favourable draws to all draws. -/
theorem survivalAt_eq_ratio (obs : Observation U) (candidate : Candidate) (k : ℕ) :
    survivalAt extension obs candidate k =
      ((((unseen obs).powersetCard k).filter (· ⊆ buffer extension obs candidate)).card : ℚ) /
        (((unseen obs).powersetCard k).card : ℚ) := by
  rw [filter_subset_buffer, card_powersetCard, card_powersetCard]
  rfl

/-- Among correct candidates, survival at each size is monotone in the size of
the model class. -/
theorem survivalAt_mono {obs : Observation U} {left right : Candidate}
    (leftCorrect : Correct extension obs left) (rightCorrect : Correct extension obs right)
    (le : (extension left).card ≤ (extension right).card) (k : ℕ) :
    survivalAt extension obs left k ≤ survivalAt extension obs right k := by
  unfold survivalAt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.choose_le_choose k ((buffer_card_le_iff leftCorrect rightCorrect).mpr le)

variable (extension)

/-- Survival under an exchangeable future: `law k` is the probability that `k`
structures are required, and given `k` every `k`-element set of unobserved
structures is equally likely. -/
def exchangeableSurvival (law : ℕ → ℚ) (obs : Observation U) (candidate : Candidate) : ℚ :=
  ∑ k ∈ range ((unseen obs).card + 1), law k * survivalAt extension obs candidate k

variable {extension}

/-- **Weakest correct is optimal under every exchangeable future**: among
correct candidates, survival is monotone in the size of the model class. -/
theorem exchangeableSurvival_mono {law : ℕ → ℚ} (nonneg : ∀ k, 0 ≤ law k) {obs : Observation U}
    {left right : Candidate}
    (leftCorrect : Correct extension obs left) (rightCorrect : Correct extension obs right)
    (le : (extension left).card ≤ (extension right).card) :
    exchangeableSurvival extension law obs left ≤ exchangeableSurvival extension law obs right :=
  sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (survivalAt_mono leftCorrect rightCorrect le k) (nonneg k)

/-- A candidate whose model class is largest among the correct candidates of a
family survives at least as well as each of them. -/
theorem weakestCorrect_optimal {law : ℕ → ℚ} (nonneg : ∀ k, 0 ≤ law k) {obs : Observation U}
    {candidates : Finset Candidate} {best : Candidate}
    (bestCorrect : Correct extension obs best)
    (maximal : ∀ c ∈ candidates, Correct extension obs c →
      (extension c).card ≤ (extension best).card) :
    ∀ c ∈ candidates, Correct extension obs c →
      exchangeableSurvival extension law obs c ≤ exchangeableSurvival extension law obs best :=
  fun c member correct =>
    exchangeableSurvival_mono nonneg correct bestCorrect (maximal c member correct)

/-- **No randomised selection among correct candidates beats a weakest correct
one.** -/
theorem randomised_le_weakest {law : ℕ → ℚ} (nonneg : ∀ k, 0 ≤ law k) {obs : Observation U}
    {candidates : Finset Candidate} {best : Candidate}
    (bestCorrect : Correct extension obs best)
    (allCorrect : ∀ c ∈ candidates, Correct extension obs c)
    (maximal : ∀ c ∈ candidates, (extension c).card ≤ (extension best).card)
    (weight : Candidate → ℚ) (weightNonneg : ∀ c ∈ candidates, 0 ≤ weight c)
    (total : ∑ c ∈ candidates, weight c = 1) :
    ∑ c ∈ candidates, weight c * exchangeableSurvival extension law obs c ≤
      exchangeableSurvival extension law obs best := by
  calc ∑ c ∈ candidates, weight c * exchangeableSurvival extension law obs c
      ≤ ∑ c ∈ candidates, weight c * exchangeableSurvival extension law obs best :=
        sum_le_sum fun c member => mul_le_mul_of_nonneg_left
          (exchangeableSurvival_mono nonneg (allCorrect c member) bestCorrect (maximal c member))
          (weightNonneg c member)
    _ = exchangeableSurvival extension law obs best := by
        rw [← sum_mul, total, one_mul]

/-- Control: under a law that requires nothing, every candidate survives. -/
theorem survival_pointMassZero (obs : Observation U) (candidate : Candidate) :
    exchangeableSurvival extension (fun k => if k = 0 then 1 else 0) obs candidate = 1 := by
  unfold exchangeableSurvival
  rw [sum_eq_single 0]
  · simp [survivalAt]
  · intro k _ nonzero
    simp [nonzero]
  · intro notMember
    exact (notMember (mem_range.mpr (Nat.succ_pos _))).elim

end Extension

/-! ## Finite theories -/

section Theories

variable {U : Type uU} [Fintype U] [DecidableEq U] {Sent : Type uSent}
  {Sat : U → Sent → Prop} [∀ u φ, Decidable (Sat u φ)]

/-- **For finite theories, weakest correct is optimal under a uniform future**:
the order of survival is the order of Bennett weakness. -/
theorem theory_uniformFuture_le_iff {obs : Observation U} {T T' : Finset Sent}
    (correct : Correct (modelFinset Sat) obs T) (correct' : Correct (modelFinset Sat) obs T') :
    (uniformFuture (modelFinset Sat) obs).probability T ≤
        (uniformFuture (modelFinset Sat) obs).probability T' ↔
      theoryBennettWeakness Sat T ≤ theoryBennettWeakness Sat T' :=
  uniformFuture_le_iff correct correct'

/-- **For finite theories, survival under an exchangeable future is monotone in
Bennett weakness** among correct theories. -/
theorem theory_exchangeableSurvival_mono {law : ℕ → ℚ} (nonneg : ∀ k, 0 ≤ law k)
    {obs : Observation U} {T T' : Finset Sent}
    (correct : Correct (modelFinset Sat) obs T) (correct' : Correct (modelFinset Sat) obs T')
    (le : theoryBennettWeakness Sat T ≤ theoryBennettWeakness Sat T') :
    exchangeableSurvival (modelFinset Sat) law obs T ≤
      exchangeableSurvival (modelFinset Sat) law obs T' :=
  exchangeableSurvival_mono nonneg correct correct' le

end Theories

end Mettapedia.Logic.TheoryModel.WeakestCorrect
