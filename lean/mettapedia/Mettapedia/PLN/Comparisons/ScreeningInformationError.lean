import Mettapedia.ProbabilityTheory.BooleanPairMass
import Mettapedia.PLN.Comparisons.ChainLoss
import Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning
import Mettapedia.InformationTheory.MarkovRecovery
import Mettapedia.InformationTheory.MarkovProjectionMarginals

/-!
# Conditional mutual information bounds PLN query error

The Markov projection retains the two adjacent pair laws and the source
marginal. Its actual divergence is conditional mutual information. Combining
that identity with conditional Pinsker bounds the error of the PLN query,
including empty internal branches. Logarithms use the natural-log convention.
-/

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.ProbabilityTheory.BooleanPairMass
open Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.Comparisons.ChainLoss

variable {Ω : Type*} [Fintype Ω]

namespace Mettapedia.PLN.Comparisons.ScreeningInformationError

/-- Conditional score in the original endpoint law. -/
noncomputable def queryValue (p : Prob Ω) (f h : Ω → Bool) : ℝ :=
  law2 p.1 f h (true, true) / pushforward p.1 f true

/-- Adjacent-pair readouts supplied to the existing deduction formula. -/
noncomputable def screenedValue (p : Prob Ω) (f g h : Ω → Bool) : ℝ :=
  plnDeductionStrength (queryValue p f g) (queryValue p g h)
    (pushforward p.1 g true) (pushforward p.1 h true)

/-- The ordinary deduction formula is the actual projected conditional on
every coherent finite model with a possible source. Neither internal branch
is required to have positive mass. -/
theorem projection_cond_eq_pln (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    markovProjectionAC p.1 f g h (true, true) / pushforward p.1 f true =
      screenedValue p f g h := by
  unfold screenedValue queryValue
  have splitAB := sum_law2_right p.1 f g true
  have splitBC := sum_law2_left p.1 g h true
  have splitB := sum_pushforward p.1 g
  rw [Fintype.sum_bool] at splitAB splitBC
  rw [Fintype.sum_bool, p.2.2] at splitB
  by_cases empty : pushforward p.1 g true = 0
  · have zeroAB : law2 p.1 f g (true, true) = 0 :=
      le_antisymm ((law2_le_pushforward_snd p.1 p.2.1 f g (true, true)).trans_eq empty)
        (pushforward_nonneg p.1 p.2.1 _ _)
    have zeroBC : law2 p.1 g h (true, true) = 0 :=
      le_antisymm ((law2_le_pushforward_fst p.1 p.2.1 g h (true, true)).trans_eq empty)
        (pushforward_nonneg p.1 p.2.1 _ _)
    have other : pushforward p.1 g false = 1 := by linarith
    have outsideAB : law2 p.1 f g (true, false) = pushforward p.1 f true := by linarith
    have outsideBC : law2 p.1 g h (false, true) = pushforward p.1 h true := by linarith
    rw [markovProjectionAC_bool_true_true, zeroAB, zeroBC, empty, other, outsideAB, outsideBC]
    simp [plnDeductionStrength, possible.ne']
  · by_cases emptyOther : pushforward p.1 g false = 0
    · have zeroOutside : law2 p.1 f g (true, false) = 0 :=
        le_antisymm ((law2_le_pushforward_snd p.1 p.2.1 f g (true, false)).trans_eq emptyOther)
          (pushforward_nonneg p.1 p.2.1 _ _)
      have inside : pushforward p.1 g true = 1 := by linarith
      have insideAB : law2 p.1 f g (true, true) = pushforward p.1 f true := by linarith
      rw [markovProjectionAC_bool_true_true, zeroOutside, emptyOther, inside, insideAB]
      simp [plnDeductionStrength, possible.ne']
    · exact markovProjectionAC_cond_eq_plnDeductionStrength p.1 p.2.2 f g h possible
        (lt_of_le_of_ne (pushforward_nonneg p.1 p.2.1 g true) (Ne.symm empty))
        (lt_of_le_of_ne (pushforward_nonneg p.1 p.2.1 g false) (Ne.symm emptyOther))

end Mettapedia.PLN.Comparisons.ScreeningInformationError

namespace Mettapedia.PLN.Comparisons.BalancedScreeningInformationError

open Mettapedia.PLN.Comparisons.ScreeningInformationError

/-- The complete source and projected pair laws retain both event marginals. -/
theorem projected_query_error_sq_le_balanced_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true *
      (queryValue p f h -
        markovProjectionAC p.1 f g h (true, true) / pushforward p.1 f true) ^ 2 ≤
      (1 - pushforward p.1 f true) * condMutualInfo p.1 f g h := by
  have bound := conditional_error_sq_le_balanced_kl (law2Prob p f h)
    (markovProjectionACProb p f g h) Prod.fst Prod.snd
    (by simpa only [law2Prob, mass_fst, sum_law2_right] using possible)
    (by simp only [law2Prob, markovProjectionACProb, mass_fst, sum_law2_right,
      sum_markovProjectionAC_right p.1 p.2.1])
    (by simp only [law2Prob, markovProjectionACProb, mass_snd, sum_law2_left,
      sum_markovProjectionAC_left p.1 p.2.1])
    (fun _ positive => markovProjectionAC_pos_of_law2_pos p.1 p.2.1 f g h positive)
  change 2 * mass (law2 p.1 f h) Prod.fst *
      (conditional (law2 p.1 f h) Prod.snd Prod.fst -
        conditional (markovProjectionAC p.1 f g h) Prod.snd Prod.fst) ^ 2 ≤
      (1 - mass (law2 p.1 f h) Prod.fst) *
        klSum (law2 p.1 f h) (markovProjectionAC p.1 f g h) at bound
  simp only [conditional_snd_fst, mass_fst, sum_law2_right p.1 f h true,
    sum_markovProjectionAC_right p.1 p.2.1 f g h true] at bound
  have complementNonneg : 0 ≤ 1 - pushforward p.1 f true := by
    have split := sum_pushforward p.1 f
    rw [Fintype.sum_bool, p.2.2] at split
    linarith [pushforward_nonneg p.1 p.2.1 f false]
  exact bound.trans (mul_le_mul_of_nonneg_left
    ((MarkovRecovery.endpoint_divergence_le_loss p f g h).trans_eq
      (MarkovRecovery.loss_eq_cmi p f g h)) complementNonneg)

theorem pln_query_error_sq_le_balanced_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true * (queryValue p f h - screenedValue p f g h) ^ 2 ≤
      (1 - pushforward p.1 f true) * condMutualInfo p.1 f g h := by
  simpa only [projection_cond_eq_pln p f g h possible] using
    projected_query_error_sq_le_balanced_cmi p f g h possible

/-- The complementary mass tightens the previous square-root certificate. -/
theorem pln_query_error_le_sqrt_balanced_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    |queryValue p f h - screenedValue p f g h| ≤
      Real.sqrt (((1 - pushforward p.1 f true) * condMutualInfo p.1 f g h) /
        (2 * pushforward p.1 f true)) := by
  have squared := pln_query_error_sq_le_balanced_cmi p f g h possible
  have positive : 0 < 2 * pushforward p.1 f true := mul_pos (by norm_num) possible
  exact Real.abs_le_sqrt ((le_div_iff₀ positive).mpr
    (by simpa only [mul_comm (2 * pushforward p.1 f true)] using squared))

end Mettapedia.PLN.Comparisons.BalancedScreeningInformationError

namespace Mettapedia.PLN.Comparisons.ScreeningInformationError

/-- The projected conditional error satisfies a query-level information
bound. Positive mass of the source is the only possibility premise. -/
theorem projected_query_error_sq_le_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true *
      (queryValue p f h -
        markovProjectionAC p.1 f g h (true, true) / pushforward p.1 f true) ^ 2 ≤
      condMutualInfo p.1 f g h := by
  exact (BalancedScreeningInformationError.projected_query_error_sq_le_balanced_cmi p f g h possible).trans
    (mul_le_of_le_one_left (condMutualInfo_nonneg p.1 p.2.1 f g h)
      (by linarith [pushforward_nonneg p.1 p.2.1 f true]))

/-- Squared error of the existing PLN formula is controlled by the finite
conditional-mutual-information sum. -/
theorem pln_query_error_sq_le_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true * (queryValue p f h - screenedValue p f g h) ^ 2 ≤
      condMutualInfo p.1 f g h := by
  simpa only [projection_cond_eq_pln p f g h possible] using
    projected_query_error_sq_le_cmi p f g h possible

/-- `|P(C|A) - PLN| ≤ sqrt(I(A;C|B)/(2 P(A)))`, in nats. -/
theorem pln_query_error_le_sqrt_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    |queryValue p f h - screenedValue p f g h| ≤
      Real.sqrt (condMutualInfo p.1 f g h / (2 * pushforward p.1 f true)) := by
  have squared := pln_query_error_sq_le_cmi p f g h possible
  have positive : 0 < 2 * pushforward p.1 f true := mul_pos (by norm_num) possible
  exact Real.abs_le_sqrt ((le_div_iff₀ positive).mpr
    (by simpa only [mul_comm (2 * pushforward p.1 f true)] using squared))

end Mettapedia.PLN.Comparisons.ScreeningInformationError
