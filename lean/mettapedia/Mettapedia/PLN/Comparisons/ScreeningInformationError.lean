import Mettapedia.ProbabilityTheory.BooleanPairMass
import Mettapedia.PLN.Comparisons.ChainLoss
import Mettapedia.ProbabilityTheory.BayesianInference.EventConditioning

/-!
# Conditional mutual information bounds PLN query error

The Markov projection retains the two adjacent pair laws and the source
marginal. Its actual divergence is conditional mutual information. Combining
that identity with conditional Pinsker bounds the error of the PLN query,
including empty internal branches. Logarithms use the natural-log convention.
-/

namespace Mettapedia.PLN.Comparisons.ScreeningInformationError

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.ProbabilityTheory.BooleanPairMass
open Mettapedia.ProbabilityTheory.BayesianInference.EventConditioning
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.Comparisons.ChainLoss

variable {Ω : Type*} [Fintype Ω]

/-- The ordinary deduction formula is the actual projected conditional on
every coherent finite model with a possible source. Neither internal branch
is required to have positive mass. -/
theorem projection_cond_eq_pln (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    markovProjectionAC p.1 f g h (true, true) / pushforward p.1 f true =
      plnDeductionStrength
        (law2 p.1 f g (true, true) / pushforward p.1 f true)
        (law2 p.1 g h (true, true) / pushforward p.1 g true)
        (pushforward p.1 g true) (pushforward p.1 h true) := by
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

/-- The projected conditional error satisfies a query-level information
bound. Positive mass of the source is the only possibility premise. -/
theorem projected_query_error_sq_le_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true *
      (law2 p.1 f h (true, true) / pushforward p.1 f true -
        markovProjectionAC p.1 f g h (true, true) / pushforward p.1 f true) ^ 2 ≤
      condMutualInfo p.1 f g h := by
  have sourcePossible : 0 < mass (law2Prob p f h).1 Prod.fst := by
    change 0 < mass (law2 p.1 f h) Prod.fst
    rw [mass_fst, sum_law2_right]
    exact possible
  have projectedPossible : 0 < mass (markovProjectionACProb p f g h).1 Prod.fst := by
    change 0 < mass (markovProjectionAC p.1 f g h) Prod.fst
    rw [mass_fst, sum_markovProjectionAC_right p.1 p.2.1 f g h true]
    exact possible
  have same : mass (law2Prob p f h).1 Prod.fst =
      mass (markovProjectionACProb p f g h).1 Prod.fst := by
    change mass (law2 p.1 f h) Prod.fst = mass (markovProjectionAC p.1 f g h) Prod.fst
    rw [mass_fst, mass_fst, sum_law2_right,
      sum_markovProjectionAC_right p.1 p.2.1 f g h true]
  have supported : ∀ world, 0 < (law2Prob p f h).1 world →
      0 < (markovProjectionACProb p f g h).1 world :=
    fun world positive => markovProjectionAC_pos_of_law2_pos p.1 p.2.1 f g h positive
  have bound := conditional_error_sq_le_kl (law2Prob p f h) (markovProjectionACProb p f g h)
    Prod.fst Prod.snd sourcePossible projectedPossible same supported
  change 2 * mass (law2 p.1 f h) Prod.fst *
      (conditional (law2 p.1 f h) Prod.snd Prod.fst -
        conditional (markovProjectionAC p.1 f g h) Prod.snd Prod.fst) ^ 2 ≤
      klSum (law2 p.1 f h) (markovProjectionAC p.1 f g h) at bound
  simp only [conditional_snd_fst, mass_fst, sum_law2_right p.1 f h true,
    sum_markovProjectionAC_right p.1 p.2.1 f g h true] at bound
  exact bound.trans (klSum_law2_markovProjectionAC_le_condMutualInfo p.1 p.2.1 f g h)

/-- Squared error of the existing PLN formula is controlled by the finite
conditional-mutual-information sum. -/
theorem pln_query_error_sq_le_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true *
      (law2 p.1 f h (true, true) / pushforward p.1 f true -
        plnDeductionStrength
          (law2 p.1 f g (true, true) / pushforward p.1 f true)
          (law2 p.1 g h (true, true) / pushforward p.1 g true)
          (pushforward p.1 g true) (pushforward p.1 h true)) ^ 2 ≤
      condMutualInfo p.1 f g h := by
  simpa only [projection_cond_eq_pln p f g h possible] using
    projected_query_error_sq_le_cmi p f g h possible

/-- `|P(C|A) - PLN| ≤ sqrt(I(A;C|B)/(2 P(A)))`, in nats. -/
theorem pln_query_error_le_sqrt_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    |law2 p.1 f h (true, true) / pushforward p.1 f true -
        plnDeductionStrength
          (law2 p.1 f g (true, true) / pushforward p.1 f true)
          (law2 p.1 g h (true, true) / pushforward p.1 g true)
          (pushforward p.1 g true) (pushforward p.1 h true)| ≤
      Real.sqrt (condMutualInfo p.1 f g h / (2 * pushforward p.1 f true)) := by
  have squared := pln_query_error_sq_le_cmi p f g h possible
  have positive : 0 < 2 * pushforward p.1 f true := mul_pos (by norm_num) possible
  rw [mul_comm (2 * pushforward p.1 f true)] at squared
  have divided := (le_div_iff₀ positive).mpr squared
  rw [← Real.sqrt_sq (abs_nonneg _)]
  apply Real.sqrt_le_sqrt
  simpa only [sq_abs] using divided

end Mettapedia.PLN.Comparisons.ScreeningInformationError
