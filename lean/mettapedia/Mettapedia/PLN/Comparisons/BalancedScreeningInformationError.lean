import Mettapedia.PLN.Comparisons.ScreeningInformationError
import Mettapedia.InformationTheory.MarkovProjectionMarginals
import Mettapedia.ProbabilityTheory.BooleanPairMass
import Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning

/-!
# A stronger information bound for PLN deduction

The Markov projection preserves both endpoint marginals. Conditional errors
inside and outside the source event therefore balance. Using both branches
improves the information bound by the complementary source mass:
`2 P(A) error² ≤ (1 - P(A)) I(A;C|B)`.

The conditioning event must be possible. Intermediate Boolean branches may be
empty, and the full-mass source case is included. Information is in nats.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Comparisons.BalancedScreeningInformationError

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability
open Mettapedia.ProbabilityTheory.BooleanPairMass
open Mettapedia.ProbabilityTheory.BayesianInference.BalancedEventConditioning
open Mettapedia.PLN.Comparisons.ScreeningInformationError
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

variable {Ω : Type*} [Fintype Ω]

/-- The complete source and projected pair laws retain both event marginals. -/
theorem projected_query_error_sq_le_balanced_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true *
      (law2 p.1 f h (true, true) / pushforward p.1 f true -
        markovProjectionAC p.1 f g h (true, true) / pushforward p.1 f true) ^ 2 ≤
      (1 - pushforward p.1 f true) * condMutualInfo p.1 f g h := by
  have sourcePossible : 0 < mass (law2Prob p f h).1 Prod.fst := by
    change 0 < mass (law2 p.1 f h) Prod.fst
    rw [mass_fst, sum_law2_right]
    exact possible
  have sameSource : mass (law2Prob p f h).1 Prod.fst =
      mass (markovProjectionACProb p f g h).1 Prod.fst := by
    change mass (law2 p.1 f h) Prod.fst = mass (markovProjectionAC p.1 f g h) Prod.fst
    rw [mass_fst, mass_fst, sum_law2_right,
      sum_markovProjectionAC_right p.1 p.2.1 f g h true]
  have sameTarget : mass (law2Prob p f h).1 Prod.snd =
      mass (markovProjectionACProb p f g h).1 Prod.snd := by
    change mass (law2 p.1 f h) Prod.snd = mass (markovProjectionAC p.1 f g h) Prod.snd
    rw [mass_snd, mass_snd, sum_law2_left,
      sum_markovProjectionAC_left p.1 p.2.1 f g h true]
  have supported : ∀ world, 0 < (law2Prob p f h).1 world →
      0 < (markovProjectionACProb p f g h).1 world :=
    fun world positive => markovProjectionAC_pos_of_law2_pos p.1 p.2.1 f g h positive
  have bound := conditional_error_sq_le_balanced_kl (law2Prob p f h)
    (markovProjectionACProb p f g h) Prod.fst Prod.snd sourcePossible sameSource sameTarget supported
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
    (klSum_law2_markovProjectionAC_le_condMutualInfo
      p.1 p.2.1 f g h) complementNonneg)

theorem pln_query_error_sq_le_balanced_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    2 * pushforward p.1 f true *
      (law2 p.1 f h (true, true) / pushforward p.1 f true -
        plnDeductionStrength
          (law2 p.1 f g (true, true) / pushforward p.1 f true)
          (law2 p.1 g h (true, true) / pushforward p.1 g true)
          (pushforward p.1 g true) (pushforward p.1 h true)) ^ 2 ≤
      (1 - pushforward p.1 f true) * condMutualInfo p.1 f g h := by
  simpa only [projection_cond_eq_pln p f g h possible] using
    projected_query_error_sq_le_balanced_cmi p f g h possible

/-- The complementary mass tightens the previous square-root certificate. -/
theorem pln_query_error_le_sqrt_balanced_cmi (p : Prob Ω) (f g h : Ω → Bool)
    (possible : 0 < pushforward p.1 f true) :
    |law2 p.1 f h (true, true) / pushforward p.1 f true -
        plnDeductionStrength
          (law2 p.1 f g (true, true) / pushforward p.1 f true)
          (law2 p.1 g h (true, true) / pushforward p.1 g true)
          (pushforward p.1 g true) (pushforward p.1 h true)| ≤
      Real.sqrt (((1 - pushforward p.1 f true) * condMutualInfo p.1 f g h) /
        (2 * pushforward p.1 f true)) := by
  have squared := pln_query_error_sq_le_balanced_cmi p f g h possible
  have positive : 0 < 2 * pushforward p.1 f true := mul_pos (by norm_num) possible
  have divided :
      (law2 p.1 f h (true, true) / pushforward p.1 f true -
        plnDeductionStrength
          (law2 p.1 f g (true, true) / pushforward p.1 f true)
          (law2 p.1 g h (true, true) / pushforward p.1 g true)
          (pushforward p.1 g true) (pushforward p.1 h true)) ^ 2 ≤
        ((1 - pushforward p.1 f true) * condMutualInfo p.1 f g h) /
          (2 * pushforward p.1 f true) := by
    apply (le_div_iff₀ positive).mpr
    nlinarith
  rw [← Real.sqrt_sq (abs_nonneg _)]
  exact Real.sqrt_le_sqrt (by simpa only [sq_abs] using divided)

end Mettapedia.PLN.Comparisons.BalancedScreeningInformationError
