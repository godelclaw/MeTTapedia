import Mettapedia.Computability.KolmogorovComplexity.Prefix
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Program weight and observable output mass

Each program contributes once. An output observer pools the weights of all
programs whose outputs it identifies. Only the total-mass bound requires
prefix-freeness; observation laws hold for every partial output map.
-/

set_option autoImplicit false

namespace KolmogorovComplexity

open scoped ENNReal BigOperators Classical

/-- Length weight of a binary program, in the extended nonnegative reals. -/
noncomputable def prefixProgramWeight (program : BinString) : ENNReal :=
  ENNReal.ofReal ((2 : Real) ^ (-(program.length : Int)))

/-- Weight of a set of programs. A prefix-free set has mass at most one. -/
noncomputable def prefixProgramMass (domain : Set BinString) : ENNReal :=
  ∑' program, if program ∈ domain then prefixProgramWeight program else 0

theorem prefixProgramMass_le_one (domain : Set BinString) (free : PrefixFree domain) :
    prefixProgramMass domain ≤ 1 := by
  unfold prefixProgramMass prefixProgramWeight
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun finite => ?_
  rw [← Finset.sum_filter]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => zpow_nonneg (by norm_num) _)]
  exact ENNReal.ofReal_le_one.mpr (kraft_inequality _ fun first firstMember second secondMember =>
    free first (Finset.mem_filter.mp firstMember).2 second (Finset.mem_filter.mp secondMember).2)

@[simp] theorem prefixProgramMass_finset (programs : Finset BinString) :
    prefixProgramMass (programs : Set BinString) = ∑ program ∈ programs, prefixProgramWeight program := by
  simpa only [prefixProgramMass, Set.indicator_apply, Finset.mem_coe] using
    (sum_eq_tsum_indicator prefixProgramWeight programs).symm

/-- Push program length weight forward along a partial output map. This is
a discrete output mass; it does not describe probabilities of future prefixes. -/
noncomputable def prefixOutputMass {Output : Type*}
    (compute : BinString → Option Output) (output : Output) : ENNReal :=
  ∑' program, if compute program = some output then prefixProgramWeight program else 0

/-- Weighted observations may be summed over outputs or over their source programs. -/
theorem prefixOutputMass_observe {Output : Type*} (compute : BinString → Option Output)
    (observe : Output → ENNReal) :
    (∑' output, observe output * prefixOutputMass compute output) =
      ∑' program, (compute program).elim 0 (fun output => observe output * prefixProgramWeight program) := by
  simp only [prefixOutputMass, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun program => by cases compute program <;> simp

/-- An observer pools exactly the output fibers it identifies. -/
theorem prefixOutputMass_map {Output Observed : Type*} (compute : BinString → Option Output)
    (observe : Output → Observed) (observed : Observed) :
    prefixOutputMass (fun program => (compute program).map observe) observed =
      ∑' output, if observe output = observed then prefixOutputMass compute output else 0 := by
  have law := prefixOutputMass_observe compute (fun output => if observe output = observed then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at law
  rw [law]
  unfold prefixOutputMass
  exact tsum_congr fun program => by cases computed : compute program <;> simp [computed]

/-- Successive output observations agree with their composite readout. -/
theorem prefixOutputMass_map_comp {Output Middle Observed : Type*}
    (compute : BinString → Option Output) (first : Output → Middle) (second : Middle → Observed)
    (observed : Observed) :
    prefixOutputMass (fun program => ((compute program).map first).map second) observed =
      ∑' output, if second (first output) = observed then prefixOutputMass compute output else 0 := by
  simpa only [Option.map_map, Function.comp_apply] using prefixOutputMass_map compute (second ∘ first) observed

/-- Each terminating program contributes to exactly one output. -/
theorem prefixOutputMass_total {Output : Type*} (compute : BinString → Option Output) :
    (∑' output, prefixOutputMass compute output) =
      prefixProgramMass {program | compute program ≠ none} := by
  simpa only [one_mul] using (prefixOutputMass_observe compute (fun _ => 1)).trans (by
    unfold prefixProgramMass
    apply tsum_congr
    intro program
    cases computed : compute program <;> simp [computed])

theorem prefixOutputMass_total_le_one {Output : Type*}
    (compute : BinString → Option Output)
    (free : PrefixFree {program | compute program ≠ none}) :
    (∑' output, prefixOutputMass compute output) ≤ 1 := by
  rw [prefixOutputMass_total]
  exact prefixProgramMass_le_one _ free

end KolmogorovComplexity
