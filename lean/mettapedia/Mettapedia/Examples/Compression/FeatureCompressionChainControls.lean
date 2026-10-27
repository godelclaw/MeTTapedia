import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionChain
import Mettapedia.Examples.Compression.FeatureCompressionRatioControls

/-!
# Genuine compression-chain controls

The ratio-two example performs two strict reconstruction/extraction steps and
ends with an empty residual. A separate unit-ratio machine removes one bit per
step for arbitrarily long chains, showing why the logarithmic bound requires
a factor strictly greater than one.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureCompressionChainControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open scoped Classical

def eight : BinString := List.replicate 8 true

def twoStage : ConditionalAlgorithm := fun program condition =>
  if program = [false] then
    if condition = [] then Part.some fourTrue
    else if condition = fourTrue then Part.some eight else Part.none
  else if program = [true] then
    if condition = eight then Part.some fourTrue
    else if condition = fourTrue then Part.some [] else Part.none
  else Part.none

theorem two_stage_chain : BChain twoStage 2 eight [[false], [false]] [] := by
  apply BChain.cons (descriptive := [true]) (residual := fourTrue)
  · simp [twoStage, eight, fourTrue]
  · simp [twoStage, eight, fourTrue]
  · simp [eight, fourTrue]
  · norm_num [eight, fourTrue]
  · apply BChain.cons (descriptive := [true]) (residual := [])
    · simp [twoStage, eight, fourTrue]
    · simp [twoStage, fourTrue]
    · simp [fourTrue]
    · norm_num [fourTrue]
    · exact .nil []

theorem final_empty_is_covered :
    (2 : ℝ) ≤ Real.log eight.length / Real.log 2 + 1 :=
  two_stage_chain.logarithmic_length (by norm_num) (by simp)

theorem positive_predecessor_bound : (2 : ℝ) ^ (2 - 1 : Nat) ≤ eight.length :=
  two_stage_chain.predecessor_geometric (by norm_num) (by simp)

def stripMachine : ConditionalAlgorithm := fun program condition =>
  if program = [] then Part.some (false :: condition)
  else if program = [true] then
    match condition with
    | [] => Part.none
    | _ :: tail => Part.some tail
  else Part.none

theorem unit_ratio_chain (count : Nat) :
    BChain stripMachine 1 (List.replicate count false) (List.replicate count []) [] := by
  induction count with
  | zero => exact .nil []
  | succ count ih =>
      apply BChain.cons (descriptive := [true]) (residual := List.replicate count false)
      · simp [stripMachine, List.replicate_succ]
      · simp [stripMachine, List.replicate_succ]
      · simp
      · simp
      · exact ih

/-- With unit ratio, the same logarithmic expression would claim that a
four-step compression has at most one step. -/
theorem factor_one_not_covered :
    BChain stripMachine 1 (List.replicate 4 false) (List.replicate 4 []) [] ∧
    ¬ ((4 : ℝ) ≤ Real.log (List.replicate 4 false).length / Real.log 1 + 1) := by
  exact ⟨unit_ratio_chain 4, by norm_num⟩

#print axioms two_stage_chain
#print axioms final_empty_is_covered
#print axioms unit_ratio_chain
#print axioms factor_one_not_covered

end Mettapedia.Examples.Compression.FeatureCompressionChainControls
