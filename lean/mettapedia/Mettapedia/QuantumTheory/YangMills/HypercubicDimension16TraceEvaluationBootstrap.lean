import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTracePublicConditioning
import Mettapedia.QuantumTheory.YangMills.WilsonExtractionRecombinationConstant

/-!
# Conditional bootstrap arithmetic in the exact trace-evaluation norm

The genuine Reynolds evaluation matrix is the stored unsigned matrix divided
by `24`.  Its explicit dual therefore has sharp row-`l1` constant
`14739388451343 / 30664304`.  If the fluctuation, cumulant, and recombination
factors of the previously isolated Appendix-O ledger hold unchanged in this
evaluation-sup norm, the factor-one ledger is multiplied by this exact
analysis cost.  This file records only that conditional norm conversion and
its resulting depth arithmetic.

The calculation concerns the derivative-free eight-field trace sector.  It
does not supply estimates for derivative-coupled sectors or for the Wilson RG
map.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceEvaluationBootstrap

open HypercubicDimension16PhysicalTracePublicConditioning

/-- Proposed Appendix-O ledger after converting from the coefficient norm to
the explicit trace-evaluation sup norm. -/
def traceEvaluationConditionedLedgerConstant : ℝ :=
  proposedMajorantLedgerConstant *
    (publicEvaluationConditioningConstant : ℝ)

theorem traceEvaluationConditionedLedgerConstant_eq :
    traceEvaluationConditionedLedgerConstant =
      (928581472434609 : ℝ) / 1742290 := by
  norm_num [traceEvaluationConditionedLedgerConstant,
    proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    publicEvaluationConditioningConstant]

theorem traceEvaluationConditioned_rgGain_two_thirtyOne_eq :
    rgGain traceEvaluationConditionedLedgerConstant 2 31 =
      (928581472434609 : ℝ) / 467692410634240 := by
  norm_num [rgGain, traceEvaluationConditionedLedgerConstant,
    proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    publicEvaluationConditioningConstant, irrelevantScale]

theorem traceEvaluationConditioned_rgGain_two_thirtyTwo_eq :
    rgGain traceEvaluationConditionedLedgerConstant 2 32 =
      (928581472434609 : ℝ) / 935384821268480 := by
  norm_num [rgGain, traceEvaluationConditionedLedgerConstant,
    proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    publicEvaluationConditioningConstant, irrelevantScale]

/-- Depth `32` is a linear contraction depth for the conditioned
ledger. -/
theorem traceEvaluationConditioned_contraction_two_thirtyTwo :
    HasExtendedExtractionContraction
      traceEvaluationConditionedLedgerConstant 2 32 := by
  refine ⟨?_, irrelevantScale_nonneg 2 32, ?_⟩
  · rw [traceEvaluationConditionedLedgerConstant_eq]
    positivity
  · change rgGain traceEvaluationConditionedLedgerConstant 2 32 < 1
    rw [traceEvaluationConditioned_rgGain_two_thirtyTwo_eq]
    norm_num

/-- No depth at most `31` is a linear contraction for the conditioned
ledger. -/
theorem not_traceEvaluationConditioned_contraction_of_depth_le_thirtyOne
    {depth : ℕ} (hdepth : depth ≤ 31) :
    ¬ HasExtendedExtractionContraction
      traceEvaluationConditionedLedgerConstant 2 depth := by
  intro hcontraction
  have hgain := hcontraction.2.2
  interval_cases depth <;>
    norm_num [rgGain, traceEvaluationConditionedLedgerConstant,
      proposedMajorantLedgerConstant,
      appendixOProposedConstantAtBlockTwo,
      publicEvaluationConditioningConstant, irrelevantScale] at hgain

/-- The least unrestricted linear contraction depth is exactly `32`. -/
theorem traceEvaluationConditioned_leastContractionDepth :
    HasExtendedExtractionContraction
        traceEvaluationConditionedLedgerConstant 2 32 ∧
      ∀ depth, depth ≤ 31 →
        ¬ HasExtendedExtractionContraction
          traceEvaluationConditionedLedgerConstant 2 depth :=
  ⟨traceEvaluationConditioned_contraction_two_thirtyTwo,
    fun _ hdepth =>
      not_traceEvaluationConditioned_contraction_of_depth_le_thirtyOne
        hdepth⟩

theorem traceEvaluationConditioned_rgGain_two_thirtyThree_eq :
    rgGain traceEvaluationConditionedLedgerConstant 2 33 =
      (928581472434609 : ℝ) / 1870769642536960 := by
  norm_num [rgGain, traceEvaluationConditionedLedgerConstant,
    proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    publicEvaluationConditioningConstant, irrelevantScale]

theorem traceEvaluationConditioned_rgGain_two_thirtyFour_eq :
    rgGain traceEvaluationConditionedLedgerConstant 2 34 =
      (928581472434609 : ℝ) / 3741539285073920 := by
  norm_num [rgGain, traceEvaluationConditionedLedgerConstant,
    proposedMajorantLedgerConstant,
    appendixOProposedConstantAtBlockTwo,
    publicEvaluationConditioningConstant, irrelevantScale]

/-- Depth `34` meets the stronger two-source `1/3` gain budget. -/
theorem traceEvaluationConditioned_twoSourceSlack_two_thirtyFour :
    HasTwoSourceBootstrapSlack
      traceEvaluationConditionedLedgerConstant 2 34 := by
  refine ⟨?_, ?_⟩
  · rw [traceEvaluationConditionedLedgerConstant_eq]
    positivity
  · rw [traceEvaluationConditioned_rgGain_two_thirtyFour_eq]
    norm_num

/-- No depth at most `33` meets the two-source budget for the conditioned
ledger. -/
theorem not_traceEvaluationConditioned_twoSourceSlack_of_depth_le_thirtyThree
    {depth : ℕ} (hdepth : depth ≤ 33) :
    ¬ HasTwoSourceBootstrapSlack
      traceEvaluationConditionedLedgerConstant 2 depth := by
  intro hslack
  have hgain := hslack.2
  interval_cases depth <;>
    norm_num [rgGain, traceEvaluationConditionedLedgerConstant,
      proposedMajorantLedgerConstant,
      appendixOProposedConstantAtBlockTwo,
      publicEvaluationConditioningConstant, irrelevantScale] at hgain

/-- The least unrestricted depth for the conditioned two-source ledger is
exactly `34`. -/
theorem traceEvaluationConditioned_leastTwoSourceDepth :
    HasTwoSourceBootstrapSlack
        traceEvaluationConditionedLedgerConstant 2 34 ∧
      ∀ depth, depth ≤ 33 →
        ¬ HasTwoSourceBootstrapSlack
          traceEvaluationConditionedLedgerConstant 2 depth :=
  ⟨traceEvaluationConditioned_twoSourceSlack_two_thirtyFour,
    fun _ hdepth =>
      not_traceEvaluationConditioned_twoSourceSlack_of_depth_le_thirtyThree
        hdepth⟩

end HypercubicDimension16TraceEvaluationBootstrap
end YangMills
end QuantumTheory
end Mettapedia
