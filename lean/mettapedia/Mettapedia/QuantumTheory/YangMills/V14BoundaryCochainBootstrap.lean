import Mettapedia.QuantumTheory.YangMills.RGBootstrapSlack
import Mettapedia.QuantumTheory.YangMills.V14BoundaryCochainExtraction

/-!
# Conditional bootstrap arithmetic for the boundary-cochain repair

The derivative-aware cochain projection has certified extraction constant one
in its explicitly labeled coefficient `ℓ¹` norm.  This module feeds that
constant into the existing v14 factorization and scalar bootstrap arithmetic.

The fluctuation, cumulant, and recombination factors are left at the same
numerical boundaries used in v14: `33/20`, `3·2⁴ = 48`, and `14`.  Their
validity for the repaired coefficient norm is not proved here.  The transfer
theorem therefore takes their nonnegativity and upper bounds as explicit
hypotheses.  Under those inputs the exact product budget is `5544/5 = 1108.8`,
and the two-source bootstrap first closes at depth fifteen rather than sixteen.

Nothing in this module upgrades the remaining F.3 fluctuation/cumulant claims
or constructs the Wilson-RG map on the full boundary-cochain census.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14BoundaryCochainBootstrap

open V14BoundaryCochainComplex
open V14BoundaryCochainExtraction

/-! ## Exact factor budget -/

def unchangedFluctuationUpperBound : ℝ := 33 / 20

def unchangedCumulantUpperBoundAtTwo : ℝ := 48

def unchangedRecombinationUpperBound : ℝ := 14

def repairedExtractionUpperBound : ℝ :=
  repairedBoundaryCochainExtractionConstant

/-- Exact worst-case product before the manuscript's decimal rounding. -/
def repairedBoundaryCochainRecursionBudget : ℝ :=
  v14WilsonRecursionConstantBudget
    unchangedFluctuationUpperBound
    unchangedCumulantUpperBoundAtTwo
    unchangedRecombinationUpperBound
    repairedExtractionUpperBound

theorem repairedBoundaryCochainRecursionBudget_eq :
    repairedBoundaryCochainRecursionBudget = (5544 : ℝ) / 5 := by
  norm_num [repairedBoundaryCochainRecursionBudget,
    unchangedFluctuationUpperBound, unchangedCumulantUpperBoundAtTwo,
    unchangedRecombinationUpperBound, repairedExtractionUpperBound,
    repairedBoundaryCochainExtractionConstant,
    v14WilsonRecursionConstantBudget]

theorem repairedBoundaryCochainRecursionBudget_le_1112 :
    repairedBoundaryCochainRecursionBudget ≤ 1112 := by
  rw [repairedBoundaryCochainRecursionBudget_eq]
  norm_num

/-- **Factor transfer.**  If the actual repaired-norm fluctuation, cumulant,
and recombination constants obey the unchanged v14 bounds, multiplying them
by the constructed extraction constant one gives the exact repaired budget.
The three analytic inequalities are hypotheses, not consequences of the new
coordinate construction. -/
theorem actualFactors_le_repairedBoundaryCochainBudget
    {Cfluct Ccumulant Crecomb : ℝ}
    (hfluct0 : 0 ≤ Cfluct)
    (hcumulant0 : 0 ≤ Ccumulant)
    (hrecomb0 : 0 ≤ Crecomb)
    (hfluct : Cfluct ≤ unchangedFluctuationUpperBound)
    (hcumulant : Ccumulant ≤ unchangedCumulantUpperBoundAtTwo)
    (hrecomb : Crecomb ≤ unchangedRecombinationUpperBound) :
    v14WilsonRecursionConstantBudget Cfluct Ccumulant Crecomb
        repairedExtractionUpperBound ≤
      repairedBoundaryCochainRecursionBudget := by
  unfold v14WilsonRecursionConstantBudget
    repairedBoundaryCochainRecursionBudget
  have hextract : repairedExtractionUpperBound = 1 := by
    rfl
  rw [hextract]
  unfold v14WilsonRecursionConstantBudget
  norm_num only [mul_one]
  change Cfluct * Ccumulant * Crecomb ≤
    unchangedFluctuationUpperBound *
      unchangedCumulantUpperBoundAtTwo *
        unchangedRecombinationUpperBound
  have hpair : Cfluct * Ccumulant ≤
      unchangedFluctuationUpperBound * unchangedCumulantUpperBoundAtTwo :=
    mul_le_mul hfluct hcumulant hcumulant0 (by
      norm_num [unchangedFluctuationUpperBound])
  have hupperPair0 : 0 ≤
      unchangedFluctuationUpperBound * unchangedCumulantUpperBoundAtTwo :=
    mul_nonneg
      (by norm_num [unchangedFluctuationUpperBound])
      (by norm_num [unchangedCumulantUpperBoundAtTwo])
  calc
    Cfluct * Ccumulant * Crecomb ≤
        (unchangedFluctuationUpperBound *
          unchangedCumulantUpperBoundAtTwo) * Crecomb :=
      mul_le_mul_of_nonneg_right hpair hrecomb0
    _ ≤ (unchangedFluctuationUpperBound *
          unchangedCumulantUpperBoundAtTwo) *
          unchangedRecombinationUpperBound :=
      mul_le_mul_of_nonneg_left hrecomb hupperPair0

/-! ## Existing bootstrap arithmetic with the repaired constant -/

theorem rgGain_repairedBoundaryCochain_two_fifteen :
    rgGain repairedBoundaryCochainRecursionBudget 2 15 =
      (693 : ℝ) / 2560 := by
  rw [repairedBoundaryCochainRecursionBudget_eq]
  norm_num [rgGain, irrelevantScale]

theorem rgGain_repairedBoundaryCochain_two_fourteen :
    rgGain repairedBoundaryCochainRecursionBudget 2 14 =
      (693 : ℝ) / 1280 := by
  rw [repairedBoundaryCochainRecursionBudget_eq]
  norm_num [rgGain, irrelevantScale]

/-- The repaired factor budget closes the two-source scalar bootstrap at
canonical depth fifteen. -/
theorem repairedBoundaryCochain_twoSourceSlack_fifteen :
    HasTwoSourceBootstrapSlack
      repairedBoundaryCochainRecursionBudget 2 15 := by
  refine ⟨?_, ?_⟩
  · rw [repairedBoundaryCochainRecursionBudget_eq]
    norm_num
  · rw [rgGain_repairedBoundaryCochain_two_fifteen]
    norm_num

theorem not_repairedBoundaryCochain_twoSourceSlack_fourteen :
    ¬ HasTwoSourceBootstrapSlack
      repairedBoundaryCochainRecursionBudget 2 14 := by
  intro h
  have hgain := h.2
  rw [rgGain_repairedBoundaryCochain_two_fourteen] at hgain
  norm_num at hgain

/-- Depth fourteen and every shallower natural depth fail the same two-source
budget. -/
theorem not_repairedBoundaryCochain_twoSourceSlack_of_depth_le_fourteen
    {depth : ℕ} (hdepth : depth ≤ 14) :
    ¬ HasTwoSourceBootstrapSlack
      repairedBoundaryCochainRecursionBudget 2 depth := by
  intro h
  have hgain := h.2
  rw [repairedBoundaryCochainRecursionBudget_eq] at hgain
  interval_cases depth <;> norm_num [rgGain, irrelevantScale] at hgain

theorem leastDepth_repairedBoundaryCochain_packet :
    HasTwoSourceBootstrapSlack
        repairedBoundaryCochainRecursionBudget 2 15 ∧
      ∀ depth : ℕ, depth ≤ 14 →
        ¬ HasTwoSourceBootstrapSlack
          repairedBoundaryCochainRecursionBudget 2 depth := by
  exact ⟨repairedBoundaryCochain_twoSourceSlack_fifteen,
    fun _ hdepth =>
      not_repairedBoundaryCochain_twoSourceSlack_of_depth_le_fourteen hdepth⟩

def repairedBoundaryCochainEpsilonStar : ℝ :=
  twoSourceEpsilonStar repairedBoundaryCochainRecursionBudget
    (rgGain repairedBoundaryCochainRecursionBudget 2 15)

theorem repairedBoundaryCochainEpsilonStar_eq :
    repairedBoundaryCochainEpsilonStar = (1867 : ℝ) / 11354112 := by
  unfold repairedBoundaryCochainEpsilonStar twoSourceEpsilonStar
  rw [repairedBoundaryCochainRecursionBudget_eq]
  norm_num [rgGain, irrelevantScale]

theorem repairedBoundaryCochainEpsilonStar_pos :
    0 < repairedBoundaryCochainEpsilonStar := by
  rw [repairedBoundaryCochainEpsilonStar_eq]
  norm_num

/-- Conditional scalar closure using exactly the repaired factor budget.  The
recursion and both source bounds remain hypotheses because their derivation in
the repaired boundary norm is analytic work, not coordinate algebra. -/
theorem repairedBoundaryCochain_scalar_bootstrap_closure
    {x couplingSource tailSource : ℕ → ℝ} {horizon : ℕ}
    (hxnonneg : ∀ step, 0 ≤ x step)
    (hx0 : x 0 ≤ repairedBoundaryCochainEpsilonStar)
    (hcoupling : ∀ step, step < horizon →
      couplingSource step ≤ repairedBoundaryCochainEpsilonStar / 4)
    (htail : ∀ step, step < horizon →
      tailSource step ≤ repairedBoundaryCochainEpsilonStar / 4)
    (hrecursion : ∀ step, step < horizon →
      x (step + 1) ≤
        rgGain repairedBoundaryCochainRecursionBudget 2 15 * x step +
        repairedBoundaryCochainRecursionBudget * (x step) ^ 2 +
        couplingSource step + tailSource step) :
    ∀ step, step ≤ horizon → x step ≤ repairedBoundaryCochainEpsilonStar := by
  refine scalar_bootstrap_two_sources ?_ ?_ ?_
    (le_of_lt repairedBoundaryCochainEpsilonStar_pos) ?_
    hxnonneg hx0 hcoupling htail hrecursion
  · rw [rgGain_repairedBoundaryCochain_two_fifteen]
    norm_num
  · rw [rgGain_repairedBoundaryCochain_two_fifteen]
    norm_num
  · rw [repairedBoundaryCochainRecursionBudget_eq]
    norm_num
  · unfold repairedBoundaryCochainEpsilonStar
    exact (twoSourceEpsilonStar_quad_budget
      (C := repairedBoundaryCochainRecursionBudget)
      (a := rgGain repairedBoundaryCochainRecursionBudget 2 15) (by
        rw [repairedBoundaryCochainRecursionBudget_eq]
        norm_num)).le

/-! ## Honest transfer ledger -/

inductive BoundaryCochainRouteField where
  | exactTwoBlockComplex
  | globalH0CensusRecovery
  | move5DescendantCancellation
  | derivativeAwareFiltration
  | coordinateBasisAndDuals
  | repairedCoefficientNormConstant
  | fullDimensionSixteenCensus
  | wilsonAnalyticCoordinateTransfer
  | fluctuationBoundInRepairedNorm
  | cumulantBoundInRepairedNorm
  | wilsonRGIntertwining
  | conditionalBootstrapArithmetic
deriving DecidableEq, Fintype, Repr

inductive BoundaryCochainRouteStatus where
  | constructed
  | parametricUntilCensusEnumerated
  | sameTargetRefuted
  | openAnalyticTransfer
deriving DecidableEq, Repr

def boundaryCochainRouteStatus :
    BoundaryCochainRouteField → BoundaryCochainRouteStatus
  | .exactTwoBlockComplex => .constructed
  | .globalH0CensusRecovery => .constructed
  | .move5DescendantCancellation => .constructed
  | .derivativeAwareFiltration => .constructed
  | .coordinateBasisAndDuals => .constructed
  | .repairedCoefficientNormConstant => .constructed
  | .fullDimensionSixteenCensus => .sameTargetRefuted
  | .wilsonAnalyticCoordinateTransfer => .openAnalyticTransfer
  | .fluctuationBoundInRepairedNorm => .openAnalyticTransfer
  | .cumulantBoundInRepairedNorm => .openAnalyticTransfer
  | .wilsonRGIntertwining => .openAnalyticTransfer
  | .conditionalBootstrapArithmetic => .constructed

def boundaryCochainRouteMatrix :
    List (BoundaryCochainRouteField × BoundaryCochainRouteStatus) :=
  [ (.exactTwoBlockComplex, .constructed)
  , (.globalH0CensusRecovery, .constructed)
  , (.move5DescendantCancellation, .constructed)
  , (.derivativeAwareFiltration, .constructed)
  , (.coordinateBasisAndDuals, .constructed)
  , (.repairedCoefficientNormConstant, .constructed)
  , (.fullDimensionSixteenCensus, .sameTargetRefuted)
  , (.wilsonAnalyticCoordinateTransfer, .openAnalyticTransfer)
  , (.fluctuationBoundInRepairedNorm, .openAnalyticTransfer)
  , (.cumulantBoundInRepairedNorm, .openAnalyticTransfer)
  , (.wilsonRGIntertwining, .openAnalyticTransfer)
  , (.conditionalBootstrapArithmetic, .constructed)
  ]

theorem boundaryCochainRouteMatrix_agrees
    (field : BoundaryCochainRouteField) :
    (field, boundaryCochainRouteStatus field) ∈
      boundaryCochainRouteMatrix := by
  cases field <;> decide

/-- **YM MOVE 6 constructed packet.**  The postponed-IBP repair exists on the
exact two-block witness, has a derivative-aware constant-one coordinate
projection, and yields improved conditional bootstrap arithmetic.  The
headline deliberately does not assert the full Wilson analytic transfer or
RG intertwining rows recorded as open in `boundaryCochainRouteMatrix`. -/
theorem v14_postponedIBP_boundaryCochain_constructed_packet :
    (LinearMap.range
        (sharedBoundaryCoboundaryLinear ActionLaplacianCensus)).mkQ
      assembledActionLaplacianBulk = 0 ∧
    RepairedBoundaryCochainExtractionCertificate ∧
    repairedBoundaryCochainRecursionBudget = (5544 : ℝ) / 5 ∧
    HasTwoSourceBootstrapSlack
      repairedBoundaryCochainRecursionBudget 2 15 := by
  exact ⟨move5Witness_handled_by_postponedIBP.2.2,
    repairedBoundaryCochainExtractionCertificate,
    repairedBoundaryCochainRecursionBudget_eq,
    repairedBoundaryCochain_twoSourceSlack_fifteen⟩

end V14BoundaryCochainBootstrap
end YangMills
end QuantumTheory
end Mettapedia
