import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BlockwisePancakeDecomposition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DyadicPancakeClosureRegression

/-!
# Blockwise pancake decomposition: regression checks

Theorem-level checks that the blockwise decomposition structure is
inhabited, the interface proposition is satisfiable, and the blockwise
sufficiency theorem recovers the scale-local strain budget end-to-end on
the rest instance.  These confirm the interface is non-vacuous and make no
claim beyond the instances they name.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace BlockwisePancakeDecompositionRegression

open DyadicPancakeClosureRegression

/-- The rest blockwise data: all blocks, envelopes, and gains vanish on the
rest relaxation data. -/
def restBlockwiseData : BlockwisePancakeDecompositionData restDyadicData where
  blockStretch := fun _ _ => 0
  blockStretch_nonneg := fun _ _ => le_refl 0
  blockStretch_hasSum := fun _ => by simp [restDyadicData]
  pressureEnvelope := fun _ _ => 0
  pressureEnvelope_nonneg := fun _ _ => le_refl 0
  selfDepletionEnvelope := fun _ _ => 0
  selfDepletionEnvelope_nonneg := fun _ _ => le_refl 0
  cascadeEnvelope := fun _ _ => 0
  cascadeEnvelope_nonneg := fun _ _ => le_refl 0
  gain := fun _ => 0
  gain_nonneg := fun _ => le_refl 0
  gainTotal := 0
  gain_hasSum := hasSum_zero
  budgetFn := fun _ => 0
  budgetFn_integrable := intervalIntegrable_const
  envelopes_hasSum := fun _ => by simp
  block_le := fun _ t _ => by simp [restDyadicData]

/-- The rest data satisfies the blockwise decomposition interface with
zero budget and zero total gain. -/
theorem restBlockwiseDecomposition :
    BlockwisePancakeDecomposition restDyadicData 0 0 := by
  refine ⟨restBlockwiseData, ?_, ?_⟩
  · simp [restBlockwiseData]
  · simp [restBlockwiseData]

/-- **Canary:** the blockwise sufficiency theorem applied to the rest
instance recovers the scale-local strain budget for the rest data. -/
theorem rest_strainBudget_of_blockwise :
    ScaleLocalPancakeStrainBudget restDyadicData 0 0 :=
  scaleLocalPancakeStrainBudget_of_blockwiseDecomposition restDyadicData
    restBlockwiseDecomposition

end BlockwisePancakeDecompositionRegression
end NavierStokes
end FluidDynamics
end Mettapedia
