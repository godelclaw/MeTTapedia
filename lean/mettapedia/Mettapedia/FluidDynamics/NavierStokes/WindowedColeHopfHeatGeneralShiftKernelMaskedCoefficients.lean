import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatGeneralShiftKernelCoefficientSums
import Mettapedia.FluidDynamics.NavierStokes.WindowedColeHopfHeatMaskedShiftKernelObstruction

/-!
# Masked Common-Shift Coefficient Identities

This module was split out of
`WindowedColeHopfHeatGeneralShiftKernelMaskedSpecialization.lean` to keep the
masked common-shift specialization organized by mathematical role.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section WindowedColeHopfHeatGeneralShiftKernelMaskedCoefficients

variable {ι X κ : Type*}
variable [Fintype ι] [Fintype κ] [AddMonoid X] [DecidableEq X]

theorem SeedLiveShiftKernel.seedCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedSeedCoeffSum
    (mask : κ → Bool) (s : X) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.seedCoeffSumAt
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) s =
      SeedLiveShiftKernel.maskedSeedCoeffSum seedCoeff := by
  unfold SeedLiveShiftKernel.seedCoeffSumAt
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedSeedCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

theorem SeedLiveShiftKernel.liveCoeffSumAt_zero_maskedAnchoredTranslationShiftKernel_eq_maskedLiveBaseCoeffSum
    (mask : κ → Bool) (s : X) (hs : s ≠ 0) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.liveCoeffSumAt
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) 0 =
      SeedLiveShiftKernel.maskedLiveBaseCoeffSum mask liveCoeff := by
  unfold SeedLiveShiftKernel.liveCoeffSumAt
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedLiveBaseCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hmask : mask i = true
  · simp [hmask, hs]
  · simp [hmask]

theorem SeedLiveShiftKernel.liveCoeffSumAt_maskedAnchoredTranslationShiftKernel_eq_maskedLiveShiftCoeffSum
    (mask : κ → Bool) (s : X) (hs : s ≠ 0) (seedCoeff liveCoeff : κ → ℝ) :
    SeedLiveShiftKernel.liveCoeffSumAt
        (SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
          (X := X) mask s seedCoeff liveCoeff) s =
      SeedLiveShiftKernel.maskedLiveShiftCoeffSum mask liveCoeff := by
  have hzero : ¬ (0 = s) := by
    intro h
    exact hs h.symm
  unfold SeedLiveShiftKernel.liveCoeffSumAt
    SeedLiveShiftKernel.maskedAnchoredTranslationShiftKernel
    SeedLiveShiftKernel.maskedLiveShiftCoeffSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hmask : mask i = true
  · simp [hmask]
  · simp [hmask, hzero]

end WindowedColeHopfHeatGeneralShiftKernelMaskedCoefficients

end NavierStokes
end FluidDynamics
end Mettapedia
