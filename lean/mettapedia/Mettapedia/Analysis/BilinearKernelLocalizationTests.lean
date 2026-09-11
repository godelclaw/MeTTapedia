import Mettapedia.Analysis.BilinearKernelLocalization
import Mettapedia.Analysis.FiniteTorusSymbolKernel

/-! Regressions for weighted bilinear differences and finite-symbol support. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearKernelLocalizationTests

open BilinearKernelLocalization FiniteTorusSymbolKernel

example (B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (a b u v : ℂ) :
    (a * b) • B u v - B (a • u) (b • v) = 0 := by
  rw [smul_sub_apply_smul]
  simp

/-- Half-sized localized inputs leave three quarters of the original output. -/
example (B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (u v : ℂ) :
    (1 * 1 : ℂ) • B u v - B ((1 / 2 : ℂ) • u) ((1 / 2 : ℂ) • v) =
      (3 / 4 : ℂ) • B u v := by
  rw [smul_sub_apply_smul]
  norm_num

example (B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (a b c d v : ℂ) :
    (c * d) • B 0 v - B (a • 0) (b • v) = 0 := by simp

example : UnitAddTorus.mFourierCoeff
    (kernel ({0} : Finset (Fin 2 → ℤ)) (fun _ ↦ (2 : ℂ))) 0 = 2 := by
  rw [mFourierCoeff_kernel]
  simp

example (k l : Fin 2 → ℤ) (h : l ≠ k) :
    UnitAddTorus.mFourierCoeff (kernel {k} (fun _ ↦ (2 : ℂ))) l = 0 := by
  rw [mFourierCoeff_kernel, if_neg (by simpa using h)]

example (x : UnitAddTorus (Fin 2)) :
    kernel (∅ : Finset (Fin 2 → ℤ)) (fun _ ↦ (2 : ℂ)) x = 0 := by simp [kernel]

end Mettapedia.Analysis.BilinearKernelLocalizationTests

#print axioms Mettapedia.Analysis.BilinearKernelLocalization.smul_sub_apply_smul
#print axioms Mettapedia.Analysis.BilinearKernelLocalization.norm_smul_sub_apply_smul_le
#print axioms Mettapedia.Analysis.BilinearKernelLocalization.smul_integral_sub_integral_apply_smul
#print axioms Mettapedia.Analysis.BilinearKernelLocalization.norm_smul_integral_sub_integral_apply_smul_le
#print axioms Mettapedia.Analysis.FiniteTorusSymbolKernel.integral_mFourier
#print axioms Mettapedia.Analysis.FiniteTorusSymbolKernel.continuous_kernel
#print axioms Mettapedia.Analysis.FiniteTorusSymbolKernel.integrable_kernel
#print axioms Mettapedia.Analysis.FiniteTorusSymbolKernel.mFourierCoeff_kernel
#print axioms Mettapedia.Analysis.FiniteTorusSymbolKernel.norm_kernel_le
