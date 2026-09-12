import Mettapedia.Analysis.PeriodicRieszOperator
import Mettapedia.Analysis.UnitTorusFourierReal

/-!
# Fourier identification of the real even Riesz operator

Real-part extraction and reversal preserve each real even scalar multiplier.
The identities concern the constructed integrable kernels, not a replacement
Fourier polynomial or an assumed operator symbol.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszOperator

open MeasureTheory UnitTorusFourierReal UnitTorusLattice
open scoped RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def entryKernel (i j : Fin d) (N : ℕ) : Td → ℝ :=
  realEvenPart (PeriodicRieszKernel.kernel i j N)

theorem integrable_entryKernel (i j : Fin d) (N : ℕ) : Integrable (entryKernel i j N) :=
  integrable_realEvenPart _ (PeriodicRieszKernel.integrable_kernel i j N)

theorem mFourierCoeff_entryKernel (i j : Fin d) (N : ℕ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (entryKernel i j N x : ℂ)) k =
      ((AnnularRieszKernel.weight N (frequency k) * AnnularRieszKernel.rieszEntry i j (frequency k) : ℝ) : ℂ) := by
  apply mFourierCoeff_realEvenPart_of_coefficients _ (PeriodicRieszKernel.integrable_kernel i j N)
  · exact PeriodicRieszKernel.mFourierCoeff_kernel_eq_weight i j N k
  · rw [PeriodicRieszKernel.mFourierCoeff_kernel_neg]
    exact PeriodicRieszKernel.mFourierCoeff_kernel_eq_weight i j N k

theorem kernel_eq_sum_entryKernel (N : ℕ) (x : Td) :
    kernel N x = ∑ i : Fin d, ∑ j : Fin d, entryKernel i j N x • basisOperator i j := by
  simp only [kernel, rawKernel, entryKernel, realEvenPart, smul_add, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  module

@[simp] theorem basisOperator_apply (i j : Fin d) (a : Rd) :
    basisOperator i j a = a j • EuclideanSpace.single i 1 := by
  simp [basisOperator, InnerProductSpace.rankOne_apply, EuclideanSpace.inner_single_left]

theorem kernel_apply_component (N : ℕ) (x : Td) (a : Rd) (i : Fin d) :
    (kernel N x a) i = ∑ j : Fin d, entryKernel i j N x * a j := by
  rw [kernel_eq_sum_entryKernel]
  simp only [sum_apply, smul_apply, basisOperator_apply, smul_smul]
  simp [Pi.single_apply]

end Mettapedia.Analysis.PeriodicRieszOperator
