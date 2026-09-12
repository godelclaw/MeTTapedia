import Mettapedia.Analysis.PeriodicRieszOperator

/-! Normalization, zero-mode, symmetry and uniform-moment regressions. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Mettapedia.Analysis
open scoped Topology FourierTransform

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

-- Starting at scale one would omit part of the lowest nonzero lattice shell.
example : AnnularRieszKernel.scale 0 = (1 / 2 : ℝ) := by
  norm_num [AnnularRieszKernel.scale]

example (N : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ AnnularRieszKernel.weight N x ∧ AnnularRieszKernel.weight N x ≤ 1 :=
  ⟨AnnularRieszKernel.weight_nonneg N x, AnnularRieszKernel.weight_le_one N x⟩

example (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    Filter.Tendsto (fun N : ℕ ↦ AnnularRieszKernel.weight N x) Filter.atTop (𝓝 1) :=
  AnnularRieszKernel.tendsto_weight x (by rw [hx])

example (i j : Fin 3) (x : UnitAddTorus (Fin 3)) : PeriodicRieszKernel.kernel i j 0 x = 0 := by
  simp

example (i j : Fin 3) (N : ℕ) :
    UnitAddTorus.mFourierCoeff (PeriodicRieszKernel.kernel i j N) 0 = 0 := by
  simp [PeriodicRieszKernel.mFourierCoeff_kernel_eq_weight,
    UnitTorusLattice.frequency, AnnularRieszKernel.rieszEntry]

example (i j : Fin 3) (N : ℕ) (k : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (PeriodicRieszKernel.kernel i j N) (-k) =
      UnitAddTorus.mFourierCoeff (PeriodicRieszKernel.kernel i j N) k :=
  PeriodicRieszKernel.mFourierCoeff_kernel_neg i j N k

example (N : ℕ) (x y : UnitAddTorus (Fin 3)) :
    PeriodicRieszOperator.kernel N (y - x) = PeriodicRieszOperator.kernel N (x - y) :=
  PeriodicRieszOperator.kernel_sub_swap N x y

example (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    (∫ x : UnitAddTorus (Fin d), ‖x‖ ^ 2 * ‖PeriodicRieszOperator.kernel N x‖) ≤ C :=
  ⟨PeriodicRieszOperator.secondMomentBound d, PeriodicRieszOperator.secondMomentBound_nonneg d,
    PeriodicRieszOperator.secondMoment_le⟩

#print axioms Mettapedia.Analysis.AnnularRieszKernel.weight_nonneg
#print axioms Mettapedia.Analysis.AnnularRieszKernel.weight_le_one
#print axioms Mettapedia.Analysis.AnnularRieszKernel.tendsto_weight
#print axioms Mettapedia.Analysis.AnnularRieszKernel.entry_eq_cutoff_mul
#print axioms Mettapedia.Analysis.AnnularRieszKernel.contDiff_entry
#print axioms Mettapedia.Analysis.AnnularRieszKernel.hasCompactSupport_entry
#print axioms Mettapedia.Analysis.AnnularRieszKernel.fourier_dyadicKernel
#print axioms Mettapedia.Analysis.AnnularRieszKernel.secondMoment_dyadicKernel
#print axioms Mettapedia.Analysis.AnnularRieszKernel.hasSum_fourier_dyadicKernel
#print axioms Mettapedia.Analysis.AnnularRieszKernel.secondMoment_partialKernel_le
#print axioms Mettapedia.Analysis.UnitTorusLattice.cell_isAddFundamentalDomain
#print axioms Mettapedia.Analysis.UnitTorusPeriodization.integral_representative
#print axioms Mettapedia.Analysis.UnitTorusPeriodization.lintegral_representative
#print axioms Mettapedia.Analysis.UnitTorusPeriodization.mFourierCoeff_periodize
#print axioms Mettapedia.Analysis.UnitTorusPeriodization.integral_moment_periodize_le
#print axioms Mettapedia.Analysis.PeriodicRieszKernel.integrable_kernel
#print axioms Mettapedia.Analysis.PeriodicRieszKernel.secondMoment_le
#print axioms Mettapedia.Analysis.PeriodicRieszKernel.mFourierCoeff_kernel_eq_weight
#print axioms Mettapedia.Analysis.PeriodicRieszKernel.tendsto_mFourierCoeff_kernel
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.kernel_sub_swap
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.integrable_kernel
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.integrable_secondMoment
#print axioms Mettapedia.Analysis.PeriodicRieszOperator.secondMoment_le
