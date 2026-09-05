import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBufferedAnnularFrozenFrameTransfer
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalFrameKernelTransfer

/-!
# Physical variable-frame endpoint for the full annular multiplier

The four-chart annular kernel is conjugated by the physical oriented frame:
both inputs are expressed in frame coordinates and the output is returned to
physical coordinates.  The exact finite-Fourier identity holds on the rotated
annular support, and the `C/N` pointwise endpoint remains uniform for an
arbitrary spatially varying frame field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBufferedAnnularPhysicalFrameTransfer

open MeasureTheory
open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeFiniteFourierBilinearTransfer
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeBufferedAnnularMultiplier
open PancakeBufferedAnnularFrozenFrameTransfer

/-- The full annular kernel action in physical coordinates for one frozen
oriented frame. -/
def physicalOrientedFrameLocalizationSquareDyadicKernelAction
    (F : OrientedFrameEquiv) (N : ℕ)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (torusBilinearKernelAction
      (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
        (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
      (fun y ↦ orientedFrameComplexLinearMap F (f y))
      (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)

/-- Exact physical finite-Fourier identity on the full rotated annular
support. -/
theorem physicalOrientedFrameLocalizationSquareDyadicKernelAction_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hbuffer : ∀ k ∈ s, ∀ l ∈ t,
      InLocalizationBufferedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l).1 ∧
        InLocalizationBufferedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l).2) :
    physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ s, ∑ l ∈ t,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F (omega k))
                (orientedFrameComplexLinearMap F (eta l)))) := by
  unfold physicalOrientedFrameLocalizationSquareDyadicKernelAction
  simp_rw [orientedFrameComplexLinearMap_finiteFourierReconstruction]
  rw [unitTorusRotatedLocalizationSquareDyadic_action_eq_coherent
    (orientedFrameFrequencyPairLinearIsometryEquiv F) hN _ _ _ _ x hbuffer]

/-- Frozen physical endpoint for arbitrary continuous bounded fields. -/
theorem exists_uniform_physicalOrientedFrameLocalizationSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N f g x‖ ≤
          243 * (C / N) * M * P := by
  rcases exists_uniform_frozenFrameLocalizationSquareDyadic_bilinear_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN f g x M P hf hg hfb hgb
  have hM : 0 ≤ M := (norm_nonneg (f x)).trans (hfb x)
  have hP : 0 ≤ P := (norm_nonneg (g x)).trans (hgb x)
  have hfFrame : Continuous (fun y ↦ orientedFrameComplexLinearMap F (f y)) :=
    (orientedFrameComplexLinearMap F).continuous_of_finiteDimensional.comp hf
  have hgFrame : Continuous (fun y ↦ orientedFrameComplexLinearMap F (g y)) :=
    (orientedFrameComplexLinearMap F).continuous_of_finiteDimensional.comp hg
  have hfbFrame : ∀ y,
      ‖orientedFrameComplexLinearMap F (f y)‖ ≤ 3 * M := by
    intro y
    exact (norm_orientedFrameComplexLinearMap_le F _).trans
      (mul_le_mul_of_nonneg_left (hfb y) (by norm_num))
  have hgbFrame : ∀ y,
      ‖orientedFrameComplexLinearMap F (g y)‖ ≤ 3 * P := by
    intro y
    exact (norm_orientedFrameComplexLinearMap_le F _).trans
      (mul_le_mul_of_nonneg_left (hgb y) (by norm_num))
  have hkernel := hbound
    (orientedFrameFrequencyPairLinearIsometryEquiv F) N hN
    (fun y ↦ orientedFrameComplexLinearMap F (f y))
    (fun y ↦ orientedFrameComplexLinearMap F (g y)) x
    (3 * M) (3 * P) hfFrame hgFrame hfbFrame hgbFrame
  unfold physicalOrientedFrameLocalizationSquareDyadicKernelAction
  calc
    ‖orientedFrameInverseComplexLinearMap F
        (torusBilinearKernelAction
          (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (fun y ↦ orientedFrameComplexLinearMap F (f y))
          (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)‖ ≤
        3 * ‖torusBilinearKernelAction
          (unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (fun y ↦ orientedFrameComplexLinearMap F (f y))
          (fun y ↦ orientedFrameComplexLinearMap F (g y)) x‖ :=
      norm_orientedFrameInverseComplexLinearMap_le F _
    _ ≤ 3 * (9 * (C / N) * (3 * M) * (3 * P)) := by gcongr
    _ = 243 * (C / N) * M * P := by ring

/-! ## Pointwise spatially varying frames -/

def variablePhysicalFrameLocalizationSquareDyadicKernelAction
    (frame : BilinearSpatialTorus → OrientedFrameEquiv) (N : ℕ)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  physicalOrientedFrameLocalizationSquareDyadicKernelAction (frame x) N f g x

/-- Exact pointwise variable-frame finite-Fourier identity. -/
theorem variablePhysicalFrameLocalizationSquareDyadicKernelAction_eq_coherent
    (frame : BilinearSpatialTorus → OrientedFrameEquiv)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hbuffer : ∀ k ∈ s, ∀ l ∈ t,
      InLocalizationBufferedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv (frame x)) N k l).1 ∧
        InLocalizationBufferedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv (frame x)) N k l).2) :
    variablePhysicalFrameLocalizationSquareDyadicKernelAction frame N
        (finiteFourierReconstruction s omega)
        (finiteFourierReconstruction t eta) x =
      orientedFrameInverseComplexLinearMap (frame x)
        (∑ k ∈ s, ∑ l ∈ t,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv (frame x))
                  N k l)
                (orientedFrameComplexLinearMap (frame x) (omega k))
                (orientedFrameComplexLinearMap (frame x) (eta l)))) :=
  physicalOrientedFrameLocalizationSquareDyadicKernelAction_eq_coherent
    (frame x) hN s t omega eta x hbuffer

/-- **Variable-frame full-annulus endpoint.**  No derivative or regularity of
the frame field and no Fourier-cardinality factor occurs. -/
theorem exists_uniform_variablePhysicalFrameLocalizationSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (frame : BilinearSpatialTorus → OrientedFrameEquiv)
        (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖variablePhysicalFrameLocalizationSquareDyadicKernelAction
            frame N f g x‖ ≤ 243 * (C / N) * M * P := by
  rcases exists_uniform_physicalOrientedFrameLocalizationSquareDyadic_bilinear_bound
    with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro frame N hN f g x M P hf hg hfb hgb
  exact hbound (frame x) N hN f g x M P hf hg hfb hgb

end PancakeBufferedAnnularPhysicalFrameTransfer
end NavierStokes
end FluidDynamics
end Mettapedia

