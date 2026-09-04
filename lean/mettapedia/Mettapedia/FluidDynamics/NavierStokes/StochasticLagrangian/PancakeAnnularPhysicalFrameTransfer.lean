import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAnnularFrozenFrameTransfer
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
namespace PancakeAnnularPhysicalFrameTransfer

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
open PancakeAnnularFrozenFrameTransfer

/-- The full annular kernel action in physical coordinates for one frozen
oriented frame. -/
def physicalOrientedFrameAnnularSquareDyadicKernelAction
    (F : OrientedFrameEquiv) (N : ℕ)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (torusBilinearKernelAction
      (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
        (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
      (fun y ↦ orientedFrameComplexLinearMap F (f y))
      (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)

/-- Exact physical finite-Fourier identity on the full rotated annular
support. -/
theorem physicalOrientedFrameAnnularSquareDyadicKernelAction_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hannular : ∀ k ∈ s, ∀ l ∈ t,
      InNormalizedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l).1 ∧
        InNormalizedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l).2) :
    physicalOrientedFrameAnnularSquareDyadicKernelAction F N
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
  unfold physicalOrientedFrameAnnularSquareDyadicKernelAction
  simp_rw [orientedFrameComplexLinearMap_finiteFourierReconstruction]
  rw [unitTorusRotatedAnnularSquareDyadic_action_eq_coherent
    (orientedFrameFrequencyPairLinearIsometryEquiv F) hN _ _ _ _ x hannular]

/-- Frozen physical endpoint for arbitrary continuous bounded fields. -/
theorem exists_uniform_physicalOrientedFrameAnnularSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖physicalOrientedFrameAnnularSquareDyadicKernelAction F N f g x‖ ≤
          243 * (C / N) * M * P := by
  rcases exists_uniform_frozenFrameAnnularSquareDyadic_bilinear_bound with
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
  unfold physicalOrientedFrameAnnularSquareDyadicKernelAction
  calc
    ‖orientedFrameInverseComplexLinearMap F
        (torusBilinearKernelAction
          (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (fun y ↦ orientedFrameComplexLinearMap F (f y))
          (fun y ↦ orientedFrameComplexLinearMap F (g y)) x)‖ ≤
        3 * ‖torusBilinearKernelAction
          (unitTorusPeriodizedRotatedAnnularSquareDyadicKernel
            (orientedFrameFrequencyPairLinearIsometryEquiv F) N)
          (fun y ↦ orientedFrameComplexLinearMap F (f y))
          (fun y ↦ orientedFrameComplexLinearMap F (g y)) x‖ :=
      norm_orientedFrameInverseComplexLinearMap_le F _
    _ ≤ 3 * (9 * (C / N) * (3 * M) * (3 * P)) := by gcongr
    _ = 243 * (C / N) * M * P := by ring

/-! ## Pointwise spatially varying frames -/

def variablePhysicalFrameAnnularSquareDyadicKernelAction
    (frame : BilinearSpatialTorus → OrientedFrameEquiv) (N : ℕ)
    (f g : BilinearSpatialTorus → ComplexVec3)
    (x : BilinearSpatialTorus) : ComplexVec3 :=
  physicalOrientedFrameAnnularSquareDyadicKernelAction (frame x) N f g x

/-- Exact pointwise variable-frame finite-Fourier identity. -/
theorem variablePhysicalFrameAnnularSquareDyadicKernelAction_eq_coherent
    (frame : BilinearSpatialTorus → OrientedFrameEquiv)
    {N : ℕ} (hN : 2 ≤ N)
    (s t : Finset Wavevector) (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hannular : ∀ k ∈ s, ∀ l ∈ t,
      InNormalizedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv (frame x)) N k l).1 ∧
        InNormalizedPancakeAnnulus
          (frozenFrameSquareDyadicFrequencyPairChart
            (orientedFrameFrequencyPairLinearIsometryEquiv (frame x)) N k l).2) :
    variablePhysicalFrameAnnularSquareDyadicKernelAction frame N
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
  physicalOrientedFrameAnnularSquareDyadicKernelAction_eq_coherent
    (frame x) hN s t omega eta x hannular

/-- **Variable-frame full-annulus endpoint.**  No derivative or regularity of
the frame field and no Fourier-cardinality factor occurs. -/
theorem exists_uniform_variablePhysicalFrameAnnularSquareDyadic_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (frame : BilinearSpatialTorus → OrientedFrameEquiv)
        (N : ℕ), 2 ≤ N →
      ∀ (f g : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (M P : ℝ),
        Continuous f → Continuous g →
        (∀ y, ‖f y‖ ≤ M) → (∀ y, ‖g y‖ ≤ P) →
        ‖variablePhysicalFrameAnnularSquareDyadicKernelAction
            frame N f g x‖ ≤ 243 * (C / N) * M * P := by
  rcases exists_uniform_physicalOrientedFrameAnnularSquareDyadic_bilinear_bound
    with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro frame N hN f g x M P hf hg hfb hgb
  exact hbound (frame x) N hN f g x M P hf hg hfb hgb

end PancakeAnnularPhysicalFrameTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
