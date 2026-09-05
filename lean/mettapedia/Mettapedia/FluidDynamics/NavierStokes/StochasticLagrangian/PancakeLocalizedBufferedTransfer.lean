import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBufferedAnnularPhysicalFrameTransfer

/-!
# Physical buffered transfer for spatially localized finite sectors

This module joins the two sides of the localization bridge.  A physical
cutoff times a finite pancake-sector field is first collected into an ordinary
finite Fourier reconstruction on its Minkowski-sum support.  The quantitative
support-thickening theorem then discharges every premise of the buffered
physical multiplier automatically.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeLocalizedBufferedTransfer

open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeMisalignmentEnergyBridge
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeAnnularSectorProjector
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeFiniteFourierLocalization
open PancakeBufferedAnnularMultiplier
open PancakeBufferedAnnularPhysicalFrameTransfer
open scoped BigOperators

/-- **Exact localized physical coherent identity.**  If the unlocalized
field modes lie in the pancake annulus and the cutoff modes lie in the fixed
normalized margin box, the buffered physical operator on the actual products
`χU` and `ψV` equals the coherent interaction of their collected convolution
coefficients.  No post-localization support assumption is required. -/
theorem physicalLocalizationAction_on_cutoffProducts_eq_coherent
    (F : OrientedFrameEquiv) {N : ℕ} (hN : 2 ≤ N)
    (sourceCutoffModes sourceModes receiverCutoffModes receiverModes :
      Finset Wavevector)
    (sourceCutoffCoeff receiverCutoffCoeff : Wavevector → ℂ)
    (omega eta : FourierVelocity)
    (x : BilinearSpatialTorus)
    (hsource : ∀ k ∈ sourceModes,
      InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N k))
    (hreceiver : ∀ l ∈ receiverModes,
      InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N l))
    (hsourceCutoff : ∀ p ∈ sourceCutoffModes,
      InNormalizedPancakeShift
        localizationTransverseMargin localizationAxialMargin
        (orientedFrameSquareDyadicNormalizedMode F N p))
    (hreceiverCutoff : ∀ p ∈ receiverCutoffModes,
      InNormalizedPancakeShift
        localizationTransverseMargin localizationAxialMargin
        (orientedFrameSquareDyadicNormalizedMode F N p)) :
    physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
        (fun y ↦
          finiteScalarFourierReconstruction
              sourceCutoffModes sourceCutoffCoeff y •
            finiteFourierReconstruction sourceModes omega y)
        (fun y ↦
          finiteScalarFourierReconstruction
              receiverCutoffModes receiverCutoffCoeff y •
            finiteFourierReconstruction receiverModes eta y) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ finiteCutoffOutputModes sourceCutoffModes sourceModes,
          ∑ l ∈ finiteCutoffOutputModes receiverCutoffModes receiverModes,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F
                  (finiteCutoffConvolutionCoeff sourceCutoffModes sourceModes
                    sourceCutoffCoeff omega k))
                (orientedFrameComplexLinearMap F
                  (finiteCutoffConvolutionCoeff
                    receiverCutoffModes receiverModes
                    receiverCutoffCoeff eta l)))) := by
  have hsourceProduct :
      (fun y ↦
        finiteScalarFourierReconstruction
            sourceCutoffModes sourceCutoffCoeff y •
          finiteFourierReconstruction sourceModes omega y) =
        finiteFourierReconstruction
          (finiteCutoffOutputModes sourceCutoffModes sourceModes)
          (finiteCutoffConvolutionCoeff
            sourceCutoffModes sourceModes sourceCutoffCoeff omega) := by
    calc
      _ = finiteCutoffLocalizedReconstruction
          sourceCutoffModes sourceModes sourceCutoffCoeff omega := by
        funext y
        exact finiteScalar_mul_finiteFourierReconstruction
          sourceCutoffModes sourceModes sourceCutoffCoeff omega y
      _ = _ := (finiteFourierReconstruction_convolutionCoeff
        sourceCutoffModes sourceModes sourceCutoffCoeff omega).symm
  have hreceiverProduct :
      (fun y ↦
        finiteScalarFourierReconstruction
            receiverCutoffModes receiverCutoffCoeff y •
          finiteFourierReconstruction receiverModes eta y) =
        finiteFourierReconstruction
          (finiteCutoffOutputModes receiverCutoffModes receiverModes)
          (finiteCutoffConvolutionCoeff
            receiverCutoffModes receiverModes receiverCutoffCoeff eta) := by
    calc
      _ = finiteCutoffLocalizedReconstruction
          receiverCutoffModes receiverModes receiverCutoffCoeff eta := by
        funext y
        exact finiteScalar_mul_finiteFourierReconstruction
          receiverCutoffModes receiverModes receiverCutoffCoeff eta y
      _ = _ := (finiteFourierReconstruction_convolutionCoeff
        receiverCutoffModes receiverModes receiverCutoffCoeff eta).symm
  rw [hsourceProduct, hreceiverProduct]
  apply physicalOrientedFrameLocalizationSquareDyadicKernelAction_eq_coherent
    F hN
  intro k hk l hl
  rw [frozenFrameSquareDyadicFrequencyPairChart_orientedFrame F
    (lt_of_lt_of_le (by norm_num) hN)]
  constructor
  · exact outputMode_mem_expandedNormalizedPancakeAnnulus
      F N hsource hsourceCutoff hk
  · exact outputMode_mem_expandedNormalizedPancakeAnnulus
      F N hreceiver hreceiverCutoff hl

/-- Spatial cutoff multiplication costs exactly the product of the cutoff and
field sup bounds in the buffered physical `C/N` endpoint.  The constant is
independent of all four finite supports. -/
theorem exists_uniform_physicalLocalization_bilinear_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (sourceCutoffModes sourceModes receiverCutoffModes receiverModes :
          Finset Wavevector)
        (sourceCutoffCoeff receiverCutoffCoeff : Wavevector → ℂ)
        (omega eta : FourierVelocity)
        (x : BilinearSpatialTorus) (A M B P : ℝ),
        (∀ y, ‖finiteScalarFourierReconstruction
          sourceCutoffModes sourceCutoffCoeff y‖ ≤ A) →
        (∀ y, ‖finiteFourierReconstruction sourceModes omega y‖ ≤ M) →
        (∀ y, ‖finiteScalarFourierReconstruction
          receiverCutoffModes receiverCutoffCoeff y‖ ≤ B) →
        (∀ y, ‖finiteFourierReconstruction receiverModes eta y‖ ≤ P) →
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
          (finiteCutoffLocalizedReconstruction
            sourceCutoffModes sourceModes sourceCutoffCoeff omega)
          (finiteCutoffLocalizedReconstruction
            receiverCutoffModes receiverModes receiverCutoffCoeff eta) x‖ ≤
          243 * (C / N) * (A * M) * (B * P) := by
  rcases
      exists_uniform_physicalOrientedFrameLocalizationSquareDyadic_bilinear_bound
    with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN sourceCutoffModes sourceModes
    receiverCutoffModes receiverModes sourceCutoffCoeff receiverCutoffCoeff
    omega eta x A M B P hA hM hB hP
  have hAnonneg : 0 ≤ A :=
    (norm_nonneg (finiteScalarFourierReconstruction
      sourceCutoffModes sourceCutoffCoeff x)).trans (hA x)
  have hMnonneg : 0 ≤ M :=
    (norm_nonneg (finiteFourierReconstruction sourceModes omega x)).trans
      (hM x)
  have hBnonneg : 0 ≤ B :=
    (norm_nonneg (finiteScalarFourierReconstruction
      receiverCutoffModes receiverCutoffCoeff x)).trans (hB x)
  have hPnonneg : 0 ≤ P :=
    (norm_nonneg (finiteFourierReconstruction receiverModes eta x)).trans
      (hP x)
  apply hbound F N hN _ _ x (A * M) (B * P)
  · exact continuous_finiteCutoffLocalizedReconstruction
      sourceCutoffModes sourceModes sourceCutoffCoeff omega
  · exact continuous_finiteCutoffLocalizedReconstruction
      receiverCutoffModes receiverModes receiverCutoffCoeff eta
  · intro y
    rw [← finiteScalar_mul_finiteFourierReconstruction]
    rw [norm_smul]
    exact mul_le_mul (hA y) (hM y) (norm_nonneg _) hAnonneg
  · intro y
    rw [← finiteScalar_mul_finiteFourierReconstruction]
    rw [norm_smul]
    exact mul_le_mul (hB y) (hP y) (norm_nonneg _) hBnonneg

end PancakeLocalizedBufferedTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
