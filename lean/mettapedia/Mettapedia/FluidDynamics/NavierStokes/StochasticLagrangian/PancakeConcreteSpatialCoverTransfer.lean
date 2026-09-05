import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConcreteSmoothCellCutoff
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalizedBufferedTransfer

/-!
# Buffered coherent transfer on the concrete smooth spatial cover

This module packages the common finite-Fourier approximation of all `125`
smooth cover cells and feeds it to the localization-stable physical pancake
multiplier.  The resulting theorem has no abstract cutoff or Fourier-tail
premise: its cutoff functions and coefficients are the concrete objects built
in `PancakeConcreteSmoothCellCutoff`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConcreteSpatialCoverTransfer

open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentStretchSymbol
open PancakeMisalignmentEnergyBridge
open PancakeFiniteFourierLocalization
open PancakeAnnularChartCutoff
open PancakeAnnularMultiplierAssembly
open PancakeBufferedAnnularMultiplier
open PancakeAnnularSectorProjector
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeBufferedAnnularPhysicalFrameTransfer
open PancakeBufferedLocalizationStability
open PancakeLocalizedBufferedTransfer
open PancakeConcreteSmoothCellCutoff
open PancakeSmoothCoherentSymbol
open scoped BigOperators

/-- A simultaneous finite-Fourier approximation of the whole concrete
spatial cover at accuracy `epsilon`. -/
structure SpatialCoverFourierPackage (epsilon : ℝ) where
  modes : SpatialCellIndex → Finset Wavevector
  threshold : ℕ
  two_le_threshold : 2 ≤ threshold
  approximation : ∀ j x,
    ‖spatialCellCutoff j x -
      finiteScalarFourierReconstruction (modes j)
        (UnitAddTorus.mFourierCoeff (spatialCellCutoff j)) x‖ < epsilon
  margin : ∀ (j : SpatialCellIndex) (F : OrientedFrameEquiv) (N : ℕ),
    threshold ≤ N → ∀ p ∈ modes j,
      InNormalizedPancakeShift
        localizationTransverseMargin localizationAxialMargin
        (orientedFrameSquareDyadicNormalizedMode F N p)

/-- Every positive target accuracy admits a concrete package for all cover
cells. -/
theorem exists_spatialCoverFourierPackage
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (SpatialCoverFourierPackage epsilon) := by
  obtain ⟨modes, N₀, hN₀, happ, hmargin⟩ :=
    exists_uniform_spatialCoverFourierApproximation hepsilon
  exact ⟨⟨modes, N₀, hN₀, happ, hmargin⟩⟩

/-- The finite cutoff selected for one concrete cell. -/
def finiteSpatialCellCutoff {epsilon : ℝ}
    (P : SpatialCoverFourierPackage epsilon) (j : SpatialCellIndex) :
    UnitAddTorus (Fin 3) → ℂ :=
  finiteScalarFourierReconstruction (P.modes j)
    (UnitAddTorus.mFourierCoeff (spatialCellCutoff j))

theorem continuous_finiteSpatialCellCutoff {epsilon : ℝ}
    (P : SpatialCoverFourierPackage epsilon) (j : SpatialCellIndex) :
    Continuous (finiteSpatialCellCutoff P j) :=
  continuous_finiteScalarFourierReconstruction _ _

/-- The finite cutoff inherits a uniform sup bound from its concrete smooth
cell and the package error. -/
theorem norm_finiteSpatialCellCutoff_le {epsilon : ℝ}
    (P : SpatialCoverFourierPackage epsilon) (j : SpatialCellIndex)
    (x : UnitAddTorus (Fin 3)) :
    ‖finiteSpatialCellCutoff P j x‖ ≤ epsilon + ‖torusCellCutoff‖ := by
  calc
    ‖finiteSpatialCellCutoff P j x‖ =
        ‖(finiteSpatialCellCutoff P j x - spatialCellCutoff j x) +
          spatialCellCutoff j x‖ := by rw [sub_add_cancel]
    _ ≤ ‖finiteSpatialCellCutoff P j x - spatialCellCutoff j x‖ +
        ‖spatialCellCutoff j x‖ := norm_add_le _ _
    _ = ‖spatialCellCutoff j x - finiteSpatialCellCutoff P j x‖ +
        ‖spatialCellCutoff j x‖ := by rw [norm_sub_rev]
    _ ≤ epsilon + ‖torusCellCutoff‖ :=
      add_le_add (P.approximation j x).le
        (norm_spatialCellCutoff_le j x)

/-- **Uniform error from actual smooth cells to their finite cutoff
approximations.**  The bound remains `O(epsilon/N)` and is independent of the
field supports and of the `125`-cell cover cardinality. -/
theorem exists_uniform_actualSpatialCells_stability :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
        (sourceCell receiverCell : SpatialCellIndex)
        (F : OrientedFrameEquiv) (N : ℕ), P.threshold ≤ N →
      ∀ (sourceModes receiverModes : Finset Wavevector)
        (omega eta : FourierVelocity) (x : BilinearSpatialTorus)
        (M Q : ℝ),
        (∀ y, ‖finiteFourierReconstruction sourceModes omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction receiverModes eta y‖ ≤ Q) →
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ spatialCellCutoff sourceCell y •
                finiteFourierReconstruction sourceModes omega y)
              (fun y ↦ spatialCellCutoff receiverCell y •
                finiteFourierReconstruction receiverModes eta y) x -
            physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ finiteSpatialCellCutoff P sourceCell y •
                finiteFourierReconstruction sourceModes omega y)
              (fun y ↦ finiteSpatialCellCutoff P receiverCell y •
                finiteFourierReconstruction receiverModes eta y) x‖ ≤
          243 * (C / N) * (epsilon * M) * (‖torusCellCutoff‖ * Q) +
            243 * (C / N) * ((epsilon + ‖torusCellCutoff‖) * M) *
              (epsilon * Q) := by
  obtain ⟨C, hC, hstable⟩ := exists_uniform_cutoffApproximation_stability
  refine ⟨C, hC, ?_⟩
  intro epsilon P sourceCell receiverCell F N hN
    sourceModes receiverModes omega eta x M Q hM hQ
  apply hstable F N (P.two_le_threshold.trans hN)
      (spatialCellCutoff sourceCell) (finiteSpatialCellCutoff P sourceCell)
      (spatialCellCutoff receiverCell) (finiteSpatialCellCutoff P receiverCell)
      (finiteFourierReconstruction sourceModes omega)
      (finiteFourierReconstruction receiverModes eta)
      x epsilon ‖torusCellCutoff‖ (epsilon + ‖torusCellCutoff‖)
      epsilon M Q
  · exact (spatialCellCutoff sourceCell).continuous
  · exact continuous_finiteSpatialCellCutoff P sourceCell
  · exact (spatialCellCutoff receiverCell).continuous
  · exact continuous_finiteSpatialCellCutoff P receiverCell
  · exact continuous_finiteFourierReconstruction _ _
  · exact continuous_finiteFourierReconstruction _ _
  · intro y
    exact (P.approximation sourceCell y).le
  · exact norm_spatialCellCutoff_le receiverCell
  · exact norm_finiteSpatialCellCutoff_le P sourceCell
  · intro y
    exact (P.approximation receiverCell y).le
  · exact hM
  · exact hQ

/-- **Exact coherent action on every approximating cover cell.**  Above the
common package threshold, the finite approximation of any pair of concrete
cells stays within the buffered pancake chart, hence the physical multiplier
is exactly the coherent convolution formula. -/
theorem physicalLocalizationAction_on_finiteSpatialCells_eq_coherent
    {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
    (sourceCell receiverCell : SpatialCellIndex)
    (F : OrientedFrameEquiv) {N : ℕ} (hN : P.threshold ≤ N)
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus)
    (hsource : ∀ k ∈ sourceModes,
      InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N k))
    (hreceiver : ∀ l ∈ receiverModes,
      InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N l)) :
    physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
        (fun y ↦ finiteSpatialCellCutoff P sourceCell y •
          finiteFourierReconstruction sourceModes omega y)
        (fun y ↦ finiteSpatialCellCutoff P receiverCell y •
          finiteFourierReconstruction receiverModes eta y) x =
      orientedFrameInverseComplexLinearMap F
        (∑ k ∈ finiteCutoffOutputModes (P.modes sourceCell) sourceModes,
          ∑ l ∈ finiteCutoffOutputModes (P.modes receiverCell) receiverModes,
          (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
            (((((1 : ℝ) / N) : ℂ)) •
              coherentProjectedNormalizedStretch ((1 : ℝ) / N)
                (frozenFrameSquareDyadicFrequencyPairChart
                  (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
                (orientedFrameComplexLinearMap F
                  (finiteCutoffConvolutionCoeff
                    (P.modes sourceCell) sourceModes
                    (UnitAddTorus.mFourierCoeff (spatialCellCutoff sourceCell))
                    omega k))
                (orientedFrameComplexLinearMap F
                  (finiteCutoffConvolutionCoeff
                    (P.modes receiverCell) receiverModes
                    (UnitAddTorus.mFourierCoeff (spatialCellCutoff receiverCell))
                    eta l)))) := by
  apply physicalLocalizationAction_on_cutoffProducts_eq_coherent
    F (P.two_le_threshold.trans hN)
  · exact hsource
  · exact hreceiver
  · exact P.margin sourceCell F N hN
  · exact P.margin receiverCell F N hN

/-- The explicit coherent convolution generated by a pair of approximating
concrete cover cells. -/
def finiteSpatialCellsCoherentAction
    {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
    (sourceCell receiverCell : SpatialCellIndex)
    (F : OrientedFrameEquiv) (N : ℕ)
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus) : ComplexVec3 :=
  orientedFrameInverseComplexLinearMap F
    (∑ k ∈ finiteCutoffOutputModes (P.modes sourceCell) sourceModes,
      ∑ l ∈ finiteCutoffOutputModes (P.modes receiverCell) receiverModes,
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x) •
        (((((1 : ℝ) / N) : ℂ)) •
          coherentProjectedNormalizedStretch ((1 : ℝ) / N)
            (frozenFrameSquareDyadicFrequencyPairChart
              (orientedFrameFrequencyPairLinearIsometryEquiv F) N k l)
            (orientedFrameComplexLinearMap F
              (finiteCutoffConvolutionCoeff
                (P.modes sourceCell) sourceModes
                (UnitAddTorus.mFourierCoeff (spatialCellCutoff sourceCell))
                omega k))
            (orientedFrameComplexLinearMap F
              (finiteCutoffConvolutionCoeff
                (P.modes receiverCell) receiverModes
                (UnitAddTorus.mFourierCoeff (spatialCellCutoff receiverCell))
                eta l))))

/-- Named form of the exact finite-cell coherent identity. -/
theorem physicalLocalizationAction_on_finiteSpatialCells_eq_namedCoherent
    {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
    (sourceCell receiverCell : SpatialCellIndex)
    (F : OrientedFrameEquiv) {N : ℕ} (hN : P.threshold ≤ N)
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (x : BilinearSpatialTorus)
    (hsource : ∀ k ∈ sourceModes,
      InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N k))
    (hreceiver : ∀ l ∈ receiverModes,
      InNormalizedPancakeAnnulus
        (orientedFrameSquareDyadicNormalizedMode F N l)) :
    physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
        (fun y ↦ finiteSpatialCellCutoff P sourceCell y •
          finiteFourierReconstruction sourceModes omega y)
        (fun y ↦ finiteSpatialCellCutoff P receiverCell y •
          finiteFourierReconstruction receiverModes eta y) x =
      finiteSpatialCellsCoherentAction P sourceCell receiverCell F N
        sourceModes receiverModes omega eta x := by
  unfold finiteSpatialCellsCoherentAction
  exact physicalLocalizationAction_on_finiteSpatialCells_eq_coherent
    P sourceCell receiverCell F hN sourceModes receiverModes omega eta x
      hsource hreceiver

/-- **Actual smooth spatial cells converge to the coherent pancake action.**
For arbitrary finite annular fields, every pair of concrete cover cells has
the intended coherent formula up to an explicit `O(epsilon/N)` error.  The
constant is uniform in frequency, frame, cells, and Fourier support sizes. -/
theorem exists_uniform_actualSpatialCells_to_coherent :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {epsilon : ℝ} (P : SpatialCoverFourierPackage epsilon)
        (sourceCell receiverCell : SpatialCellIndex)
        (F : OrientedFrameEquiv) (N : ℕ), P.threshold ≤ N →
      ∀ (sourceModes receiverModes : Finset Wavevector)
        (omega eta : FourierVelocity) (x : BilinearSpatialTorus)
        (M Q : ℝ),
        (∀ k ∈ sourceModes,
          InNormalizedPancakeAnnulus
            (orientedFrameSquareDyadicNormalizedMode F N k)) →
        (∀ l ∈ receiverModes,
          InNormalizedPancakeAnnulus
            (orientedFrameSquareDyadicNormalizedMode F N l)) →
        (∀ y, ‖finiteFourierReconstruction sourceModes omega y‖ ≤ M) →
        (∀ y, ‖finiteFourierReconstruction receiverModes eta y‖ ≤ Q) →
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ spatialCellCutoff sourceCell y •
                finiteFourierReconstruction sourceModes omega y)
              (fun y ↦ spatialCellCutoff receiverCell y •
                finiteFourierReconstruction receiverModes eta y) x -
            finiteSpatialCellsCoherentAction P sourceCell receiverCell F N
              sourceModes receiverModes omega eta x‖ ≤
          243 * (C / N) * (epsilon * M) * (‖torusCellCutoff‖ * Q) +
            243 * (C / N) * ((epsilon + ‖torusCellCutoff‖) * M) *
              (epsilon * Q) := by
  obtain ⟨C, hC, hstable⟩ := exists_uniform_actualSpatialCells_stability
  refine ⟨C, hC, ?_⟩
  intro epsilon P sourceCell receiverCell F N hN
    sourceModes receiverModes omega eta x M Q
    hsource hreceiver hM hQ
  have hbound := hstable P sourceCell receiverCell F N hN
    sourceModes receiverModes omega eta x M Q hM hQ
  rw [physicalLocalizationAction_on_finiteSpatialCells_eq_namedCoherent
    P sourceCell receiverCell F hN sourceModes receiverModes omega eta x
      hsource hreceiver] at hbound
  exact hbound

end PancakeConcreteSpatialCoverTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
