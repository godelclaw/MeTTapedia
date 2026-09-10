import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBoundaryEnergy

/-!
# Exact energy of a complex cutoff times a real Fourier field

Real symmetrization is performed before cutoff convolution. Thus an
arbitrary complex cutoff polynomial realizes its nonnegative squared-norm
weight exactly. The collected coefficients retain every frequency in the
Minkowski sum of the cutoff and field supports.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption PancakeTransverseEnergyFreezing
open PancakeFiniteFourierLocalization PancakeRealFourierProjection
open PancakePressureAnisotropyBudget PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def localizedCoefficient (c : FourierCoeff (Fin 3)) (modes : Finset Wavevector)
    (a : FourierVelocity) : FourierVelocity :=
  finiteCutoffConvolutionCoeff c.support modes c (realSymmetricCoeff a)

def localizedEnergy (c : FourierCoeff (Fin 3)) (modes : Finset Wavevector)
    (a : FourierVelocity) : ℝ :=
  fullEnergy (finiteCutoffOutputModes c.support modes) (localizedCoefficient c modes a)

theorem norm_realSymmetric_reconstruction_sq (modes : Finset Wavevector) (a : FourierVelocity)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) (x : T3) :
    ‖coefficientVec (finiteFourierReconstruction modes (realSymmetricCoeff a) x)‖ ^ 2 =
      ‖complexRealPartEuclidean (finiteFourierReconstruction modes a x)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coefficientVec, complexRealPartEuclidean, PiLp.toLp_apply,
    reconstruction_realSymmetricCoeff modes a hs, Complex.norm_real]

theorem localized_reconstruction_norm_sq (c : FourierCoeff (Fin 3)) (modes : Finset Wavevector)
    (a : FourierVelocity) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) (x : T3) :
    ‖coefficientVec (finiteFourierReconstruction (finiteCutoffOutputModes c.support modes)
      (localizedCoefficient c modes a) x)‖ ^ 2 =
        quadraticWeight c x * ‖complexRealPartEuclidean (finiteFourierReconstruction modes a x)‖ ^ 2 := by
  rw [localizedCoefficient, finiteFourierReconstruction_convolutionCoeff,
    ← finiteScalar_mul_finiteFourierReconstruction, scalarReconstruction_eq_fourierPolynomial]
  change ‖fourierPolynomial c x • coefficientVec
    (finiteFourierReconstruction modes (realSymmetricCoeff a) x)‖ ^ 2 = _
  rw [norm_smul, mul_pow, norm_realSymmetric_reconstruction_sq modes a hs,
    quadraticWeight, Complex.normSq_eq_norm_sq]

theorem integral_quadraticWeight_real_reconstruction_sq (c : FourierCoeff (Fin 3))
    (modes : Finset Wavevector) (a : FourierVelocity) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, quadraticWeight c x *
      ‖complexRealPartEuclidean (finiteFourierReconstruction modes a x)‖ ^ 2) =
      localizedEnergy c modes a := by
  rw [localizedEnergy, ← integral_norm_coefficientReconstruction_sq]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦
    (localized_reconstruction_norm_sq c modes a hs x).symm))

theorem localizedEnergy_nonneg (c : FourierCoeff (Fin 3)) (modes : Finset Wavevector)
    (a : FourierVelocity) : 0 ≤ localizedEnergy c modes a := fullEnergy_nonneg _ _

theorem localizedCoefficient_eq_zero_off_support (c : FourierCoeff (Fin 3)) (modes : Finset Wavevector)
    (a : FourierVelocity) (q : Wavevector) (hq : q ∉ finiteCutoffOutputModes c.support modes) :
    localizedCoefficient c modes a q = 0 := by
  unfold localizedCoefficient finiteCutoffConvolutionCoeff
  apply Finset.sum_eq_zero
  intro pk hpk
  have hp := Finset.mem_filter.mp hpk
  have hm := Finset.mem_product.mp hp.1
  exact False.elim (hq ((mem_finiteCutoffOutputModes_iff c.support modes q).mpr
    ⟨pk.1, hm.1, pk.2, hm.2, hp.2⟩))

end Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy
