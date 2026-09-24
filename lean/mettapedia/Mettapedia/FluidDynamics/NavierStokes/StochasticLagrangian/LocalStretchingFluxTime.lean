import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalProjectedTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityGradientTime

/-!
# Actual time derivative of the projected stretching flux

The raw cubic tensor is differentiated in the continuous-field norm,
then mapped through the actual bounded gradient projection into tensor
L². The three product-rule contributions contain the actual velocity
RHS; none is an externally supplied time derivative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalStretchingFluxTime

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeInfiniteFourierTime PancakeIndexedFourierMoments
open PancakeHigherDerivativeMoments PancakeCurlOutputTail PancakeCoefficientLimitEquation
open PancakeGalerkinKineticEnergy PancakeDyadicDirectionEvolution PancakeLocalInfiniteVelocity
open PancakeLocalVelocityGradientTime PancakeVelocityGradientEnvelope PancakeInfiniteVelocityEnvelope
open LocalVorticityTime LongitudinalVorticityTime FullLambVector LongitudinalGradientFlux
open LongitudinalProjectedTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "H" => TensorL2 (Fin 3) R3

def velocityDerivativeField (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  realField (indexedDerivativeCoeff id j u)

def stretchingField (u : FourierVelocity) : C(T3, R3) :=
  ∑ j, pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (velocityDerivativeField u j)

def stretchingRateField (ν : ℝ) (u : FourierVelocity) : C(T3, R3) :=
  ∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (velocityDerivativeField (infiniteVelocityRHS ν u) j) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityField (infiniteVelocityRHS ν u))) (velocityDerivativeField u j))

def fluxRateField (ν : ℝ) (u : FourierVelocity) (j : Fin 3) : C(T3, R3) :=
  -(pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (stretchingRateField ν u) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (vorticityField (infiniteVelocityRHS ν u))) (stretchingField u))

def projectedRate (ν : ℝ) (u : FourierVelocity) : H :=
  gradientProjection (toTensorL2 (fluxRateField ν u))

def eulerianWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  ⟪projectedFlux 0 u, projectedRate ν u⟫

theorem velocityDerivativeField_apply (u : FourierVelocity) (j : Fin 3) (x : T3) :
    velocityDerivativeField u j x = velocityJet u j x := rfl

theorem stretchingField_apply (u : FourierVelocity) (x : T3) :
    stretchingField u x = ∑ j, vorticityField u x j • velocityJet u j x := rfl

theorem fluxField_zero_eq (u : FourierVelocity) (j : Fin 3) :
    fluxField 0 u j = -pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      (componentField j (vorticityField u)) (stretchingField u) := by
  ext x
  simp only [fluxField, ContinuousMap.coe_mk, mul_zero, zero_smul, add_zero,
    ContinuousMap.neg_apply, pointwise, ContinuousLinearMap.lsmul_apply,
    componentField_apply, stretchingField_apply]

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hg hSum hu

theorem hasDerivAt_velocityDerivativeField (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ velocityDerivativeField (s.coefficients τ) j)
      (velocityDerivativeField (infiniteVelocityRHS ν (s.coefficients t)) j) t :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).hasFDerivAt.comp_hasDerivAt t
    (fullGradientField_hasDerivAt s g hg hSum hu j t ht)

theorem hasDerivAt_vorticityField (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ vorticityField (s.coefficients τ))
      (vorticityField (infiniteVelocityRHS ν (s.coefficients t))) t :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).hasFDerivAt.comp_hasDerivAt t
    (fullCurlField_hasDerivAt s g hg hSum hu t ht)

theorem hasDerivAt_stretchingField (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ stretchingField (s.coefficients τ))
      (stretchingRateField ν (s.coefficients t)) t := by
  have hw := hasDerivAt_vorticityField s g hg hSum hu t ht
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
    hasDerivAt_pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
      ((componentField j).hasFDerivAt.comp_hasDerivAt t hw)
      (hasDerivAt_velocityDerivativeField s g hg hSum hu j t ht))

theorem hasDerivAt_fluxField (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fluxField 0 (s.coefficients τ) j)
      (fluxRateField ν (s.coefficients t) j) t := by
  simp only [fluxField_zero_eq]
  exact (hasDerivAt_pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    ((componentField j).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_vorticityField s g hg hSum hu t ht))
    (hasDerivAt_stretchingField s g hg hSum hu t ht)).neg

theorem hasDerivAt_projectedFlux (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ projectedFlux 0 (s.coefficients τ))
      (projectedRate ν (s.coefficients t)) t :=
  ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_pi.mpr (fun j ↦ hasDerivAt_fluxField s g hg hSum hu j t ht))

theorem hasDerivAt_projectedFluxSquare (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ projectedFluxSquare 0 (s.coefficients τ))
      (2 * eulerianWork ν (s.coefficients t)) t := by
  exact (hasDerivAt_projectedFlux s g hg hSum hu t ht).norm_sq

end Mettapedia.FluidDynamics.NavierStokes.LocalStretchingFluxTime
