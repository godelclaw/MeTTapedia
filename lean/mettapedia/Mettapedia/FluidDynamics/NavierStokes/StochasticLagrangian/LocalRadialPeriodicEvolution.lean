import Mettapedia.Analysis.PeriodicRadialRieszEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialImageEvolution

/-!
# Summing the complete signed image rates for the actual solution

For fixed cutoff, the whole periodic pairing has a material derivative
equal to the convergent series of the complete signed image rates.
Real material lifts are used throughout. At coincident torus endpoints,
both vorticities agree and every first variation vanishes; no exceptional
diagonal is discarded. This is not a cutoff-uniform time budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialPeriodicEvolution

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity PancakeLocalGradientEquation
open PancakeLocalStrainEquation PancakeMatrixCurlAlgebra PancakeFilteredStrainDynamics
open PancakeLocalProjectedEquation PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakePeriodicComplexStretch PancakeInfiniteFourierDerivative
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing LocalVorticitySeparation
open LocalMeanAlignmentBalance (velocity)
open Mettapedia.Analysis EuclideanCrossProduct UnitTorusPeriodization
open scoped RealInnerProductSpace

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "Lat" => UnitTorusLattice.LatticeSubmodule (ι := Fin 3)

theorem torusProjection_separation (x y : X3) :
    torusProjection (separation x y) = torusPoint x - torusPoint y := by
  funext i
  exact AddCircle.coe_sub (p := (1 : ℝ)) (x i) (y i)

def periodicDensity (n N : ℕ) (u : FourierVelocity) (x y : X3) : ℝ :=
  SignedCrossKernel.pairedStretch (2 * (n + 1)) (PeriodicRadialRiesz.tensor N (torusPoint x - torusPoint y))
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y))

def periodicRate (n N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : X3) : ℝ :=
  SignedCrossKernel.pairedMaterialRate n (PeriodicRadialRiesz.tensor N (torusPoint x - torusPoint y))
    (PeriodicRadialRiesz.liftedTensorDerivative N (separation x y)
      (velocity u (torusPoint x) - velocity u (torusPoint y)))
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y))
    (fullStrainOperator u (torusPoint x) (fullVorticity u (torusPoint x)) +
      nu • fullVorticityLaplacian u (torusPoint x))
    (fullStrainOperator u (torusPoint y) (fullVorticity u (torusPoint y)) +
      nu • fullVorticityLaplacian u (torusPoint y))

/-- The same signed rate as a field on the product torus. -/
def fieldRate (n N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : T3) : ℝ :=
  SignedCrossKernel.pairedMaterialRate n (PeriodicRadialRiesz.tensor N (x - y))
    (periodize (RadialRieszRegularization.tensorDerivative N) (x - y) (velocity u x - velocity u y))
    (fullVorticity u x) (fullVorticity u y)
    (fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x)
    (fullStrainOperator u y (fullVorticity u y) + nu • fullVorticityLaplacian u y)

theorem periodicRate_eq_fieldRate (n N : ℕ) (u : FourierVelocity) (nu : ℝ) (x y : X3) :
    periodicRate n N u nu x y = fieldRate n N u nu (torusPoint x) (torusPoint y) := by
  simp only [periodicRate, fieldRate, PeriodicRadialRiesz.liftedTensorDerivative_eq_periodize,
    torusProjection_separation]

theorem imageRate_eq_zero_of_equalVorticity (n N : ℕ) (z : R3) (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x y : X3)
    (hω : fullVorticity u (torusPoint x) = fullVorticity u (torusPoint y)) :
    LocalRadialImageEvolution.materialRate n N z u nu x y = 0 := by
  rw [← LocalRadialImageEvolution.materialRate_eq n N z u nu hu hd]
  simp [SignedRadialStretch.rate, SignedRadialStretch.residualRate, SignedRadialStretch.amplitudePair,
    tripleProduct, hω]

theorem hasSum_materialImageRates (n N : ℕ) (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x y : X3) :
    HasSum (fun z : Lat ↦ LocalRadialImageEvolution.materialRate n N (z : R3) u nu x y)
      (periodicRate n N u nu x y) := by
  by_cases hxy : torusPoint x = torusPoint y
  · have hω := congrArg (fullVorticity u) hxy
    have hp : periodicRate n N u nu x y = 0 := by
      simp only [periodicRate, hω, SignedCrossKernel.pairedMaterialRate_self]
    rw [hp]
    apply hasSum_zero.congr_fun
    intro z
    exact imageRate_eq_zero_of_equalVorticity n N z u nu hu hd x y hω
  · have hq : torusProjection (separation x y) ≠ 0 := by
      rw [torusProjection_separation]
      exact sub_ne_zero.mpr hxy
    have hs := PeriodicRadialRiesz.hasSum_signedImageRates N n (EuclideanSpace.single 0 1) (by simp)
      (separation x y) hq (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y))
      (fullStrainOperator u (torusPoint x) (fullVorticity u (torusPoint x)) +
        nu • fullVorticityLaplacian u (torusPoint x))
      (fullStrainOperator u (torusPoint y) (fullVorticity u (torusPoint y)) +
        nu • fullVorticityLaplacian u (torusPoint y))
      (velocity u (torusPoint x) - velocity u (torusPoint y))
    rw [torusProjection_separation] at hs
    apply hs.congr_fun
    intro z
    exact (LocalRadialImageEvolution.materialRate_eq n N z u nu hu hd x y).symm

theorem summable_abs_materialImageRates (n N : ℕ) (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x y : X3) :
    Summable (fun z : Lat ↦ |LocalRadialImageEvolution.materialRate n N (z : R3) u nu x y|) :=
  (hasSum_materialImageRates n N u nu hu hd x y).summable.abs

theorem hasDerivAt_periodicDensity_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t) (n N : ℕ) :
    HasDerivAt (fun τ ↦ periodicDensity n N (s.coefficients τ) (X τ) (Y τ))
      (periodicRate n N (s.coefficients t) nu (X t) (Y t)) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ separation (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)
  have hH := (PeriodicRadialRiesz.hasFDerivAt_tensor_lift N (separation (X t) (Y t))).comp_hasDerivAt t hh
  simp only [Function.comp_def, torusProjection_separation] at hH
  exact SignedCrossKernel.hasDerivAt_pairedStretch_movingKernel n hx hy hH

theorem hasDerivAt_periodicDensity_imageSum {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t) (n N : ℕ) :
    HasDerivAt (fun τ ↦ periodicDensity n N (s.coefficients τ) (X τ) (Y τ))
      (∑' z : Lat, LocalRadialImageEvolution.materialRate n N (z : R3)
        (s.coefficients t) nu (X t) (Y t)) t := by
  have hm := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht)))))
  rw [(hasSum_materialImageRates n N _ nu hm (s.transverse t) (X t) (Y t)).tsum_eq]
  exact hasDerivAt_periodicDensity_path s g hg hSum hu a b hab hI X Y t ht hX hY n N

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialPeriodicEvolution
