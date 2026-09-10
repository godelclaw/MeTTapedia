import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierFiniteSupport

/-!
# Ordinary coordinate jets of finite Fourier fields

Every finite Fourier field has continuous coordinate jets of all orders.
The finite formulas specialize the full-series definitions, and the
Laplacian of the gradient uses genuine third coordinate derivatives.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierFiniteJets

open scoped BigOperators Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierPressureStrain
open PancakeFourierMaterialPaths PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeInfiniteSpatialLaplacian PancakeIndexedFourierMoments PancakeLocalGradientEquation
open PancakePeriodicVorticityEquation FourierFiniteSupport

local notation "T3" => UnitAddTorus (Fin 3)

def scalarJetCoeff (j : Fin 3) (n : ℕ) (a : Wavevector → ℂ) (q : Wavevector) : ℂ :=
  (unitTorusDerivativePhase * (q j : ℂ)) ^ n * a q

theorem scalarJetCoeff_supported (modes : Finset Wavevector) (a : Wavevector → ℂ)
    (hs : ∀ q, q ∉ modes → a q = 0) (j : Fin 3) (n : ℕ) (q : Wavevector) (hq : q ∉ modes) :
    scalarJetCoeff j n a q = 0 := by simp [scalarJetCoeff, hs q hq]

theorem scalarJet_hasDerivAt (modes : Finset Wavevector) (a : Wavevector → ℂ)
    (hs : ∀ q, q ∉ modes → a q = 0) (j : Fin 3) (n : ℕ) (x : T3) :
    HasDerivAt (fun h : ℝ ↦ fullFourierField id (scalarJetCoeff j n a)
        (x + PancakeFourierTranslationCurve.coordinateShift j h))
      (fullFourierField id (scalarJetCoeff j (n + 1) a) x) 0 := by
  have hz := scalarJetCoeff_supported modes a hs j n
  have ha : Summable (fun q ↦ ‖scalarJetCoeff j n a q‖) :=
    summable_of_ne_finset_zero (s := modes) (fun q hq ↦ by rw [hz q hq, norm_zero])
  have hd : indexedDerivativeCoeff id j (scalarJetCoeff j n a) = scalarJetCoeff j (n + 1) a := by
    funext q
    simp [indexedDerivativeCoeff, scalarJetCoeff, pow_succ', mul_assoc]
  have hn : Summable (fun q ↦ ‖indexedDerivativeCoeff id j (scalarJetCoeff j n a) q‖) := by
    apply summable_of_ne_finset_zero (s := modes)
    intro q hq
    simp [indexedDerivativeCoeff, hz q hq]
  simpa only [hd, PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
    hasDerivAt_fullFourierField_shift id _ ha j hn 0 x

theorem coordinateJet_eq_fullFourierField (modes : Finset Wavevector) (a : Wavevector → ℂ)
    (hs : ∀ q, q ∉ modes → a q = 0) (j : Fin 3) (n : ℕ) :
    PancakeContinuousCoordinateJet.coordinateJet (fullFourierField id a) j n =
      fullFourierField id (scalarJetCoeff j n a) := by
  induction n with
  | zero =>
    have hz : scalarJetCoeff j 0 a = a := by funext q; simp [scalarJetCoeff]
    rw [PancakeContinuousCoordinateJet.coordinateJet_zero, hz]
  | succ n ih =>
    rw [PancakeContinuousCoordinateJet.coordinateJet_succ, ih]
    funext x
    exact (scalarJet_hasDerivAt modes a hs j n x).deriv

theorem hasContinuousCoordinateJet (modes : Finset Wavevector) (a : Wavevector → ℂ)
    (hs : ∀ q, q ∉ modes → a q = 0) (N : ℕ) :
    PancakeContinuousCoordinateJet.HasContinuousCoordinateJet N (fullFourierField id a) := by
  constructor
  · intro j n _
    rw [coordinateJet_eq_fullFourierField modes a hs]
    exact (fullFourierField id _).continuous
  · intro j n _ x
    rw [coordinateJet_eq_fullFourierField modes a hs]
    exact (scalarJet_hasDerivAt modes a hs j n x).differentiableAt

theorem hasContinuousCoordinateJet_component (modes : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ modes → u q = 0) (N : ℕ) (i : Fin 3) :
    PancakeContinuousCoordinateJet.HasContinuousCoordinateJet N
      (fun x ↦ fullFourierField id u x i) := by
  have hc : (fun x ↦ fullFourierField id u x i) =
      fullFourierField id (fun q ↦ u q i) := by
    funext x
    rw [fullFourierField_eq_sum modes u hs,
      fullFourierField_eq_sum modes _ (fun q hq ↦ by rw [hs q hq]; rfl)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hc]
  exact hasContinuousCoordinateJet modes _ (fun q hq ↦ by rw [hs q hq]; rfl) N

theorem spatialVelocityGradient_eq_matrixReconstruction
    (modes : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ modes → u q = 0) (x : T3) :
    spatialVelocityGradient (fullFourierField id u) x =
      matrixReconstruction modes (gradientCoeff u) x := by
  ext i j
  rw [spatialVelocityGradient, coordinateDerivative_eq_sum modes u hs j x]
  simp only [Finset.sum_apply, Pi.smul_apply, indexedDerivativeCoeff,
    matrixReconstruction_apply, gradientCoeff, smul_eq_mul, id_eq]

theorem laplacian_gradient_eq_matrixReconstruction
    (modes : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ modes → u q = 0) (x : T3) :
    matrixLaplacian (spatialVelocityGradient (fullFourierField id u)) x =
      matrixReconstruction modes
        (fun q ↦ (unitTorusDerivativePhase ^ 2 * modeSquare q) • gradientCoeff u q) x := by
  have hm : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment modes u hs 1
  have hd (j : Fin 3) (q : Wavevector) (hq : q ∉ modes) : indexedDerivativeCoeff id j u q = 0 := by
    simp [indexedDerivativeCoeff, hs q hq]
  ext i j
  simp only [matrixLaplacian, spatialVelocityGradient,
    coordinateDerivative_fullFourierField id u hm j]
  rw [spatialLaplacian_fullFourierField _ (summable_fourierMoment modes _ (hd j) 2),
    fullFourierField_eq_sum modes _ (fun q hq ↦ by simp [laplacianCoeff, hd j q hq])]
  simp only [Finset.sum_apply, Pi.smul_apply, laplacianCoeff, indexedDerivativeCoeff,
    matrixReconstruction_apply, gradientCoeff, smul_eq_mul, Matrix.smul_apply, id_eq]

end Mettapedia.FluidDynamics.NavierStokes.FourierFiniteJets
