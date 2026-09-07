import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalWeightedTransport

/-!
# Actual Fourier transport inside the vorticity forcing

The character-motion term is the real coordinate transport of the actual
vorticity. Its identification uses reality of the reconstructed velocity,
not a formal replacement of complex multiplication by real multiplication.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeVorticityTransportSplit

open scoped ComplexConjugate
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakePhysicalSpectralDefect
open PancakePhysicalDiffusionLimit PancakeMappedFourierDiffusion PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakeWeakIncompressibleTransport PancakeWeightedOperatorTransport
open PancakePhysicalTransportCancellation PancakeMeasurableMaterialRate PancakeDyadicDirectionEvolution
open PancakeMovingBlockEvolution PancakeGalerkinKineticEnergy PancakeSpatialStrainEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem shiftRate_vorticity_component (modes : Finset Wavevector) (u : FourierVelocity)
    (i j : Fin 3) (x : T3) :
    shiftRate (fun y ↦ spatialVorticity modes u y i) (coordinateShift j) x =
      vorticityGradient modes u j x i := by
  have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_spatialVorticity_shift modes u j 0 x)
  simpa only [shiftRate, Function.comp_def, PiLp.proj_apply, coordinateShift_zero, add_zero] using h.deriv

theorem vectorTransport_vorticity_eq (modes : Finset Wavevector) (u : FourierVelocity)
    (v : Fin 3 → T3 → ℝ) (x : T3) :
    vectorTransport (spatialVorticity modes u) v x =
      ∑ j : Fin 3, v j x • vorticityGradient modes u j x := by
  ext i
  simp only [vectorTransport, PiLp.toLp_apply, coordinateTransport, shiftRate_vorticity_component,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mul_comm]

theorem complex_coordinate_transport_sum (modes : Finset Wavevector) (a : FourierVelocity)
    (v : R3) (x : T3) :
    (∑ q ∈ modes, (unitTorusDerivativePhase * (realModeDot q (fun j ↦ v j) : ℂ) *
      UnitAddTorus.mFourier q x) • a q) =
      ∑ j : Fin 3, v j • finiteFourierReconstruction modes (derivativeCoeff j a) x := by
  ext i
  simp only [finiteFourierReconstruction, derivativeCoeff, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul, realModeDot, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem real_characterTransport_eq (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (hchi : ∀ q, chi (-q) = conj (chi q)) :
    complexRealPartEuclideanCLM (∑ q ∈ modes,
      finiteVelocityCharacterRate modes (filteredVelocity chi u) q x • fourierCurl u q) =
      vectorTransport (spatialVorticity modes u) (velocityComponent chi modes u) x := by
  have hp : ∀ q, finiteVelocityCharacterRate modes (filteredVelocity chi u) q x =
      unitTorusDerivativePhase * (realModeDot q (fun j ↦ spatialVelocity chi modes u x j) : ℂ) *
        UnitAddTorus.mFourier q x := by
    intro q
    rw [finiteVelocityCharacterRate_eq,
      ← ofReal_realModeDot_reconstruction modes (filteredVelocity chi u) q x hs
        (filteredVelocity_conjugate chi u hchi hr)]
    rfl
  simp_rw [hp]
  rw [complex_coordinate_transport_sum, map_sum, vectorTransport_vorticity_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, vorticityGradient, mappedField, fourierField_vector_eq]
  rfl

theorem spatialVorticityMaterialRate_transport_split
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (nu : ℝ) (x : T3)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (hchi : ∀ q, chi (-q) = conj (chi q)) :
    spatialVorticityMaterialRate chi modes u nu x =
      vectorTransport (spatialVorticity modes u) (velocityComponent chi modes u) x +
      complexRealPartEuclideanCLM (finiteFourierReconstruction modes
        (finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) nu) x) := by
  change complexRealPartEuclideanCLM (movingFiniteFourierDerivative modes (fourierCurl u)
    (finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) nu)
    (fun q ↦ finiteVelocityCharacterRate modes (filteredVelocity chi u) q x) x) = _
  simp only [movingFiniteFourierDerivative, Finset.sum_add_distrib, map_add, finiteFourierReconstruction]
  rw [real_characterTransport_eq chi modes u x hs hr hchi]

theorem velocityComponent_sub (chi eta : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (j : Fin 3) (x : T3) :
    velocityComponent (fun q ↦ chi q - eta q) modes u j x =
      velocityComponent chi modes u j x - velocityComponent eta modes u j x := by
  simp only [velocityComponent, spatialVelocity, finiteFourierReconstruction, filteredVelocity,
    sub_smul, smul_sub, Finset.sum_sub_distrib, map_sub, PiLp.sub_apply]

theorem vectorTransport_velocity_sub (w : T3 → R3) (v a : Fin 3 → T3 → ℝ) (x : T3) :
    vectorTransport w (fun j y ↦ v j y - a j y) x =
      vectorTransport w v x - vectorTransport w a x := by
  ext i
  simp only [vectorTransport, PiLp.toLp_apply, coordinateTransport, PiLp.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

/-- The full retained-velocity forcing is retained explicitly. It includes
the finite-output projection defect and is not asserted to vanish. -/
theorem spatialVorticityForcing_filter_split
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (nu : ℝ) (x : T3)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (hchi : ∀ q, chi (-q) = conj (chi q)) :
    spatialVorticityForcing chi modes u nu x =
      spatialVorticityForcing (fun _ ↦ 1) modes u nu x +
      ((spatialStrain modes (filteredVelocity (fun _ ↦ 1) u) x).1 -
        (spatialStrain modes (filteredVelocity chi u) x).1) (spatialVorticity modes u x) +
      vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x := by
  have hv : velocityComponent (fun q ↦ chi q - 1) modes u =
      fun j y ↦ velocityComponent chi modes u j y - velocityComponent (fun _ ↦ 1) modes u j y := by
    funext j y
    exact velocityComponent_sub chi (fun _ ↦ 1) modes u j y
  rw [hv, vectorTransport_velocity_sub]
  simp only [spatialVorticityForcing,
    spatialVorticityMaterialRate_transport_split chi modes u nu x hs hr hchi,
    spatialVorticityMaterialRate_transport_split (fun _ ↦ 1) modes u nu x hs hr (fun _ ↦ by simp), sub_apply]
  abel

end Mettapedia.FluidDynamics.NavierStokes.PancakeVorticityTransportSplit
