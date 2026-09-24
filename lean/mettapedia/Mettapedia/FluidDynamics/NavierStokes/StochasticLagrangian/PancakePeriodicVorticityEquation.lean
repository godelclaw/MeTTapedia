import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierStretchingEvolution

/-!
# Unit-torus Fourier normalization of the pancake vorticity equation

The coherent pancake estimates use a Biot--Savart/stretching symbol with the
common Fourier phases suppressed.  That suppression is harmless for norms,
but an evolution equation must restore the sign.  For the unit-torus character
`exp (2 pi i k dot x)`, curl inversion contributes `-(2 pi i)⁻¹` and one
spatial derivative contributes `2 pi i`; their product is `-1`.

This file records that normalization exactly.  It defines the physical
unit-torus velocity, strain--vorticity, transport, and viscous coefficient
symbols, proves that physical strain is the negative of the previously used
phase-suppressed symbol, and packages the resulting finite Fourier vorticity
right-hand side.  No analytic estimate or solution-existence assertion is
made here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakePeriodicVorticityEquation

open scoped BigOperators
open PeriodicFourierTriad
open PancakePeriodicCoherentSplit
open PancakePeriodicComplexStretch
open PancakeComplexMisalignmentExpansion
open PancakeFiniteFourierLocalization
open PancakeArbitraryDataBlocks
open PancakeFrameCovariance
open PancakeBilinearPeriodization
open PancakeDyadicDirectionEvolution
open PancakeFourierStretchingEvolution
open DirectionEvolutionTilting
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-! ## Exact unit-torus coefficient symbols -/

/-- Fourier derivative multiplier for the unit-torus character
`exp (2 pi i k dot x)`. -/
def unitTorusDerivativePhase : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I

theorem unitTorusDerivativePhase_ne_zero : unitTorusDerivativePhase ≠ 0 := by
  simpa [unitTorusDerivativePhase] using Complex.two_pi_I_ne_zero

/-- Physical velocity coefficient recovered from a vorticity coefficient.
Indeed `omega_k = (2 pi i) k × u_k`, so
`u_k = -(2 pi i)⁻¹ |k|⁻² k × omega_k`. -/
def unitTorusBiotSavartAmp
    (k : Wavevector) (w : VelocityCoefficient) : VelocityCoefficient :=
  (-(unitTorusDerivativePhase)⁻¹) • complexBiotSavartAmp k w

/-- Direct unit-torus Fourier amplitude of `S(u_source) w_receiver`. -/
def unitTorusStrainStretchAmp
    (k : Wavevector) (wSource wReceiver : VelocityCoefficient) :
    VelocityCoefficient :=
  let u := unitTorusBiotSavartAmp k wSource
  ((1 / 2 : ℂ) * unitTorusDerivativePhase) •
    (coefficientDot u wReceiver • wavevectorCoefficient k +
      modeDot k wReceiver • u)

/-- Restoring the two Fourier phases changes the sign of the normalized
stretching symbol. -/
theorem unitTorusStrainStretchAmp_eq_neg_complexStretchAmp
    (k : Wavevector) (wSource wReceiver : VelocityCoefficient) :
    unitTorusStrainStretchAmp k wSource wReceiver =
      -complexStretchAmp k wSource wReceiver := by
  unfold unitTorusStrainStretchAmp unitTorusBiotSavartAmp
  unfold complexStretchAmp
  dsimp only
  rw [coefficientDot_smul_left]
  have hinner :
      ((-unitTorusDerivativePhase⁻¹ *
          coefficientDot (complexBiotSavartAmp k wSource) wReceiver) •
            wavevectorCoefficient k +
        modeDot k wReceiver •
          (-unitTorusDerivativePhase⁻¹ •
            complexBiotSavartAmp k wSource)) =
      (-unitTorusDerivativePhase⁻¹) •
        (coefficientDot (complexBiotSavartAmp k wSource) wReceiver •
            wavevectorCoefficient k +
          modeDot k wReceiver • complexBiotSavartAmp k wSource) := by
    ext i
    simp only [Pi.smul_apply, Pi.add_apply]
    ring
  rw [hinner, smul_smul]
  have hscalar :
      ((1 / 2 : ℂ) * unitTorusDerivativePhase) *
          (-unitTorusDerivativePhase⁻¹) = -(1 / 2 : ℂ) := by
    calc
      _ = -(1 / 2 : ℂ) *
          (unitTorusDerivativePhase * unitTorusDerivativePhase⁻¹) := by
            ring
      _ = -(1 / 2 : ℂ) := by
            rw [mul_inv_cancel₀ unitTorusDerivativePhase_ne_zero, mul_one]
  rw [hscalar]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply]
  ring

/-- Direct amplitude of the right-hand-side transport term
`-(u_source · grad) w_receiver`. -/
def unitTorusNegativeTransportAmp
    (source receiver : Wavevector)
    (wSource wReceiver : VelocityCoefficient) : VelocityCoefficient :=
  (-(unitTorusDerivativePhase *
      modeDot receiver (unitTorusBiotSavartAmp source wSource))) •
    wReceiver

/-- Curl inversion and differentiation also cancel exactly in the transport
term; the extra PDE minus sign leaves the positive phase-suppressed symbol. -/
theorem unitTorusNegativeTransportAmp_eq
    (source receiver : Wavevector)
    (wSource wReceiver : VelocityCoefficient) :
    unitTorusNegativeTransportAmp source receiver wSource wReceiver =
      modeDot receiver (complexBiotSavartAmp source wSource) • wReceiver := by
  unfold unitTorusNegativeTransportAmp unitTorusBiotSavartAmp
  rw [PancakePeriodicCoherentSplit.modeDot_smul]
  ext i
  simp only [Pi.smul_apply]
  field_simp [unitTorusDerivativePhase_ne_zero]

/-- Unit-torus Fourier amplitude of `nu * Delta omega` at one mode. -/
def unitTorusViscousVorticityCoeff
    (nu : ℝ) (omega : FourierVelocity) (q : Wavevector) :
    VelocityCoefficient :=
  ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • omega q

/-! ## Finite convolution coefficients -/

/-- Physical strain--vorticity convolution collected by output frequency. -/
def finiteUnitTorusStretchingCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  ∑ sr ∈ sourceModes ×ˢ receiverModes with sr.1 + sr.2 = q,
    unitTorusStrainStretchAmp sr.1 (omega sr.1) (eta sr.2)

/-- The physical finite stretching coefficient is the negative of the
phase-suppressed coefficient used by the coherent estimates. -/
theorem finiteUnitTorusStretchingCoeff_eq_neg
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    finiteUnitTorusStretchingCoeff sourceModes receiverModes omega eta q =
      -finiteComplexStretchingConvolutionCoeff
        sourceModes receiverModes omega eta q := by
  classical
  unfold finiteUnitTorusStretchingCoeff
    finiteComplexStretchingConvolutionCoeff
  simp_rw [unitTorusStrainStretchAmp_eq_neg_complexStretchAmp]
  simpa only [Finset.sum_neg_distrib]

/-- Reconstructing the physical coefficients gives the negative of the
previous pair-indexed phase-suppressed stretching polynomial. -/
theorem finiteFourierReconstruction_unitTorusStretchingCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) :
    finiteFourierReconstruction
        (finiteCutoffOutputModes sourceModes receiverModes)
        (finiteUnitTorusStretchingCoeff
          sourceModes receiverModes omega eta) =
      -finiteComplexStretchingSum sourceModes receiverModes omega eta := by
  rw [← finiteFourierReconstruction_stretchingConvolutionCoeff]
  have hcoeff :
      finiteUnitTorusStretchingCoeff sourceModes receiverModes omega eta =
        -finiteComplexStretchingConvolutionCoeff
          sourceModes receiverModes omega eta := by
    funext q
    exact finiteUnitTorusStretchingCoeff_eq_neg
      sourceModes receiverModes omega eta q
  rw [hcoeff]
  funext x i
  simp only [finiteFourierReconstruction, Pi.neg_apply, Finset.sum_apply,
    smul_neg]
  rw [Finset.sum_neg_distrib]

/-- Right-hand-side transport convolution collected by output frequency. -/
def finiteUnitTorusNegativeTransportCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  ∑ sr ∈ sourceModes ×ˢ receiverModes with sr.1 + sr.2 = q,
    unitTorusNegativeTransportAmp sr.1 sr.2 (omega sr.1) (eta sr.2)

/-- The two non-stretching channels in the finite vorticity equation. -/
def finiteUnitTorusNonstretchingCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (nu : ℝ) (q : Wavevector) :
    VelocityCoefficient :=
  finiteUnitTorusNegativeTransportCoeff
      sourceModes receiverModes omega eta q +
    unitTorusViscousVorticityCoeff nu eta q

/-- Exact finite unit-torus vorticity right-hand side
`S(u) eta - (u · grad) eta + nu Delta eta`. -/
def finiteUnitTorusVorticityRHS
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta : FourierVelocity) (nu : ℝ) (q : Wavevector) :
    VelocityCoefficient :=
  finiteUnitTorusStretchingCoeff sourceModes receiverModes omega eta q +
    finiteUnitTorusNonstretchingCoeff
      sourceModes receiverModes omega eta nu q

/-! ## The actual coefficient equation in the same-block direction law -/

/-- If the supplied coefficient derivative is the finite unit-torus
vorticity RHS, subtracting physical stretching leaves exactly transport plus
viscosity in the hard pancake block. -/
theorem dyadicPancakeEvolutionRemainder_eq_transport_add_viscosity
    (F : OrientedFrameEquiv) (N : ℕ)
    (sourceModes receiverModes : Finset Wavevector)
    (omega eta omegaDot : FourierVelocity) (nu : ℝ)
    (x : BilinearSpatialTorus)
    (hODE : omegaDot = finiteUnitTorusVorticityRHS
      sourceModes receiverModes omega eta nu) :
    dyadicPancakeEvolutionRemainder F N omegaDot
        (finiteUnitTorusStretchingCoeff
          sourceModes receiverModes omega eta) x =
      squareDyadicPancakeRealBlock F N
        (finiteUnitTorusNonstretchingCoeff
          sourceModes receiverModes omega eta nu) x := by
  subst omegaDot
  unfold dyadicPancakeEvolutionRemainder finiteUnitTorusVorticityRHS
  congr 1
  funext q i
  simp

/-- Direction evolution of the actual hard pancake block under the exact
finite unit-torus vorticity coefficient equation.  The two residual channels
are now concretely transport-plus-viscosity and the block/strain commutator. -/
theorem dyadicPancakeDirectionDerivative_eq_unitTorusVorticityChannels
    (S : R3 →L[ℝ] R3) (F : OrientedFrameEquiv) (N : ℕ)
    (sourceModes receiverModes : Finset Wavevector)
    {omegaPath : ℝ → FourierVelocity}
    (omega eta omegaDot : FourierVelocity) (nu : ℝ)
    (x : BilinearSpatialTorus)
    {r : ℝ → ℝ} {xi : ℝ → R3}
    {xiDot : R3} {radialRate t : ℝ}
    (hcoeff : ∀ k ∈ squareDyadicPancakeModes F N, ∀ i,
      HasDerivAt (fun tau ↦ omegaPath tau k i) (omegaDot k i) t)
    (hr : HasDerivAt r radialRate t)
    (hxi : HasDerivAt xi xiDot t)
    (hfactor :
      (fun tau ↦ squareDyadicPancakeRealBlock F N (omegaPath tau) x) =
        fun tau ↦ r tau • xi tau)
    (hunit : ∀ tau, ⟪xi tau, xi tau⟫ = 1)
    (hrne : r t ≠ 0)
    (hODE : omegaDot = finiteUnitTorusVorticityRHS
      sourceModes receiverModes omega eta nu) :
    xiDot = transverseComponent (xi t) (S (xi t)) +
      (r t)⁻¹ • transverseComponent (xi t)
        (squareDyadicPancakeRealBlock F N
          (finiteUnitTorusNonstretchingCoeff
            sourceModes receiverModes omega eta nu) x) +
      (r t)⁻¹ • transverseComponent (xi t)
        (dyadicPancakeStretchingProjectionDefect S F N
          (finiteUnitTorusStretchingCoeff
            sourceModes receiverModes omega eta)
          (r t) (xi t) x) := by
  rw [dyadicPancakeDirectionDerivative_eq_strain_add_evolutionRemainder_add_projectionDefect
    S F N omegaDot
      (finiteUnitTorusStretchingCoeff
        sourceModes receiverModes omega eta)
    x hcoeff hr hxi hfactor hunit hrne]
  rw [dyadicPancakeEvolutionRemainder_eq_transport_add_viscosity
    F N sourceModes receiverModes omega eta omegaDot nu x hODE]

end PancakePeriodicVorticityEquation
end NavierStokes
end FluidDynamics
end Mettapedia
