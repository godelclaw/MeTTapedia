import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeVorticityTransportSplit

/-!
# Removing the transport mismatch from the squared forcing cost

The actual vorticity forcing splits into a reduced forcing and transport by
the difference of filtered and full retained velocities. Its signed pairing
with the spectral weight transfers to weak derivatives of that weight.
The full-velocity projection defect and strain difference remain explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSignedTransportForcing

open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakeFourierMaterialPaths PancakeFilteredStrainDynamics
open PancakePhysicalSpectralDefect PancakeMaterialDiffusionBudget PancakePhysicalWeightedTransport
open PancakeVorticityTransportSplit PancakePhysicalTransportCancellation PancakeWeightedOperatorTransport
open PancakeRegularizedMaterialRate PancakeRegularizedDiffusion PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def reducedVorticityForcing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (x : T3) : R3 :=
  spatialVorticityForcing (fun _ ↦ 1) modes u nu x +
    ((spatialStrain modes (filteredVelocity (fun _ ↦ 1) u) x).1 -
      (spatialStrain modes (filteredVelocity chi u) x).1) (spatialVorticity modes u x)

def gapForcingPairing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (f : T3 → R3) (x : T3) : ℝ :=
  2 * ⟪physicalGapWeight chi modes u delta x (spatialVorticity modes u x), f x⟫

theorem continuous_reducedVorticityForcing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) : Continuous (reducedVorticityForcing chi modes u nu) :=
  (continuous_vorticityForcing (fun _ ↦ 1) modes u nu).add
    (((continuous_subtype_val.comp (continuous_strain modes (filteredVelocity (fun _ ↦ 1) u))).sub
      (continuous_subtype_val.comp (continuous_strain modes (filteredVelocity chi u)))).clm_apply
        (continuous_vorticity modes u))

theorem continuous_gapForcingPairing (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (f : T3 → R3) (hf : Continuous f) :
    Continuous (gapForcingPairing chi modes u delta f) :=
  (((continuous_physicalGapWeight chi modes u delta).clm_apply (continuous_vorticity modes u)).inner hf).const_mul 2

theorem forcing_eq_reduced_add_transport
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (nu : ℝ) (x : T3)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (hchi : ∀ q, chi (-q) = conj (chi q)) :
    spatialVorticityForcing chi modes u nu x = reducedVorticityForcing chi modes u nu x +
      vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x :=
  spatialVorticityForcing_filter_split chi modes u nu x hs hr hchi

/-- Exact signed replacement for the transport part of the forcing.
There is no norm or Young inequality in this identity. -/
theorem integral_gapForcingPairing_reduced
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta nu : ℝ)
    (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q))
    (hchi : ∀ q, chi (-q) = conj (chi q))
    (hu : ∀ q ∈ modes, modeDot q (u q) = 0) :
    (∫ x : T3, gapForcingPairing chi modes u delta (spatialVorticityForcing chi modes u nu) x) =
      (∫ x : T3, gapForcingPairing chi modes u delta (reducedVorticityForcing chi modes u nu) x) -
      (∫ x : T3, physicalWeightVariation chi (fun q ↦ chi q - 1) modes u delta x) := by
  obtain ⟨hIT, _, hcancel⟩ := integral_physical_weighted_transport chi (fun q ↦ chi q - 1) modes u delta hu
  have hIG := (continuous_gapForcingPairing chi modes u delta _
    (continuous_reducedVorticityForcing chi modes u nu)).integrable_of_hasCompactSupport (μ := volume)
      (HasCompactSupport.of_compactSpace _)
  have he : ∀ x : T3, gapForcingPairing chi modes u delta (spatialVorticityForcing chi modes u nu) x =
      gapForcingPairing chi modes u delta (reducedVorticityForcing chi modes u nu) x +
      2 * ⟪physicalGapWeight chi modes u delta x (spatialVorticity modes u x),
        vectorTransport (spatialVorticity modes u) (velocityComponent (fun q ↦ chi q - 1) modes u) x⟫ := by
    intro x
    simp only [gapForcingPairing, forcing_eq_reduced_add_transport chi modes u nu x hs hr hchi,
      inner_add_right, mul_add]
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_add hIG (hIT.const_mul 2),
    integral_const_mul, hcancel]
  rfl

theorem material_linearRate_transport_le (S : SymmetricStrain) (w : R3)
    (R A : R3 →L[ℝ] R3) (g c b : R3) (delta nu : ℝ) :
    linearRate S delta w (-S.1 * S.1 + R + nu • A) (S.1 w + g + c + nu • b) +
      (1 / 2 : ℝ) * ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 ≤
      nu * linearRate S delta w A b + nonviscousEnvelope S w R g delta +
        2 * ⟪regularizedGap S delta w, c⟫ := by
  have he : S.1 w + g + c + nu • b = (S.1 w + g + nu • b) + c := by abel
  have hlin : linearRate S delta w (-S.1 * S.1 + R + nu • A) (S.1 w + g + c + nu • b) =
      linearRate S delta w (-S.1 * S.1 + R + nu • A) (S.1 w + g + nu • b) +
        2 * ⟪regularizedGap S delta w, c⟫ := by
    simp only [linearRate, he, inner_add_right]
    ring
  rw [hlin]
  have h := material_linearRate_le S w R A g b delta nu
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeSignedTransportForcing
