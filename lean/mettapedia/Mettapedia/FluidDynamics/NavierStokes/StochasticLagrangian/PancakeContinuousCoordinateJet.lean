import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalFourierDerivative

/-!
# Canonical continuous coordinate jets and their Fourier coefficients

Every jet entry is an iterated ordinary spatial derivative of the input
field. The regularity predicate asserts continuity and differentiability
of these defined functions; it does not supply independent derivative
objects or Fourier identities. Translation invariance transfers the
derivative at zero to every point on each coordinate orbit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeContinuousCoordinateJet

open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierTranslationCurve
open PancakeHaarTransportRate PancakePhysicalFourierDerivative PancakeIncomingLowSourceEnergy

local notation "T3" => UnitAddTorus (Fin 3)

def scalarCoordinateDerivative (j : Fin 3) (f : T3 → ℂ) (x : T3) : ℂ :=
  deriv (fun h : ℝ ↦ f (x + coordinateShift j h)) 0

def coordinateJet (f : T3 → ℂ) (j : Fin 3) (n : ℕ) : T3 → ℂ :=
  (scalarCoordinateDerivative j)^[n] f

def HasContinuousCoordinateJet (N : ℕ) (f : T3 → ℂ) : Prop :=
  (∀ j n, n ≤ N → Continuous (coordinateJet f j n)) ∧
  (∀ j n, n < N → ∀ x, DifferentiableAt ℝ (fun h ↦ coordinateJet f j n (x + coordinateShift j h)) 0)

theorem coordinateJet_zero (f : T3 → ℂ) (j : Fin 3) : coordinateJet f j 0 = f := rfl

theorem coordinateJet_succ (f : T3 → ℂ) (j : Fin 3) (n : ℕ) :
    coordinateJet f j (n + 1) = scalarCoordinateDerivative j (coordinateJet f j n) :=
  Function.iterate_succ_apply' _ _ _

theorem coordinateShift_add (j : Fin 3) (s t : ℝ) :
    coordinateShift j (s + t) = coordinateShift j s + coordinateShift j t := by
  ext i
  by_cases hij : i = j <;>
    simp [coordinateShift, PancakeFourierMaterialPaths.torusPoint,
      PancakeFourierStrainGradient.coordinateLine, hij]

theorem hasDerivAt_coordinate_shift (f : T3 → ℂ) (j : Fin 3)
    (hd : ∀ x, DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ f (x + coordinateShift j t))
      (scalarCoordinateDerivative j f (x + coordinateShift j h)) h := by
  have hp : HasDerivAt (fun t ↦ f ((x + coordinateShift j h) + coordinateShift j t))
      (scalarCoordinateDerivative j f (x + coordinateShift j h)) (h - h) := by
    simpa only [sub_self, scalarCoordinateDerivative] using (hd (x + coordinateShift j h)).hasDerivAt
  have hdinner : HasDerivAt (fun t : ℝ ↦ t - h) 1 h := by
    simpa only [id_eq] using (hasDerivAt_id h).sub_const h
  have hc := hp.scomp (h := fun t : ℝ ↦ t - h) h hdinner
  have he (t : ℝ) : (x + coordinateShift j h) + coordinateShift j (t - h) = x + coordinateShift j t := by
    rw [add_assoc, ← coordinateShift_add]
    congr 2
    ring
  simpa only [Function.comp_def, he, one_smul] using hc

theorem fourierCoeff_coordinateJet (f : T3 → ℂ) (N : ℕ) (hf : HasContinuousCoordinateJet N f)
    (j : Fin 3) (n : ℕ) (hn : n ≤ N) (k : Wavevector) :
    UnitAddTorus.mFourierCoeff (coordinateJet f j n) k =
      (unitTorusDerivativePhase * (k j : ℂ)) ^ n * UnitAddTorus.mFourierCoeff f k := by
  induction n with
  | zero => simp only [coordinateJet_zero, pow_zero, one_mul]
  | succ n ih =>
    have hder := fourierCoeff_derivative
      ⟨coordinateJet f j n, hf.1 j n (by omega)⟩
      ⟨coordinateJet f j (n + 1), hf.1 j (n + 1) hn⟩ j
      (fun x h ↦ by
        simpa only [ContinuousMap.coe_mk, coordinateJet_succ] using
          hasDerivAt_coordinate_shift (coordinateJet f j n) j (hf.2 j n (by omega)) x h) k
    change UnitAddTorus.mFourierCoeff (coordinateJet f j (n + 1)) k =
      (unitTorusDerivativePhase * (k j : ℂ)) * UnitAddTorus.mFourierCoeff (coordinateJet f j n) k at hder
    rw [hder, ih (by omega), pow_succ]
    ring

theorem coordinateJet_frequency_bound (f : T3 → ℂ) (N : ℕ) (hf : HasContinuousCoordinateJet N f)
    (j : Fin 3) (n : ℕ) (hn : n ≤ N) (k : Wavevector) :
    ((2 * Real.pi) * ‖(k j : ℂ)‖) ^ n * ‖UnitAddTorus.mFourierCoeff f k‖ ≤
      ‖(⟨coordinateJet f j n, hf.1 j n hn⟩ : C(T3, ℂ))‖ := by
  have h := norm_fourierCoeff_le (⟨coordinateJet f j n, hf.1 j n hn⟩ : C(T3, ℂ)) k
  change ‖UnitAddTorus.mFourierCoeff (coordinateJet f j n) k‖ ≤ _ at h
  rw [fourierCoeff_coordinateJet f N hf j n hn k, norm_mul, norm_pow, norm_mul, norm_derivativePhase] at h
  exact h

end Mettapedia.FluidDynamics.NavierStokes.PancakeContinuousCoordinateJet
