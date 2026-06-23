import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyPressureSchwartzMean
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyPressureSchwartzLinear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyPressureSchwartzSmooth
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyPressureSchwartzScalar
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyPressureSchwartzSlice

/-!
# Navier-Stokes Energy: Interfaces

Analytic seam predicates and scalar-Schwartz derivative/integrability interfaces for the energy lane.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- The space integrand `u · Δu` from the viscous term. -/
def laplacianEnergyPairing (u : NSVelocityField) (t : NSTime) : NSSpace → ℝ :=
  fun x => ⟪u t x, spatialLaplacian u t x⟫

/-- The derivative-under-the-integral seam for the normalized kinetic energy.
This is the first genuinely analytic missing lemma on the current concrete NS
surface. -/
def EnergyDerivativeFormula (u : NSVelocityField) : Prop :=
  ∀ t,
    HasDerivAt (normalizedKineticEnergy u)
      (∫ x, timeEnergyPairing u t x ∂volume) t

/-- The viscous integration-by-parts seam
`∫ u · Δu = - ∫ ‖∇u‖²`. This is the second genuinely analytic missing lemma on
the current concrete NS surface. -/
def ViscousEnergyPairingFormula (u : NSVelocityField) : Prop :=
  ∀ t, ∫ x, laplacianEnergyPairing u t x ∂volume = -enstrophyAt u t

/-- Corrected viscous pairing seam using the coordinatewise dissipation density
coming from the standard orthonormal basis of `ℝ^3`. -/
def CoordinateViscousEnergyPairingFormula (u : NSVelocityField) : Prop :=
  ∀ t, ∫ x, laplacianEnergyPairing u t x ∂volume = -coordinateEnstrophyAt u t

/-- Integrability of the three space pairings used in the energy reduction. -/
def EnergyPairingIntegrable (u : NSVelocityField) (p : NSPressureField) : Prop :=
  ∀ t,
    Integrable (laplacianEnergyPairing u t) ∧
      Integrable (convectionEnergyPairing u t) ∧
      Integrable (pressureEnergyPairing u p t)

/-- A Schwartz profile on `ℝ^3` has integrable squared norm against Lebesgue
measure. This is the concrete `L²` input needed for the kinetic-energy
computations below. -/
theorem integrable_norm_sq_of_schwartz
    (f : 𝓢(NSSpace, NSSpace)) :
    Integrable (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ)) := by
  simpa using
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (μ := (volume : Measure NSSpace))
      f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (μ := (volume : Measure NSSpace)))

/-- Time derivative of a scalar-modulated spatial profile `u(t,x)=a(t)•f(x)`.
-/
theorem timeVelocityDerivative_scalar_smul
    (a a' : ℝ → ℝ) (f : NSSpace → NSSpace)
    (ha : ∀ t, HasDerivAt a (a' t) t) :
    ∀ t x, timeVelocityDerivative (fun s y => a s • f y) t x = a' t • f x := by
  intro t x
  unfold timeVelocityDerivative timeFDeriv
  have hDeriv : HasDerivAt (fun s : NSTime => a s • f x) (a' t • f x) t := by
    exact (ha t).smul_const (f x)
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Kinetic energy of a scalar-modulated Schwartz profile
`u(t,x)=a(t)•f(x)`. -/
theorem kineticEnergyAt_scalar_smul_schwartz
    (a : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace)) :
    kineticEnergyAt (fun t x => a t • f x) =
      fun t => (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  funext t
  rw [kineticEnergyAt]
  have hDensity :
      kineticEnergyDensity (fun s y => a s • f y) t =
        fun x : NSSpace => (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) := by
    funext x
    simp [kineticEnergyDensity, norm_smul, mul_pow, sq_abs]
  rw [hDensity]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    integral_const_mul ((a t) ^ (2 : ℕ)) (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ))

/-- Integral of the time-energy pairing for a scalar-modulated Schwartz profile
`u(t,x)=a(t)•f(x)`. -/
theorem integral_timeEnergyPairing_scalar_smul_schwartz
    (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t) :
    ∀ t,
      ∫ x, timeEnergyPairing (fun s y => a s • f y) t x ∂volume =
        (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
  intro t
  have hPair :
      timeEnergyPairing (fun s y => a s • f y) t =
        fun x : NSSpace => (a t * a' t) * ‖f x‖ ^ (2 : ℕ) := by
    funext x
    rw [timeEnergyPairing, timeVelocityDerivative_scalar_smul a a' f ha t x]
    simp [real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm]
  rw [hPair]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    integral_const_mul (a t * a' t) (fun x : NSSpace => ‖f x‖ ^ (2 : ℕ))

/-- The derivative-under-the-integral seam holds for scalar-modulated
Schwartz profiles `u(t,x)=a(t)•f(x)`. This is a genuine nontrivial finite-energy
class on the concrete `ℝ × ℝ^3` surface. -/
theorem EnergyDerivativeFormula_of_scalar_smul_schwartz
    (a a' : ℝ → ℝ) (f : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t) :
    EnergyDerivativeFormula (fun s y => a s • f y) := by
  intro t
  let E : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  have hEnergy :
      normalizedKineticEnergy (fun s y => a s • f y) =
        fun s => ((1 / 2 : ℝ) * E) * (a s) ^ (2 : ℕ) := by
    funext s
    rw [normalizedKineticEnergy, kineticEnergyAt_scalar_smul_schwartz]
    simp [E]
    ring
  have hPair :
      ∫ x, timeEnergyPairing (fun s y => a s • f y) t x ∂volume =
        (a t * a' t) * E := by
    simpa [E] using integral_timeEnergyPairing_scalar_smul_schwartz a a' f ha t
  rw [hEnergy, hPair]
  have hPow :
      HasDerivAt (fun s : ℝ => (a s) ^ (2 : ℕ)) (2 * a t * a' t) t := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (ha t).pow 2
  have hDeriv :
      HasDerivAt (fun s : ℝ => ((1 / 2 : ℝ) * E) * (a s) ^ (2 : ℕ))
        (((1 / 2 : ℝ) * E) * (2 * a t * a' t)) t := by
    exact hPow.const_mul (((1 / 2 : ℝ) * E))
  convert hDeriv using 1
  ring

/-- The pointwise inner product of two Schwartz profiles on `ℝ^3` is
integrable against Lebesgue measure. -/
theorem integrable_inner_schwartz
    (f g : 𝓢(NSSpace, NSSpace)) :
    Integrable (fun x : NSSpace => ⟪f x, g x⟫) := by
  simpa [SchwartzMap.pairing_apply_apply] using
    (SchwartzMap.pairing (innerSL ℝ) f g).integrable

/-- Time derivative of a two-profile scalar superposition
`u(t,x)=a(t)•f(x)+b(t)•g(x)`. -/
theorem timeVelocityDerivative_add_scalar_smul
    (a a' b b' : ℝ → ℝ) (f g : NSSpace → NSSpace)
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    ∀ t x,
      timeVelocityDerivative (fun s y => a s • f y + b s • g y) t x =
        a' t • f x + b' t • g x := by
  intro t x
  unfold timeVelocityDerivative timeFDeriv
  have hDeriv :
      HasDerivAt (fun s : NSTime => a s • f x + b s • g x)
        (a' t • f x + b' t • g x) t := by
    exact (ha t).smul_const (f x) |>.add ((hb t).smul_const (g x))
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Kinetic energy of a two-profile scalar Schwartz superposition
`u(t,x)=a(t)•f(x)+b(t)•g(x)`. -/
theorem kineticEnergyAt_add_scalar_smul_schwartz
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) :
    kineticEnergyAt (fun t x => a t • f x + b t • g x) =
      fun t =>
        (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (2 * (a t * b t)) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t) ^ (2 : ℕ) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
  funext t
  rw [kineticEnergyAt]
  have hDensity :
      kineticEnergyDensity (fun s y => a s • f y + b s • g y) t =
        fun x : NSSpace =>
          (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
            (2 * (a t * b t)) * ⟪f x, g x⟫ +
              (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) := by
    funext x
    rw [kineticEnergyDensity]
    simpa [real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      norm_smul, sq_abs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using
      (norm_add_sq_real (a t • f x) (b t • g x))
  have hIntF :
      Integrable (fun x : NSSpace => (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul ((a t) ^ (2 : ℕ))
  have hIntFG :
      Integrable (fun x : NSSpace => (2 * (a t * b t)) * ⟪f x, g x⟫) := by
    exact (integrable_inner_schwartz f g).const_mul (2 * (a t * b t))
  have hIntG :
      Integrable (fun x : NSSpace => (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul ((b t) ^ (2 : ℕ))
  rw [hDensity]
  calc
    ∫ x,
        ((a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
          (2 * (a t * b t)) * ⟪f x, g x⟫ +
            (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ)) ∂volume
      = ∫ x,
          ((a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) +
            (2 * (a t * b t)) * ⟪f x, g x⟫) ∂volume
            + ∫ x, (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          simpa [add_assoc] using integral_add (hIntF.add hIntFG) hIntG
    _ = (∫ x, (a t) ^ (2 : ℕ) * ‖f x‖ ^ (2 : ℕ) ∂volume
          + ∫ x, (2 * (a t * b t)) * ⟪f x, g x⟫ ∂volume)
          + ∫ x, (b t) ^ (2 : ℕ) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_add hIntF hIntFG]
    _ = (a t) ^ (2 : ℕ) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (2 * (a t * b t)) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t) ^ (2 : ℕ) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- Integral of the time-energy pairing for a two-profile scalar Schwartz
superposition. -/
theorem integral_timeEnergyPairing_add_scalar_smul_schwartz
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    ∀ t,
      ∫ x, timeEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume =
        (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (a t * b' t + b t * a' t) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t * b' t) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
  intro t
  have hPair :
      timeEnergyPairing (fun s y => a s • f y + b s • g y) t =
        fun x : NSSpace =>
          (a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
            (a t * b' t + b t * a' t) * ⟪f x, g x⟫ +
              (b t * b' t) * ‖g x‖ ^ (2 : ℕ) := by
    funext x
    rw [timeEnergyPairing, timeVelocityDerivative_add_scalar_smul a a' b b' f g ha hb t x]
    simp [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm,
      add_mul, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hIntF :
      Integrable (fun x : NSSpace => (a t * a' t) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul (a t * a' t)
  have hIntFG :
      Integrable (fun x : NSSpace => (a t * b' t + b t * a' t) * ⟪f x, g x⟫) := by
    exact (integrable_inner_schwartz f g).const_mul (a t * b' t + b t * a' t)
  have hIntG :
      Integrable (fun x : NSSpace => (b t * b' t) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul (b t * b' t)
  rw [hPair]
  calc
    ∫ x,
        ((a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
          (a t * b' t + b t * a' t) * ⟪f x, g x⟫ +
            (b t * b' t) * ‖g x‖ ^ (2 : ℕ)) ∂volume
      = ∫ x,
          ((a t * a' t) * ‖f x‖ ^ (2 : ℕ) +
            (a t * b' t + b t * a' t) * ⟪f x, g x⟫) ∂volume
            + ∫ x, (b t * b' t) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          simpa [add_assoc] using integral_add (hIntF.add hIntFG) hIntG
    _ = (∫ x, (a t * a' t) * ‖f x‖ ^ (2 : ℕ) ∂volume
          + ∫ x, (a t * b' t + b t * a' t) * ⟪f x, g x⟫ ∂volume)
          + ∫ x, (b t * b' t) * ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_add hIntF hIntFG]
    _ = (a t * a' t) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
          (a t * b' t + b t * a' t) * ∫ x, ⟪f x, g x⟫ ∂volume +
            (b t * b' t) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

/-- The derivative-under-the-integral seam holds for two-profile scalar
Schwartz superpositions `u(t,x)=a(t)•f(x)+b(t)•g(x)`. This is the first class
where nontrivial cross terms enter the energy identity on the concrete whole
space. -/
theorem EnergyDerivativeFormula_of_add_scalar_smul_schwartz
    (a a' b b' : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (ha : ∀ t, HasDerivAt a (a' t) t)
    (hb : ∀ t, HasDerivAt b (b' t) t) :
    EnergyDerivativeFormula (fun s y => a s • f y + b s • g y) := by
  intro t
  let F : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume
  let FG : ℝ := ∫ x, ⟪f x, g x⟫ ∂volume
  let G : ℝ := ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume
  have hEnergy :
      normalizedKineticEnergy (fun s y => a s • f y + b s • g y) =
        fun s =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ) := by
    funext s
    rw [normalizedKineticEnergy, kineticEnergyAt_add_scalar_smul_schwartz]
    simp [F, FG, G]
    ring
  have hPair :
      ∫ x, timeEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume =
        F * (a t * a' t) + FG * (a t * b' t + b t * a' t) + G * (b t * b' t) := by
    simpa [F, FG, G, mul_comm, mul_left_comm, mul_assoc] using
      integral_timeEnergyPairing_add_scalar_smul_schwartz a a' b b' f g ha hb t
  rw [hEnergy, hPair]
  have hA2 :
      HasDerivAt (fun s : ℝ => (a s) ^ (2 : ℕ)) (2 * a t * a' t) t := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (ha t).pow 2
  have hAB :
      HasDerivAt (fun s : ℝ => a s * b s) (a' t * b t + a t * b' t) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (ha t).mul (hb t)
  have hB2 :
      HasDerivAt (fun s : ℝ => (b s) ^ (2 : ℕ)) (2 * b t * b' t) t := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (hb t).pow 2
  have hDeriv :
      HasDerivAt
        (fun s : ℝ =>
          ((1 / 2 : ℝ) * F) * (a s) ^ (2 : ℕ) +
            FG * (a s * b s) +
              ((1 / 2 : ℝ) * G) * (b s) ^ (2 : ℕ))
        ((((1 / 2 : ℝ) * F) * (2 * a t * a' t)) +
          (FG * (a' t * b t + a t * b' t)) +
            (((1 / 2 : ℝ) * G) * (2 * b t * b' t))) t := by
    simpa [add_assoc] using
      (hA2.const_mul (((1 / 2 : ℝ) * F))).add
        ((hAB.const_mul FG).add (hB2.const_mul (((1 / 2 : ℝ) * G))))
  convert hDeriv using 1
  ring
end NavierStokes
end FluidDynamics
end Mettapedia
