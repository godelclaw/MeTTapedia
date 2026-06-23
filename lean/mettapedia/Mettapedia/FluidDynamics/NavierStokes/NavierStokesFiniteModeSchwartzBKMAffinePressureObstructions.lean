import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeSchwartzBKMZeroVelocity

/-!
# Navier-Stokes Finite-Mode Schwartz BKM: AffinePressureObstructions

Affine-plus-localized Schwartz pressure-gradient algebra and one-one two-mode obstruction theorems.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- The spatial gradient of a time-scaled Schwartz pressure slice is the
time coefficient times the spatial gradient of the fixed Schwartz profile. -/
theorem spatialPressureGradient_scalarSchwartzPressure
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
      ρ t • spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  unfold spatialPressureGradient
  change gradient ((ρ t) • fun y : NSSpace => q y) x =
    ρ t • gradient (fun y : NSSpace => q y) x
  rw [gradient, fderiv_const_smul_field]
  simp [gradient]

/-- In the full affine-plus-localized pressure class, the zero-flow forcing
term is exactly the affine coefficient plus the time-scaled Schwartz spatial
gradient.  This is the algebraic boundary that any zero-flow repair must meet. -/
theorem spatialPressureGradient_affineAddScalarSchwartzPressure
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
      c t + ρ t •
        spatialPressureGradient (fun _ : NSTime => fun y : NSSpace => q y) t x := by
  have haff :
      DifferentiableAt ℝ
        (fun y : NSSpace => (fun s : NSTime => fun z : NSSpace => ⟪c s, z⟫ + π s) t y)
        x := by
    simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      (((((InnerProductSpace.toDual ℝ NSSpace) (c t))).hasFDerivAt).add_const
        (π t)).differentiableAt
  have hschwartz :
      DifferentiableAt ℝ
        (fun y : NSSpace => (fun s : NSTime => fun z : NSSpace => ρ s * q z) t y)
        x := by
    exact ((q.smooth'.differentiable (by simp)) x).const_mul (ρ t)
  rw [affineAddScalarSchwartzPressure]
  rw [spatialPressureGradient_add haff hschwartz]
  rw [spatialPressureGradient_affinePressure]
  rw [spatialPressureGradient_scalarSchwartzPressure]

/-- Two-point obstruction for the concrete affine-plus-localized pressure
repair of the non-cancelling constant-one two-mode branch.  Under inviscid
convection closure, the exact pressure-gradient repair condition forces the
viscous Laplacian residual pair-difference to be a scalar multiple of the
fixed Schwartz pressure-gradient pair-difference.  The arbitrary affine
coefficient and time-only gauge disappear after subtracting the two spatial
points. -/
theorem not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
    (ν : ℝ) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          ρ t •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  intro hmom
  rcases hbad with ⟨t, x, y, hbad⟩
  let Lx :=
    spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
      spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x
  let Ly :=
    spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
      spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y
  let Qx := spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x
  let Qy := spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y
  have hbalance :=
    (momentumEquation_oneOneTwoModeSchwartzVelocity_iff_pressureGradient_lapSum_of_inviscidClosure
      ν (affineAddScalarSchwartzPressure c π ρ q) f g hclosure).1 hmom
  have hx :
      spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • Lx := by
    simpa [Lx] using hbalance t x
  have hy :
      spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y =
        (ν : ℝ) • Ly := by
    simpa [Ly] using hbalance t y
  have hpair :
      (ν : ℝ) • (Lx - Ly) = ρ t • (Qx - Qy) := by
    calc
      (ν : ℝ) • (Lx - Ly) = (ν : ℝ) • Lx - (ν : ℝ) • Ly := by
        rw [smul_sub]
      _ =
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x -
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y := by
        rw [← hx, ← hy]
      _ = (c t + ρ t • Qx) - (c t + ρ t • Qy) := by
        rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x,
          spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t y]
      _ = ρ t • Qx - ρ t • Qy := by
        abel
      _ = ρ t • (Qx - Qy) := by
        rw [smul_sub]
  exact hbad (by simpa [Lx, Ly, Qx, Qy] using hpair)

/-- If the localized pressure amplitude is zero at a time, the same
two-point obstruction reduces to spatial constancy of the viscous Laplacian
residual at that time.  For positive viscosity, a single residual
pair-difference blocks every affine-gauge repair with inactive localized
pressure at that time. -/
theorem not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_zeroLocalizedAmplitude_lapSum_pair_ne
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity)
    (c : NSTime → NSSpace) (π ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        ρ t = 0 ∧
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∀ t x,
      timeVelocityDerivative
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialConvection
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
        (ν : ℝ) • spatialLaplacian
          (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  refine
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
      ν f g c π ρ q hclosure ?_
  rcases hbad with ⟨t, x, y, hρzero, hLne⟩
  refine ⟨t, x, y, ?_⟩
  intro hpair
  have hsmul :
      (ν : ℝ) •
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) = 0 := by
    simpa [hρzero] using hpair
  have hdiff :
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y) = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hν.ne'
  exact hLne (sub_eq_zero.mp hdiff)

/-- Scalar-amplitude obstruction for the concrete affine-plus-localized
pressure repair.  If, at one time, no scalar can make the fixed Schwartz
pressure-gradient pair-differences match the viscous Laplacian residual
pair-differences, then there is no choice of affine coefficient, time-only
gauge, or localized amplitude curve that repairs the non-cancelling
constant-one branch. -/
theorem not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
    (ν : ℝ) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t, ∀ r : ℝ, ∃ x y,
        (ν : ℝ) •
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) ≠
          r •
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  rintro ⟨c, π, ρ, hmom⟩
  rcases hbad with ⟨t, hbad_t⟩
  rcases hbad_t (ρ t) with ⟨x, y, hpair⟩
  exact
    not_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_lapSum_pair_mismatch
      ν f g c π ρ q hclosure ⟨t, x, y, hpair⟩ hmom

/-- Two-pair scalar-amplitude obstruction for the concrete
affine-plus-localized pressure repair.  If two spatial pairs at the same time
have the same fixed Schwartz pressure-gradient pair-difference but different
viscous Laplacian residual pair-differences, then no single localized amplitude
can fit both pairs; hence no affine coefficient, gauge, or amplitude curve
repairs the non-cancelling constant-one branch. -/
theorem not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
            spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
        ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  classical
  refine
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
      ν f g q hclosure ?_
  rcases hbad with ⟨t, x₁, y₁, x₂, y₂, hQeq, hLne⟩
  let L₁ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)
  let L₂ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂)
  let Q₁ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁
  let Q₂ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂
  have hQeq' : Q₁ = Q₂ := by
    simpa [Q₁, Q₂] using hQeq
  have hLne' : L₁ ≠ L₂ := by
    simpa [L₁, L₂] using hLne
  refine ⟨t, fun r => ?_⟩
  by_cases hfirst : (ν : ℝ) • L₁ ≠ r • Q₁
  · exact ⟨x₁, y₁, by simpa [L₁, Q₁] using hfirst⟩
  · refine ⟨x₂, y₂, ?_⟩
    intro hsecond
    have hfirst_eq : (ν : ℝ) • L₁ = r • Q₁ := not_not.mp hfirst
    have hsecond_eq : (ν : ℝ) • L₂ = r • Q₂ := by
      simpa [L₂, Q₂] using hsecond
    have hsmul_eq : (ν : ℝ) • L₁ = (ν : ℝ) • L₂ := by
      calc
        (ν : ℝ) • L₁ = r • Q₁ := hfirst_eq
        _ = r • Q₂ := by rw [hQeq']
        _ = (ν : ℝ) • L₂ := hsecond_eq.symm
    have hsmul_zero : (ν : ℝ) • (L₁ - L₂) = 0 := by
      rw [smul_sub, hsmul_eq, sub_self]
    have hdiff_zero : L₁ - L₂ = 0 :=
      (smul_eq_zero.mp hsmul_zero).resolve_left hν.ne'
    exact hLne' (sub_eq_zero.mp hdiff_zero)

/-- If the fixed Schwartz pressure profile has the same spatial gradient at a
pair of points while the viscous Laplacian residual separates those points,
then no scalar localized amplitude can repair the non-cancelling constant-one
branch.  This blocks the full affine-plus-localized pressure family, not just a
preselected amplitude curve. -/
theorem not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_pressureGradient_pair_eq_lapSum_pair_ne
    {ν : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x y,
        spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x =
          spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y ∧
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) ≠
          (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
            spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∀ t x,
        timeVelocityDerivative
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialConvection
              (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x +
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) • spatialLaplacian
            (twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g) t x := by
  refine
    not_exists_momentumEquation_oneOneTwoMode_affineAddScalarSchwartzPressure_of_no_scalar_lapSum_pair_fit
      ν f g q hclosure ?_
  rcases hbad with ⟨t, x, y, hQeq, hLne⟩
  refine ⟨t, fun r => ⟨x, y, ?_⟩⟩
  intro hpair
  have hsmul :
      (ν : ℝ) •
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y)) = 0 := by
    simpa [hQeq] using hpair
  have hdiff :
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) -
        (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y +
          spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y) = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left hν.ne'
  exact hLne (sub_eq_zero.mp hdiff)

/-- BKM-data-level form of the two-pair over-determination obstruction.  If
the bad pair time lies inside the certified slab, then no finite-time witness
can hide the failed positive-viscosity repair inside its BKM envelope: the
witness momentum equation at the four slab points already forces the two
Laplacian residual pair-differences to agree. -/
theorem not_exists_BKMData_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
      ∃ W : ExplicitFiniteTimeRegularityWitness
          ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint := by
  rintro ⟨c, π, ρ, W, hWvel, hWpress, _Ω, _Bint, _hEnv, _hInt⟩
  rcases hbad with ⟨t, x₁, y₁, x₂, y₂, ht0, htT, hQeq, hLne⟩
  let L₁ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)
  let L₂ :=
    (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
      (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
        spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂)
  let Q₁ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁
  let Q₂ :=
    spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
      spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂
  have hQeq' : Q₁ = Q₂ := by
    simpa [Q₁, Q₂] using hQeq
  have hLne' : L₁ ≠ L₂ := by
    simpa [L₁, L₂] using hLne
  have hpressure :
      ∀ x : NSSpace,
        spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x =
          (ν : ℝ) •
            (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x +
              spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x) := by
    intro x
    have hmom := W.momentum_equation_on t x ht0 htT
    rw [hWvel, hWpress] at hmom
    rw [timeVelocityDerivative_twoModeSchwartzVelocity_deriv
        (a := fun _ : NSTime => 1) (b := fun _ : NSTime => 1)
        contDiff_const contDiff_const f g t x,
      spatialConvection_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x,
      spatialLaplacian_twoModeSchwartzVelocity
        (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x] at hmom
    simpa [hclosure t x] using hmom
  have hpair₁ : (ν : ℝ) • L₁ = ρ t • Q₁ := by
    calc
      (ν : ℝ) • L₁ =
          (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁) := by
        rw [smul_sub]
      _ =
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x₁ -
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y₁ := by
        rw [← hpressure x₁, ← hpressure y₁]
      _ = (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁) -
            (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) := by
        rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x₁,
          spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t y₁]
      _ = ρ t • Q₁ := by
        rw [smul_sub]
        abel
  have hpair₂ : (ν : ℝ) • L₂ = ρ t • Q₂ := by
    calc
      (ν : ℝ) • L₂ =
          (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
            (ν : ℝ) •
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂) := by
        rw [smul_sub]
      _ =
          spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t x₂ -
            spatialPressureGradient (affineAddScalarSchwartzPressure c π ρ q) t y₂ := by
        rw [← hpressure x₂, ← hpressure y₂]
      _ = (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂) -
            (c t + ρ t •
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) := by
        rw [spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t x₂,
          spatialPressureGradient_affineAddScalarSchwartzPressure c π ρ q t y₂]
      _ = ρ t • Q₂ := by
        rw [smul_sub]
        abel
  have hsmul_eq : (ν : ℝ) • L₁ = (ν : ℝ) • L₂ := by
    calc
      (ν : ℝ) • L₁ = ρ t • Q₁ := hpair₁
      _ = ρ t • Q₂ := by rw [hQeq']
      _ = (ν : ℝ) • L₂ := hpair₂.symm
  have hsmul_zero : (ν : ℝ) • (L₁ - L₂) = 0 := by
    rw [smul_sub, hsmul_eq, sub_self]
  have hdiff_zero : L₁ - L₂ = 0 :=
    (smul_eq_zero.mp hsmul_zero).resolve_left hν.ne'
  exact hLne' (sub_eq_zero.mp hdiff_zero)

/-- Route-level composition for the non-cancelling constant-one two-mode
branch.  The inviscid branch supplies a nonzero finite-time BKM-premise
package, but the same profile pair cannot be promoted to a positive-viscosity
finite-time BKM datum through any affine-plus-one-Schwartz-pressure repair
when the two-pair over-determination witness is present on the certified slab.
-/
theorem oneOneTwoModeSchwartzVelocity_inviscidBKM_and_not_exists_posViscosity_BKMData_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
    {ν T : ℝ} (hν : 0 < ν) (f g : NSSchwartzInitialVelocity) (q : 𝓢(NSSpace, ℝ))
    (hfg : ∃ x : NSSpace, f x + g x ≠ 0)
    (hfDiv : ∀ x, initialSpatialDivergence (f : NSInitialVelocity) x = 0)
    (hgDiv : ∀ x, initialSpatialDivergence (g : NSInitialVelocity) x = 0)
    (hclosure : ∀ t x,
          spatialConvection (timeIndependentVelocity (f : NSInitialVelocity)) t x +
            spatialFDeriv (timeIndependentVelocity (f : NSInitialVelocity)) t x (g x) +
            spatialFDeriv (timeIndependentVelocity (g : NSInitialVelocity)) t x (f x) +
            spatialConvection (timeIndependentVelocity (g : NSInitialVelocity)) t x =
        0)
    (hbad : ∃ t x₁ y₁ x₂ y₂,
        0 ≤ t ∧ t ≤ T ∧
          (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₁ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₁) =
            (spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t x₂ -
              spatialPressureGradient (fun _ : NSTime => fun z : NSSpace => q z) t y₂) ∧
          ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₁) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₁ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₁)) ≠
            ((spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t x₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t x₂) -
              (spatialLaplacian (timeIndependentVelocity (f : NSInitialVelocity)) t y₂ +
                spatialLaplacian (timeIndependentVelocity (g : NSInitialVelocity)) t y₂))) :
    ((∃ t x,
      twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g t x ≠
        (0 : NSSpace)) ∧
      ∃ W :
          ExplicitFiniteTimeRegularityWitness 0
            (twoModeSchwartzInitialVelocity 1 1 f g) T,
        W.velocity =
            twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
          W.pressure = (0 : NSPressureField) ∧
          ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
            vorticityEnvelopeOn W.velocity T Ω ∧
              integrableVorticityEnvelopeOn Ω T Bint) ∧
      ¬ ∃ c : NSTime → NSSpace, ∃ π : NSTime → ℝ, ∃ ρ : NSTime → ℝ,
        ∃ W : ExplicitFiniteTimeRegularityWitness
            ν (twoModeSchwartzInitialVelocity 1 1 f g) T,
          W.velocity =
              twoModeSchwartzVelocity (fun _ : NSTime => 1) (fun _ : NSTime => 1) f g ∧
            W.pressure = affineAddScalarSchwartzPressure c π ρ q ∧
            ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
              vorticityEnvelopeOn W.velocity T Ω ∧
                integrableVorticityEnvelopeOn Ω T Bint := by
  constructor
  · exact
      oneOneTwoModeSchwartzVelocity_nonzero_inviscidZeroPressure_BKMPremise_of_convectionClosure
        f g hfg hfDiv hgDiv hclosure
  · exact
      not_exists_BKMData_oneOneTwoMode_affineAddScalarSchwartzPressure_of_same_pressureGradient_pair_lapSum_pair_ne_on
        hν f g q hclosure hbad
end NavierStokes
end FluidDynamics
end Mettapedia
