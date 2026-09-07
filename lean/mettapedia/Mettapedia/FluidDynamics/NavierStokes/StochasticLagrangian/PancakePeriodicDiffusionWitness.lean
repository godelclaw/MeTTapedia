import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePlanarDiffusion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A periodic incompressible test of spectral-defect diffusion

An explicit trigonometric planar velocity supplies the strain and curl;
they are not independently chosen fields. The spatial Laplacian of its
actual spectral defect at the origin is -76. The pure heat contribution
to its time derivative there is -4 times the viscosity. Consequently the
heat-chain-rule production is positive, 72 times the viscosity.

This tests a pointwise subsolution claim, not monotonicity of a spatial
integral, and not existence or blowup for the nonlinear Navier--Stokes
equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicDiffusionWitness

open Real PancakePlanarSpectralDefect PancakePlanarDiffusion
open scoped Topology
open Filter

theorem hasDerivAt_trig_formula (f : ℝ → ℝ) (c0 cs cc t : ℝ)
    (hf : ∀ s, f s = c0 + cs * sin s + cc * cos s) :
    HasDerivAt f (cs * cos t - cc * sin t) t := by
  have h := ((hasDerivAt_const t c0).add ((Real.hasDerivAt_sin t).const_mul cs)).add
    ((Real.hasDerivAt_cos t).const_mul cc)
  have h' : HasDerivAt (fun s ↦ c0 + cs * sin s + cc * cos s)
      (cs * cos t - cc * sin t) t := h.congr_deriv (by ring)
  exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)

def velocityX (x y : ℝ) : ℝ := -sin y / 2 + sin x * cos y - 9 * cos x * cos y + 16 * cos y

def velocityY (x y : ℝ) : ℝ := sin x / 2 - cos x * sin y + 8 * cos x - 9 * sin x * sin y

def strainA (x y : ℝ) : ℝ := cos x * cos y + 9 * sin x * cos y

def strainB (x y : ℝ) : ℝ := (cos x - cos y) / 4 - 4 * sin x - 8 * sin y

def vorticityZ (x y : ℝ) : ℝ := (cos x + cos y) / 2 + 2 * sin x * sin y - 8 * sin x - 18 * cos x * sin y + 16 * sin y

def ax (x y : ℝ) : ℝ := -sin x * cos y + 9 * cos x * cos y

def ay (x y : ℝ) : ℝ := -cos x * sin y - 9 * sin x * sin y

def bx (x _y : ℝ) : ℝ := -sin x / 4 - 4 * cos x

def byy (_x y : ℝ) : ℝ := sin y / 4 - 8 * cos y

def wx (x y : ℝ) : ℝ := -sin x / 2 + 2 * cos x * sin y - 8 * cos x + 18 * sin x * sin y

def wy (x y : ℝ) : ℝ := -sin y / 2 + 2 * sin x * cos y - 18 * cos x * cos y + 16 * cos y

theorem hasDerivAt_strainA_x (x y : ℝ) :
    HasDerivAt (fun s ↦ strainA s y) (ax x y) x := by
  apply (hasDerivAt_trig_formula (fun s ↦ strainA s y) (0) (9 * cos y) (cos y) x
    (by intro s; dsimp [strainA]; ring)).congr_deriv
  dsimp [ax]
  ring

theorem hasDerivAt_strainA_y (x y : ℝ) :
    HasDerivAt (fun s ↦ strainA x s) (ay x y) y := by
  apply (hasDerivAt_trig_formula (fun s ↦ strainA x s) (0) (0) (cos x + 9 * sin x) y
    (by intro s; dsimp [strainA]; ring)).congr_deriv
  dsimp [ay]
  ring

theorem hasDerivAt_strainB_x (x y : ℝ) :
    HasDerivAt (fun s ↦ strainB s y) (bx x y) x := by
  apply (hasDerivAt_trig_formula (fun s ↦ strainB s y) (-cos y / 4 - 8 * sin y) (-4) (1 / 4) x
    (by intro s; dsimp [strainB]; ring)).congr_deriv
  dsimp [bx]
  ring

theorem hasDerivAt_strainB_y (x y : ℝ) :
    HasDerivAt (fun s ↦ strainB x s) (byy x y) y := by
  apply (hasDerivAt_trig_formula (fun s ↦ strainB x s) (cos x / 4 - 4 * sin x) (-8) (-1 / 4) y
    (by intro s; dsimp [strainB]; ring)).congr_deriv
  dsimp [byy]
  ring

theorem hasDerivAt_vorticityZ_x (x y : ℝ) :
    HasDerivAt (fun s ↦ vorticityZ s y) (wx x y) x := by
  apply (hasDerivAt_trig_formula (fun s ↦ vorticityZ s y) (cos y / 2 + 16 * sin y) (2 * sin y - 8) (1 / 2 - 18 * sin y) x
    (by intro s; dsimp [vorticityZ]; ring)).congr_deriv
  dsimp [wx]
  ring

theorem hasDerivAt_vorticityZ_y (x y : ℝ) :
    HasDerivAt (fun s ↦ vorticityZ x s) (wy x y) y := by
  apply (hasDerivAt_trig_formula (fun s ↦ vorticityZ x s) (cos x / 2 - 8 * sin x) (2 * sin x - 18 * cos x + 16) (1 / 2) y
    (by intro s; dsimp [vorticityZ]; ring)).congr_deriv
  dsimp [wy]
  ring

theorem hasDerivAt_velocityX_x (x y : ℝ) :
    HasDerivAt (fun s ↦ velocityX s y) (strainA x y) x := by
  apply (hasDerivAt_trig_formula (fun s ↦ velocityX s y) (-sin y / 2 + 16 * cos y) (cos y) (-9 * cos y) x
    (by intro s; dsimp [velocityX]; ring)).congr_deriv
  dsimp [strainA]
  ring

theorem hasDerivAt_velocityX_y (x y : ℝ) :
    HasDerivAt (fun s ↦ velocityX x s) (strainB x y - vorticityZ x y / 2) y := by
  apply (hasDerivAt_trig_formula (fun s ↦ velocityX x s) (0) (-1 / 2) (sin x - 9 * cos x + 16) y
    (by intro s; dsimp [velocityX]; ring)).congr_deriv
  dsimp [strainB, vorticityZ]
  ring

theorem hasDerivAt_velocityY_x (x y : ℝ) :
    HasDerivAt (fun s ↦ velocityY s y) (strainB x y + vorticityZ x y / 2) x := by
  apply (hasDerivAt_trig_formula (fun s ↦ velocityY s y) (0) (1 / 2 - 9 * sin y) (8 - sin y) x
    (by intro s; dsimp [velocityY]; ring)).congr_deriv
  dsimp [strainB, vorticityZ]
  ring

theorem hasDerivAt_velocityY_y (x y : ℝ) :
    HasDerivAt (fun s ↦ velocityY x s) (-strainA x y) y := by
  apply (hasDerivAt_trig_formula (fun s ↦ velocityY x s) (sin x / 2 + 8 * cos x) (-cos x - 9 * sin x) (0) y
    (by intro s; dsimp [velocityY]; ring)).congr_deriv
  dsimp [strainA]
  ring

/-- The velocity is divergence-free everywhere. Its strain and curl
are the same fields used by the spectral test. -/
theorem velocity_gradient (x y : ℝ) :
    deriv (fun s ↦ velocityX s y) x = strainA x y ∧
    deriv (fun s ↦ velocityY x s) y = -strainA x y ∧
    (deriv (fun s ↦ velocityX x s) y + deriv (fun s ↦ velocityY s y) x) / 2 =
      strainB x y ∧
    deriv (fun s ↦ velocityY s y) x - deriv (fun s ↦ velocityX x s) y =
      vorticityZ x y := by
  rw [(hasDerivAt_velocityX_x x y).deriv, (hasDerivAt_velocityY_y x y).deriv,
    (hasDerivAt_velocityX_y x y).deriv, (hasDerivAt_velocityY_x x y).deriv]
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> ring

theorem velocity_divergence_zero (x y : ℝ) :
    deriv (fun s ↦ velocityX s y) x + deriv (fun s ↦ velocityY x s) y = 0 := by
  rw [(velocity_gradient x y).1, (velocity_gradient x y).2.1]
  ring

theorem origin_values : strainA 0 0 = 1 ∧ strainB 0 0 = 0 ∧ vorticityZ 0 0 = 1 := by
  norm_num [strainA, strainB, vorticityZ]

theorem hasDerivAt_ax_origin :
    HasDerivAt (fun s ↦ ax s 0) (-1 : ℝ) 0 := by
  have h := hasDerivAt_trig_formula (fun s ↦ ax s 0) (0) (-1) (9) 0
    (by intro s; simp only [ax, cos_zero]; ring)
  simpa using h

theorem hasDerivAt_ay_origin :
    HasDerivAt (fun s ↦ ay 0 s) (-1 : ℝ) 0 := by
  have h := hasDerivAt_trig_formula (fun s ↦ ay 0 s) (0) (-1) (0) 0
    (by intro s; simp only [ay, sin_zero, cos_zero]; ring)
  simpa using h

theorem hasDerivAt_bx_origin :
    HasDerivAt (fun s ↦ bx s 0) (-1 / 4 : ℝ) 0 := by
  have h := hasDerivAt_trig_formula (fun s ↦ bx s 0) (0) (-1 / 4) (-4) 0
    (by intro s; dsimp [bx]; ring)
  simpa using h

theorem hasDerivAt_byy_origin :
    HasDerivAt (fun s ↦ byy 0 s) (1 / 4 : ℝ) 0 := by
  have h := hasDerivAt_trig_formula (fun s ↦ byy 0 s) (0) (1 / 4) (-8) 0
    (by intro s; dsimp [byy]; ring)
  simpa using h

theorem hasDerivAt_wx_origin :
    HasDerivAt (fun s ↦ wx s 0) (-1 / 2 : ℝ) 0 := by
  have h := hasDerivAt_trig_formula (fun s ↦ wx s 0) (0) (-1 / 2) (-8) 0
    (by intro s; simp only [wx, sin_zero]; ring)
  simpa using h

theorem hasDerivAt_wy_origin :
    HasDerivAt (fun s ↦ wy 0 s) (-1 / 2 : ℝ) 0 := by
  have h := hasDerivAt_trig_formula (fun s ↦ wy 0 s) (0) (-1 / 2) (-2) 0
    (by intro s; simp only [wy, sin_zero, cos_zero]; ring)
  simpa using h

def defect (x y : ℝ) : ℝ := planarDefect (strainA x y) (strainB x y) (vorticityZ x y)

theorem defect_xx_origin : deriv (deriv (fun x ↦ defect x 0)) 0 = -146 := by
  have h := hasDerivAt_deriv_planarDefect_at_normalized
    (fun x ↦ strainA x 0) (fun x ↦ strainB x 0) (fun x ↦ vorticityZ x 0)
    (fun x ↦ ax x 0) (fun x ↦ bx x 0) (fun x ↦ wx x 0)
    (-1) (-1 / 4) (-1 / 2) 0
    (fun x ↦ hasDerivAt_strainA_x x 0) (fun x ↦ hasDerivAt_strainB_x x 0)
    (fun x ↦ hasDerivAt_vorticityZ_x x 0)
    hasDerivAt_ax_origin hasDerivAt_bx_origin hasDerivAt_wx_origin
    origin_values.1 origin_values.2.1 origin_values.2.2
  have hd := h.deriv
  norm_num [ax, bx, wx] at hd
  exact hd

theorem defect_yy_origin : deriv (deriv (fun y ↦ defect 0 y)) 0 = 70 := by
  have h := hasDerivAt_deriv_planarDefect_at_normalized
    (fun y ↦ strainA 0 y) (fun y ↦ strainB 0 y) (fun y ↦ vorticityZ 0 y)
    (fun y ↦ ay 0 y) (fun y ↦ byy 0 y) (fun y ↦ wy 0 y)
    (-1) (1 / 4) (-1 / 2) 0
    (fun y ↦ hasDerivAt_strainA_y 0 y) (fun y ↦ hasDerivAt_strainB_y 0 y)
    (fun y ↦ hasDerivAt_vorticityZ_y 0 y)
    hasDerivAt_ay_origin hasDerivAt_byy_origin hasDerivAt_wy_origin
    origin_values.1 origin_values.2.1 origin_values.2.2
  have hd := h.deriv
  norm_num [ay, byy, wy] at hd
  exact hd

def planarLaplacian (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (deriv (fun s ↦ f s y)) x + deriv (deriv (fun s ↦ f x s)) y

theorem laplacian_defect_origin : planarLaplacian defect 0 0 = -76 := by
  rw [planarLaplacian, defect_xx_origin, defect_yy_origin]
  norm_num

theorem laplacian_strainA_origin : planarLaplacian strainA 0 0 = -2 := by
  have hx : deriv (fun s ↦ strainA s 0) = fun s ↦ ax s 0 :=
    funext (fun s ↦ (hasDerivAt_strainA_x s 0).deriv)
  have hy : deriv (fun s ↦ strainA 0 s) = fun s ↦ ay 0 s :=
    funext (fun s ↦ (hasDerivAt_strainA_y 0 s).deriv)
  rw [planarLaplacian, hx, hy, hasDerivAt_ax_origin.deriv, hasDerivAt_ay_origin.deriv]
  norm_num

theorem laplacian_strainB_origin : planarLaplacian strainB 0 0 = 0 := by
  have hx : deriv (fun s ↦ strainB s 0) = fun s ↦ bx s 0 :=
    funext (fun s ↦ (hasDerivAt_strainB_x s 0).deriv)
  have hy : deriv (fun s ↦ strainB 0 s) = fun s ↦ byy 0 s :=
    funext (fun s ↦ (hasDerivAt_strainB_y 0 s).deriv)
  rw [planarLaplacian, hx, hy, hasDerivAt_bx_origin.deriv, hasDerivAt_byy_origin.deriv]
  norm_num

theorem laplacian_vorticityZ_origin : planarLaplacian vorticityZ 0 0 = -1 := by
  have hx : deriv (fun s ↦ vorticityZ s 0) = fun s ↦ wx s 0 :=
    funext (fun s ↦ (hasDerivAt_vorticityZ_x s 0).deriv)
  have hy : deriv (fun s ↦ vorticityZ 0 s) = fun s ↦ wy 0 s :=
    funext (fun s ↦ (hasDerivAt_vorticityZ_y 0 s).deriv)
  rw [planarLaplacian, hx, hy, hasDerivAt_wx_origin.deriv, hasDerivAt_wy_origin.deriv]
  norm_num

def actualDefect (x y : ℝ) : ℝ :=
  PancakeSpectralDefectEvolution.topSpectralDefect
    (planarStrain (strainA x y) (strainB x y)) (normalVorticity (vorticityZ x y))

theorem actualDefect_eq (x y : ℝ) (ha : 0 < strainA x y) :
    actualDefect x y = defect x y := topSpectralDefect_planar _ _ _ ha

theorem laplacian_actualDefect_origin : planarLaplacian actualDefect 0 0 = -76 := by
  have hx : (fun s ↦ actualDefect s 0) =ᶠ[𝓝 0] (fun s ↦ defect s 0) := by
    have hc := (hasDerivAt_strainA_x 0 0).continuousAt
    have hp : 0 < strainA 0 0 := by rw [origin_values.1]; norm_num
    filter_upwards [hc.eventually (lt_mem_nhds hp)] with s hs
    exact actualDefect_eq s 0 hs
  have hy : (fun s ↦ actualDefect 0 s) =ᶠ[𝓝 0] (fun s ↦ defect 0 s) := by
    have hc := (hasDerivAt_strainA_y 0 0).continuousAt
    have hp : 0 < strainA 0 0 := by rw [origin_values.1]; norm_num
    filter_upwards [hc.eventually (lt_mem_nhds hp)] with s hs
    exact actualDefect_eq 0 s hs
  rw [planarLaplacian, hx.deriv.deriv_eq, hy.deriv.deriv_eq,
    defect_xx_origin, defect_yy_origin]
  norm_num

/-- The instantaneous viscous rate is evaluated in the Laplacian direction
of the same physical strain and vorticity fields. -/
def viscousDefectRate (nu x y : ℝ) : ℝ :=
  planarDefectRate (strainA x y) (strainB x y) (vorticityZ x y)
    (nu * planarLaplacian strainA x y) (nu * planarLaplacian strainB x y)
    (nu * planarLaplacian vorticityZ x y)

theorem viscousDefectRate_origin (nu : ℝ) : viscousDefectRate nu 0 0 = -4 * nu := by
  rw [viscousDefectRate, origin_values.1, origin_values.2.1, origin_values.2.2,
    laplacian_strainA_origin, laplacian_strainB_origin, laplacian_vorticityZ_origin]
  simp [planarDefectRate]
  ring

/-- The Laplacian direction is realized as an actual differentiable
curve of strains and vorticities. Only its derivative at zero is used;
this affine jet is not asserted to be a heat solution for nonzero time. -/
def viscousJetDefect (nu t : ℝ) : ℝ :=
  PancakeSpectralDefectEvolution.topSpectralDefect
    (planarStrain (strainA 0 0 + t * (nu * planarLaplacian strainA 0 0))
      (strainB 0 0 + t * (nu * planarLaplacian strainB 0 0)))
    (normalVorticity (vorticityZ 0 0 + t * (nu * planarLaplacian vorticityZ 0 0)))

theorem hasDerivAt_viscousJetDefect (nu : ℝ) :
    HasDerivAt (viscousJetDefect nu) (-4 * nu) 0 := by
  have ha := (hasDerivAt_id (0 : ℝ)).mul_const (nu * planarLaplacian strainA 0 0)
    |>.const_add (strainA 0 0)
  have hb := (hasDerivAt_id (0 : ℝ)).mul_const (nu * planarLaplacian strainB 0 0)
    |>.const_add (strainB 0 0)
  have hw := (hasDerivAt_id (0 : ℝ)).mul_const (nu * planarLaplacian vorticityZ 0 0)
    |>.const_add (vorticityZ 0 0)
  have h := hasDerivAt_planarDefect _ _ _ _ _ _ 0 ha hb hw (by
    simp [origin_values.1, origin_values.2.1])
  have hd : HasDerivAt
      (fun t ↦ planarDefect
        (strainA 0 0 + t * (nu * planarLaplacian strainA 0 0))
        (strainB 0 0 + t * (nu * planarLaplacian strainB 0 0))
        (vorticityZ 0 0 + t * (nu * planarLaplacian vorticityZ 0 0))) (-4 * nu) 0 := by
    apply h.congr_deriv
    simpa only [viscousDefectRate, id_eq, zero_mul, add_zero, one_mul]
      using viscousDefectRate_origin nu
  apply hd.congr_of_eventuallyEq
  have hp : 0 < strainA 0 0 + (0 : ℝ) * (nu * planarLaplacian strainA 0 0) := by
    simp [origin_values.1]
  filter_upwards [ha.continuousAt.eventually (lt_mem_nhds hp)] with t ht
  exact topSpectralDefect_planar _ _ _ ht

/-- The actual spectral defect is not a pointwise heat subsolution solely
by virtue of incompressibility and strain/vorticity compatibility. This
does not assert growth of its spatial integral or a Navier--Stokes blowup. -/
theorem viscous_chainRule_production_origin (nu : ℝ) :
    viscousDefectRate nu 0 0 - nu * planarLaplacian actualDefect 0 0 = 72 * nu := by
  rw [viscousDefectRate_origin, laplacian_actualDefect_origin]
  ring

theorem viscous_chainRule_production_pos (nu : ℝ) (hnu : 0 < nu) :
    0 < viscousDefectRate nu 0 0 - nu * planarLaplacian actualDefect 0 0 := by
  rw [viscous_chainRule_production_origin]
  positivity

theorem velocity_periodic (x y : ℝ) :
    velocityX (x + 2 * π) y = velocityX x y ∧
    velocityX x (y + 2 * π) = velocityX x y ∧
    velocityY (x + 2 * π) y = velocityY x y ∧
    velocityY x (y + 2 * π) = velocityY x y := by
  simp [velocityX, velocityY, sin_add_two_pi, cos_add_two_pi]

end Mettapedia.FluidDynamics.NavierStokes.PancakePeriodicDiffusionWitness
