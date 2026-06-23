import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyPressureSchwartzMean

/-!
# Navier-Stokes Energy: Pressure-Schwartz Linear Pressures

Semantic layer split from `NavierStokesEnergyPressureSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- A Schwartz time slice has integrable pressure energy pairing against the
linear pressure field `p(t,x) = ⟪c, x⟫`. -/
theorem integrable_pressureEnergyPairing_linear_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (c : NSSpace) (hslice : ∀ x, u t x = f x) :
    Integrable (pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t =
        fun x : NSSpace =>
          coord nsCoord0 x * c nsCoord0 +
            (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2) := by
    funext x
    rw [pressureEnergyPairing_linear]
    change ⟪u t x, c⟫ =
      coord nsCoord0 x * c nsCoord0 +
        (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2)
    rw [hslice x, real_inner_eq_coord_sum]
    rw [hCoordEq nsCoord0 x, hCoordEq nsCoord1 x, hCoordEq nsCoord2 x]
  rw [hPair]
  have h0 : Integrable (fun x : NSSpace => coord nsCoord0 x * c nsCoord0) := by
    simpa [mul_comm] using (coord nsCoord0).integrable.const_mul (c nsCoord0)
  have h1 : Integrable (fun x : NSSpace => coord nsCoord1 x * c nsCoord1) := by
    simpa [mul_comm] using (coord nsCoord1).integrable.const_mul (c nsCoord1)
  have h2 : Integrable (fun x : NSSpace => coord nsCoord2 x * c nsCoord2) := by
    simpa [mul_comm] using (coord nsCoord2).integrable.const_mul (c nsCoord2)
  exact h0.add (h1.add h2)

/-- A divergence-free Schwartz time slice has vanishing pressure energy
integral against any linear pressure field `p(t,x) = ⟪c, x⟫`. -/
theorem integral_pressureEnergyPairing_linear_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (c : NSSpace) (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun _ : NSTime => fun y : NSSpace => ⟪c, y⟫) t =
        fun x : NSSpace =>
          coord nsCoord0 x * c nsCoord0 +
            (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2) := by
    funext x
    rw [pressureEnergyPairing_linear]
    change ⟪u t x, c⟫ =
      coord nsCoord0 x * c nsCoord0 +
        (coord nsCoord1 x * c nsCoord1 + coord nsCoord2 x * c nsCoord2)
    rw [hslice x, real_inner_eq_coord_sum]
    rw [hCoordEq nsCoord0 x, hCoordEq nsCoord1 x, hCoordEq nsCoord2 x]
  have h0 : Integrable (fun x : NSSpace => coord nsCoord0 x * c nsCoord0) := by
    simpa [mul_comm] using (coord nsCoord0).integrable.const_mul (c nsCoord0)
  have h1 : Integrable (fun x : NSSpace => coord nsCoord1 x * c nsCoord1) := by
    simpa [mul_comm] using (coord nsCoord1).integrable.const_mul (c nsCoord1)
  have h2 : Integrable (fun x : NSSpace => coord nsCoord2 x * c nsCoord2) := by
    simpa [mul_comm] using (coord nsCoord2).integrable.const_mul (c nsCoord2)
  have hCoordU (k : Fin 3) :
      (fun x : NSSpace => coord k x) = fun x : NSSpace => (u t x) k := by
    funext x
    rw [hCoordEq k x, ← hslice x]
  have hIntCoordZero (k : Fin 3) : ∫ x, coord k x ∂volume = 0 := by
    rw [hCoordU k]
    exact integral_coord_zero_of_schwartzSlice_of_spatialDivergence_zero
      (u := u) (t := t) (f := f) (hslice := hslice) (hdiv := hdiv) (k := k)
  have hAdd03 :
      ∫ x, coord nsCoord0 x * c nsCoord0 +
          ((coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2) ∂volume =
        ∫ x, coord nsCoord0 x * c nsCoord0 ∂volume +
          ∫ x, (coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2 ∂volume := by
    simpa using integral_add h0 (h1.add h2)
  have hAdd12 :
      ∫ x, (coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2 ∂volume =
        ∫ x, coord nsCoord1 x * c nsCoord1 ∂volume +
          ∫ x, coord nsCoord2 x * c nsCoord2 ∂volume := by
    simpa using integral_add h1 h2
  have hConst0 :
      ∫ x, coord nsCoord0 x * c nsCoord0 ∂volume =
        c nsCoord0 * ∫ x, coord nsCoord0 x ∂volume := by
    simpa [mul_comm] using
      integral_const_mul (c nsCoord0) (fun x : NSSpace => coord nsCoord0 x)
  have hConst1 :
      ∫ x, coord nsCoord1 x * c nsCoord1 ∂volume =
        c nsCoord1 * ∫ x, coord nsCoord1 x ∂volume := by
    simpa [mul_comm] using
      integral_const_mul (c nsCoord1) (fun x : NSSpace => coord nsCoord1 x)
  have hConst2 :
      ∫ x, coord nsCoord2 x * c nsCoord2 ∂volume =
        c nsCoord2 * ∫ x, coord nsCoord2 x ∂volume := by
    simpa [mul_comm] using
      integral_const_mul (c nsCoord2) (fun x : NSSpace => coord nsCoord2 x)
  rw [hPair]
  calc
    ∫ x, coord nsCoord0 x * c nsCoord0 +
        ((coord nsCoord1 x * c nsCoord1) + coord nsCoord2 x * c nsCoord2) ∂volume =
      ∫ x, coord nsCoord0 x * c nsCoord0 ∂volume +
        (∫ x, coord nsCoord1 x * c nsCoord1 ∂volume +
          ∫ x, coord nsCoord2 x * c nsCoord2 ∂volume) := by
        rw [hAdd03, hAdd12]
    _ = c nsCoord0 * ∫ x, coord nsCoord0 x ∂volume +
        (c nsCoord1 * ∫ x, coord nsCoord1 x ∂volume +
          c nsCoord2 * ∫ x, coord nsCoord2 x ∂volume) := by
        rw [hConst0, hConst1, hConst2]
    _ = 0 := by
        rw [hIntCoordZero nsCoord0, hIntCoordZero nsCoord1, hIntCoordZero nsCoord2]
        simp

end NavierStokes
end FluidDynamics
end Mettapedia
