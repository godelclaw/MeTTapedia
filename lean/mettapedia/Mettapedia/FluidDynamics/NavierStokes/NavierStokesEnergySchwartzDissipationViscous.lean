import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyIdentities

/-!
# Navier-Stokes Energy: Schwartz Dissipation Viscous Pairing

Semantic layer split from `NavierStokesEnergySchwartzDissipation`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Corrected Schwartz-slice viscous pairing identity:

`∫ u · Δu = - ∫ Σᵢ |∂ᵢ u|²`.

This is the exact integration-by-parts statement produced by mathlib's
Schwartz-space Laplacian machinery on `ℝ^3`, and it targets the coordinatewise
gradient square rather than the operator norm of the full derivative. -/
theorem schwartz_integral_laplacianEnergyPairing_eq_neg_coordinateEnstrophy
    (f : 𝓢(NSSpace, NSSpace)) :
    ∫ x, ⟪f x, Δ f x⟫ ∂volume =
      - ∫ x, ∑ i : NSStdBasisIndex, ‖∂_{nsStdBasis i} f x‖ ^ (2 : ℕ) ∂volume := by
  let b : OrthonormalBasis NSStdBasisIndex ℝ NSSpace := nsStdBasis
  have hIntSecond :
      ∀ i : NSStdBasisIndex, Integrable (fun x : NSSpace => ⟪f x, ∂_{b i} (∂_{b i} f) x⟫) := by
    intro i
    refine ((SchwartzMap.pairing (innerSL ℝ) f (∂_{b i} (∂_{b i} f))).integrable).congr ?_
    filter_upwards with x
    show ((innerSL ℝ) (f x)) ((∂_{b i} (∂_{b i} f)) x) =
      ⟪f x, (∂_{b i} (∂_{b i} f)) x⟫
    rfl
  have hIntDiag :
      ∀ i : NSStdBasisIndex, Integrable (fun x : NSSpace => ‖(∂_{b i} f) x‖ ^ (2 : ℕ)) := by
    intro i
    have hPair :
        Integrable
          (⇑(((SchwartzMap.pairing (innerSL ℝ)) (∂_{b i} f)) (∂_{b i} f)))
          (volume : Measure NSSpace) := by
      exact
        ((SchwartzMap.pairing (innerSL ℝ) (∂_{b i} f) (∂_{b i} f)).integrable
          (μ := (volume : Measure NSSpace)))
    have hEq :
        (⇑(((SchwartzMap.pairing (innerSL ℝ)) (∂_{b i} f)) (∂_{b i} f))) =
          fun x : NSSpace => ‖(∂_{b i} f) x‖ ^ (2 : ℕ) := by
      funext x
      rw [SchwartzMap.pairing_apply_apply]
      change ⟪(∂_{b i} f) x, (∂_{b i} f) x⟫ = ‖(∂_{b i} f) x‖ ^ (2 : ℕ)
      rw [real_inner_self_eq_norm_sq]
    rw [← hEq]
    exact hPair
  have hIBP :
      ∀ i : NSStdBasisIndex,
        ∫ x, ⟪f x, (∂_{b i} (∂_{b i} f)) x⟫ ∂volume =
          - ∫ x, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
    intro i
    have hRaw :
        ∫ x, ((innerSL ℝ) (f x)) ((∂_{b i} (∂_{b i} f)) x) ∂volume =
          - ∫ x, ((innerSL ℝ) ((∂_{b i} f) x)) ((∂_{b i} f) x) ∂volume := by
      exact
        (SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
        (μ := (volume : Measure NSSpace))
        f (∂_{b i} f) (innerSL ℝ) (b i))
    have hLeft :
        (fun x : NSSpace => ((innerSL ℝ) (f x)) ((∂_{b i} (∂_{b i} f)) x)) =
          fun x : NSSpace => ⟪f x, (∂_{b i} (∂_{b i} f)) x⟫ := by
      funext x
      rfl
    have hRight :
        (fun x : NSSpace => ((innerSL ℝ) ((∂_{b i} f) x)) ((∂_{b i} f) x)) =
          fun x : NSSpace => ‖(∂_{b i} f) x‖ ^ (2 : ℕ) := by
      funext x
      change ⟪(∂_{b i} f) x, (∂_{b i} f) x⟫ = ‖(∂_{b i} f) x‖ ^ (2 : ℕ)
      rw [real_inner_self_eq_norm_sq]
    rw [hLeft, hRight] at hRaw
    exact hRaw
  have hLapExpand :
      ∫ x, ⟪f x, Δ f x⟫ ∂volume =
        ∫ x, ∑ i : NSStdBasisIndex, ⟪f x, ∂_{b i} (∂_{b i} f) x⟫ ∂volume := by
    rw [SchwartzMap.laplacian_eq_sum b f]
    simp [inner_sum]
  calc
    ∫ x, ⟪f x, Δ f x⟫ ∂volume
        = ∫ x, ∑ i : NSStdBasisIndex, ⟪f x, ∂_{b i} (∂_{b i} f) x⟫ ∂volume := hLapExpand
    _ = ∑ i : NSStdBasisIndex, ∫ x, ⟪f x, ∂_{b i} (∂_{b i} f) x⟫ ∂volume := by
      rw [integral_finsetSum]
      intro i hi
      exact hIntSecond i
    _ = ∑ i : NSStdBasisIndex, - ∫ x, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hIBP i
    _ = - ∑ i : NSStdBasisIndex, ∫ x, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = - ∫ x, ∑ i : NSStdBasisIndex, ‖(∂_{b i} f) x‖ ^ (2 : ℕ) ∂volume := by
      congr 1
      rw [integral_finsetSum]
      intro i hi
      exact hIntDiag i
    _ = - ∫ x, ∑ i : NSStdBasisIndex, ‖∂_{b i} f x‖ ^ (2 : ℕ) ∂volume := by
          rfl

/-- A concrete Navier-Stokes time slice that agrees pointwise with a Schwartz
function satisfies the corrected viscous pairing identity. -/
theorem coordinateViscousEnergyPairingFormula_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x) :
    ∫ x, laplacianEnergyPairing u t x ∂volume = -coordinateEnstrophyAt u t := by
  let b : OrthonormalBasis NSStdBasisIndex ℝ NSSpace := nsStdBasis
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hLhs :
      laplacianEnergyPairing u t = fun x : NSSpace => ⟪f x, Δ f x⟫ := by
    funext x
    have hLap : spatialLaplacian u t x = Δ f x := by
      rw [spatialLaplacian, hsliceFun]
      exact (SchwartzMap.laplacian_apply f x).symm
    rw [laplacianEnergyPairing, hslice x, hLap]
  have hRhs :
      coordinateEnstrophyDensity u t =
        fun x : NSSpace => ∑ i : NSStdBasisIndex, ‖∂_{b i} f x‖ ^ (2 : ℕ) := by
    funext x
    simp only [coordinateEnstrophyDensity]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [spatialFDeriv, hsliceFun]
    rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [hLhs, coordinateEnstrophyAt, hRhs]
  exact schwartz_integral_laplacianEnergyPairing_eq_neg_coordinateEnstrophy f

/-- The corrected viscous pairing seam holds for two-profile scalar Schwartz
superpositions `u(t,x)=a(t)•f(x)+b(t)•g(x)`. This matches the same nontrivial
finite-energy class where the derivative-under-the-integral seam has already
been proved. -/
theorem CoordinateViscousEnergyPairingFormula_of_add_scalar_smul_schwartz
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) :
    CoordinateViscousEnergyPairingFormula (fun s y => a s • f y + b s • g y) := by
  intro t
  exact
    coordinateViscousEnergyPairingFormula_of_schwartzSlice
      (u := fun s y => a s • f y + b s • g y)
      (t := t)
      (f := (a t) • f + (b t) • g)
      (hslice := by
        intro x
        rfl)

/-- A concrete Navier-Stokes time slice that agrees pointwise with a Schwartz
function has integrable viscous energy pairing. -/
theorem integrable_laplacianEnergyPairing_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x) :
    Integrable (laplacianEnergyPairing u t) := by
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hPair :
      laplacianEnergyPairing u t = fun x : NSSpace => ⟪f x, Δ f x⟫ := by
    funext x
    have hLap : spatialLaplacian u t x = Δ f x := by
      rw [spatialLaplacian, hsliceFun]
      exact (SchwartzMap.laplacian_apply f x).symm
    rw [laplacianEnergyPairing, hslice x, hLap]
  rw [hPair]
  simpa [SchwartzMap.pairing_apply_apply] using integrable_inner_schwartz f (Δ f)

end NavierStokes
end FluidDynamics
end Mettapedia
