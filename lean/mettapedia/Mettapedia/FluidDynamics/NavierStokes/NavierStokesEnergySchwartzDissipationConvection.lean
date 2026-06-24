import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyIdentities

/-!
# Navier-Stokes Energy: Schwartz Dissipation Convection Cancellation

Semantic layer split from `NavierStokesEnergySchwartzDissipation`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- A concrete Navier-Stokes time slice that agrees pointwise with a Schwartz
function has integrable convection energy pairing. -/
theorem integrable_convectionEnergyPairing_of_schwartzSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x) :
    Integrable (convectionEnergyPairing u t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hConvectionEq :
      convectionEnergyPairing u t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ := by
    funext x
    have hVec :
        f x = ∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      change (f x).ofLp j =
        (∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ)).ofLp j
      fin_cases j <;> rw [Fin.sum_univ_three] <;> simp [hCoordEq]
    rw [convectionEnergyPairing, spatialConvection, hslice x, spatialFDeriv, hsliceFun]
    rw [hVec, map_sum, inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [ContinuousLinearMap.map_smul, real_inner_smul_right]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫) := by
    refine ((SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (SchwartzMap.pairing (innerSL ℝ) f (∂_{EuclideanSpace.single i (1 : ℝ)} f))).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply, hCoordEq i x]
    rfl
  rw [hConvectionEq]
  simpa using integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i hi => hTermIntegrable i)

/-- A concrete Navier-Stokes time slice that agrees pointwise with a
divergence-free Schwartz function has vanishing convection energy integral. -/
theorem integral_convectionEnergyPairing_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, convectionEnergyPairing u t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  let normSq : 𝓢(NSSpace, ℝ) := SchwartzMap.pairing (innerSL ℝ) f f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordDeriv (i : Fin 3) (x : NSSpace) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
        (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i := by
    have hcoordFun : (coord i : NSSpace → ℝ) = fun y : NSSpace => (f y) i := by
      funext y
      simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    calc
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
          fderiv ℝ (fun y : NSSpace => (f y) i) x (EuclideanSpace.single i (1 : ℝ)) := by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoordFun]
      _ = fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) i := by
        change fderiv ℝ ((fun y : NSSpace => y i) ∘ (f : NSSpace → NSSpace)) x
            (EuclideanSpace.single i (1 : ℝ)) =
          fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) i
        simpa [ContinuousLinearMap.comp_apply] using hproj
      _ = (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i := by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hNormSqDeriv (i : Fin 3) (x : NSSpace) :
      ∂_{EuclideanSpace.single i (1 : ℝ)} normSq x =
        2 * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ := by
    have hNormSqEq :
        (normSq : NSSpace → ℝ) = fun y : NSSpace => ‖f y‖ ^ (2 : ℕ) := by
      funext y
      rw [SchwartzMap.pairing_apply_apply]
      change ⟪f y, f y⟫ = ‖f y‖ ^ (2 : ℕ)
      rw [real_inner_self_eq_norm_sq]
    have hnorm :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        ((f.hasFDerivAt x).norm_sq.fderiv)
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hNormSqEq]
    simpa [ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hnorm
  have hConvectionEq :
      convectionEnergyPairing u t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ := by
    funext x
    have hVec :
        f x = ∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      change (f x).ofLp j =
        (∑ i : Fin 3, coord i x • EuclideanSpace.single i (1 : ℝ)).ofLp j
      fin_cases j <;> rw [Fin.sum_univ_three] <;> simp [hCoordEq]
    rw [convectionEnergyPairing, spatialConvection, hslice x, spatialFDeriv, hsliceFun]
    rw [hVec, map_sum, inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [ContinuousLinearMap.map_smul, real_inner_smul_right]
    simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫) := by
    refine ((SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (SchwartzMap.pairing (innerSL ℝ) f (∂_{EuclideanSpace.single i (1 : ℝ)} f))).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply, hCoordEq i x]
    rfl
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x) := by
    refine ((SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        normSq).integrable).congr ?_
    filter_upwards with x
    rw [SchwartzMap.pairing_apply_apply]
    rfl
  have hDivEq (x : NSSpace) :
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x = 0 := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    convert hx using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hCoordDeriv i x
  calc
    ∫ x, convectionEnergyPairing u t x ∂volume
        = ∫ x,
            ∑ i : Fin 3,
              coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ ∂volume := by
            rw [hConvectionEq]
    _ = ∑ i : Fin 3,
          ∫ x, coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫ ∂volume := by
          rw [integral_finsetSum]
          intro i hi
          exact hTermIntegrable i
    _ = ∑ i : Fin 3,
          (1 / 2 : ℝ) *
            ∫ x, coord i x * ∂_{EuclideanSpace.single i (1 : ℝ)} normSq x ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hEq :
              (fun x : NSSpace =>
                coord i x * ⟪f x, ∂_{EuclideanSpace.single i (1 : ℝ)} f x⟫) =
                fun x : NSSpace =>
                  (1 / 2 : ℝ) *
                    (coord i x * ∂_{EuclideanSpace.single i (1 : ℝ)} normSq x) := by
            funext x
            rw [hNormSqDeriv i x]
            ring
          rw [hEq, integral_const_mul]
    _ = ∑ i : Fin 3,
          (-(1 / 2 : ℝ)) *
            ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x ∂volume := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) normSq (EuclideanSpace.single i (1 : ℝ))]
          ring
    _ = (-(1 / 2 : ℝ)) *
          ∑ i : Fin 3,
            ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x ∂volume := by
          rw [← Finset.mul_sum]
    _ = (-(1 / 2 : ℝ)) *
          ∫ x,
            ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * normSq x ∂volume := by
      congr 2
      rw [integral_finsetSum]
      intro i hi
      exact hDivTermIntegrable i
    _ = (-(1 / 2 : ℝ)) * ∫ x, (0 : ℝ) ∂volume := by
          congr 2
          funext x
          rw [← Finset.sum_mul, hDivEq x]
          simp
    _ = 0 := by simp

/-- The nonlinear transport energy integral vanishes for a two-profile Schwartz
superposition whenever the combined velocity field is divergence-free on every
time slice. -/
theorem integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (hdiv :
      ∀ t x,
        spatialDivergence (fun s y => a s • f y + b s • g y) t x = 0) :
    ∀ t,
      ∫ x, convectionEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume = 0 := by
  intro t
  apply integral_convectionEnergyPairing_of_schwartzSlice_of_spatialDivergence_zero
    (u := fun s y => a s • f y + b s • g y)
    (t := t)
    (f := (a t) • f + (b t) • g)
  · intro x
    rfl
  · intro x
    exact hdiv t x

/-- The nonlinear transport energy integral vanishes for a two-profile Schwartz
superposition once both spatial profiles are divergence-free in the standard
coordinate basis of `ℝ^3`. -/
theorem integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_divergenceFree
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace))
    (hfdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i = 0)
    (hgdiv : ∀ x,
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} g x) i = 0) :
    ∀ t,
      ∫ x, convectionEnergyPairing (fun s y => a s • f y + b s • g y) t x ∂volume = 0 := by
  apply integral_convectionEnergyPairing_of_add_scalar_smul_schwartz_of_spatialDivergence_zero
    (a := a) (b := b) (f := f) (g := g)
  intro t x
  let uf : NSVelocityField := fun _ y => f y
  let ug : NSVelocityField := fun _ y => g y
  have huf : spatialDivergence uf t x = 0 := by
    simpa [uf, spatialDivergence, spatialFDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      hfdiv x
  have hug : spatialDivergence ug t x = 0 := by
    simpa [ug, spatialDivergence, spatialFDeriv, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      hgdiv x
  have hsum :
      spatialDivergence ((a t) • uf + (b t) • ug) t x =
        spatialDivergence ((a t) • uf) t x + spatialDivergence ((b t) • ug) t x := by
    apply spatialDivergence_add
    · simpa [uf] using (show DifferentiableAt ℝ (fun y : NSSpace => a t • f y) x by fun_prop)
    · simpa [ug] using (show DifferentiableAt ℝ (fun y : NSSpace => b t • g y) x by fun_prop)
  change spatialDivergence ((a t) • uf + (b t) • ug) t x = 0
  rw [hsum, spatialDivergence_const_smul, spatialDivergence_const_smul, huf, hug]
  simp

end NavierStokes
end FluidDynamics
end Mettapedia
