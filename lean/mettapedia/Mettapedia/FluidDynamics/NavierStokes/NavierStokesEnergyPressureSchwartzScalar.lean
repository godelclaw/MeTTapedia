import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBasic

/-!
# Navier-Stokes Energy: Pressure-Schwartz Scalar Schwartz Pressures

Semantic layer split from `NavierStokesEnergyPressureSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Against a scalar-multiple Schwartz pressure profile `p(t,x) = ρ(t) * q(x)`,
the pressure energy pairing is the coordinatewise velocity-pressure pairing with
the spatial derivatives of `q`. -/
theorem pressureEnergyPairing_scalar_smul_schwartzPressure
    (u : NSVelocityField) (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ)) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t =
      fun x : NSSpace =>
        ρ t *
          ∑ i : Fin 3,
            (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : NSSpace => q y) x := q.differentiableAt
  have hgradq :
      HasGradientAt (fun y : NSSpace => q y) (gradient (fun y : NSSpace => q y) x) x :=
    hdiff.hasGradientAt
  have hgrad :
      spatialPressureGradient (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x =
        (ρ t) • gradient (fun y : NSSpace => q y) x := by
    unfold spatialPressureGradient
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [smul_eq_mul] using (hgradq.hasFDerivAt.const_mul (ρ t))
  have hGradCoord (i : Fin 3) :
      (gradient (fun y : NSSpace => q y) x) i =
        (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    have h :=
      hgradq.fderiv_apply (𝕜 := ℝ) (y := EuclideanSpace.single i (1 : ℝ))
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    simpa [EuclideanSpace.inner_single_right] using h.symm
  have hInnerRaw :
      ⟪u t x, gradient (fun y : NSSpace => q y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (gradient (fun y : NSSpace => q y) x) i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hInner :
      ⟪u t x, gradient (fun y : NSSpace => q y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    rw [hInnerRaw]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact congrArg (fun z : ℝ => (u t x) i * z) (hGradCoord i)
  rw [pressureEnergyPairing, hgrad, real_inner_smul_right, hInner]

/-- A Schwartz time slice has integrable pressure energy pairing against a
scalar-multiple Schwartz pressure profile `p(t,x) = ρ(t) * q(x)`. -/
theorem integrable_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x) :
    Integrable (pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t =
        fun x : NSSpace =>
          ρ t *
            ∑ i : Fin 3,
              coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    funext x
    rw [pressureEnergyPairing_scalar_smul_schwartzPressure]
    apply congrArg (fun z : ℝ => ρ t * z)
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} q)).integrable
  rw [hPair]
  have hSum :
      Integrable
        (fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x) := by
    simpa using
      integrable_finset_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hTermIntegrable i)
  exact hSum.const_mul (ρ t)

/-- A divergence-free Schwartz velocity slice has vanishing pressure energy
integral against a scalar-multiple Schwartz pressure profile
`p(t,x) = ρ(t) * q(x)`. -/
theorem integral_pressureEnergyPairing_of_schwartzSlice_scalarSchwartzPressure_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (ρ : NSTime → ℝ) (q : 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t x ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordDeriv (i : Fin 3) (x : NSSpace) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x =
        (∂_{EuclideanSpace.single i (1 : ℝ)} f x) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single i (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hproj
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => ρ s * q y) t =
        fun x : NSSpace =>
          ρ t *
            ∑ i : Fin 3,
              coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x := by
    funext x
    rw [pressureEnergyPairing_scalar_smul_schwartzPressure]
    apply congrArg (fun z : ℝ => ρ t * z)
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} q)).integrable
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        q).integrable
  have hDivEq (x : NSSpace) :
      ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x = 0 := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    convert hx using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hCoordDeriv i x
  rw [hPair]
  calc
    ∫ x, ρ t * ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x ∂volume
        = ρ t *
            ∫ x, ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x ∂volume := by
          rw [integral_const_mul]
    _ = ρ t *
          ∑ i : Fin 3,
            ∫ x, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} q) x ∂volume := by
          congr 1
          rw [integral_finset_sum]
          intro i hi
          exact hTermIntegrable i
    _ = ρ t *
          ∑ i : Fin 3,
            (-∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x ∂volume) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) q (EuclideanSpace.single i (1 : ℝ))]
    _ = -(ρ t) *
          ∑ i : Fin 3,
            ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x ∂volume := by
          rw [Finset.sum_neg_distrib]
          ring
    _ = -(ρ t) *
          ∫ x,
            ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q x ∂volume := by
          congr 2
          rw [integral_finset_sum]
          intro i hi
          exact hDivTermIntegrable i
    _ = -(ρ t) * ∫ x, (0 : ℝ) ∂volume := by
          congr 2
          funext x
          rw [← Finset.sum_mul, hDivEq x]
          simp
    _ = 0 := by simp

end NavierStokes
end FluidDynamics
end Mettapedia
