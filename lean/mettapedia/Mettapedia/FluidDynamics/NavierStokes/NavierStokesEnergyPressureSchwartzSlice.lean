import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBasic

/-!
# Navier-Stokes Energy: Pressure-Schwartz Time-Indexed Schwartz Slices

Semantic layer split from `NavierStokesEnergyPressureSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- If each fixed-time pressure slice is Schwartz, then the pressure energy
pairing has the expected coordinate expansion against the spatial derivatives
of that slice. -/
theorem pressureEnergyPairing_schwartzPressureSlice
    (u : NSVelocityField) (q : NSTime → 𝓢(NSSpace, ℝ)) (t : NSTime) :
    pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t =
      fun x : NSSpace =>
        ∑ i : Fin 3, (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : NSSpace => q t y) x := (q t).differentiableAt
  have hgradq :
      HasGradientAt (fun y : NSSpace => q t y) (gradient (fun y : NSSpace => q t y) x) x :=
    hdiff.hasGradientAt
  have hgrad :
      spatialPressureGradient (fun s : NSTime => fun y : NSSpace => q s y) t x =
        gradient (fun y : NSSpace => q t y) x := by
    rfl
  have hGradCoord (i : Fin 3) :
      (gradient (fun y : NSSpace => q t y) x) i =
        (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    have h :=
      hgradq.fderiv_apply (𝕜 := ℝ) (y := EuclideanSpace.single i (1 : ℝ))
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    simpa [EuclideanSpace.inner_single_right] using h.symm
  have hInnerRaw :
      ⟪u t x, gradient (fun y : NSSpace => q t y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (gradient (fun y : NSSpace => q t y) x) i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hInner :
      ⟪u t x, gradient (fun y : NSSpace => q t y) x⟫ =
        ∑ i : Fin 3, (u t x) i * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    rw [hInnerRaw]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact congrArg (fun z : ℝ => (u t x) i * z) (hGradCoord i)
  rw [pressureEnergyPairing, hgrad, hInner]

/-- A Schwartz velocity time slice has integrable pressure energy pairing
against any time-indexed Schwartz pressure slice. -/
theorem integrable_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (q : NSTime → 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x) :
    Integrable (pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t) := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hPair :
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    rw [pressureEnergyPairing_schwartzPressureSlice]
    funext x
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (q t))).integrable
  rw [hPair]
  exact integrable_finset_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hTermIntegrable i)

/-- A divergence-free Schwartz velocity time slice has zero pressure work
against any time-indexed Schwartz pressure slice. -/
theorem integral_pressureEnergyPairing_of_schwartzSlice_schwartzPressureSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (q : NSTime → 𝓢(NSSpace, ℝ))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t x ∂volume = 0 := by
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
      pressureEnergyPairing u (fun s : NSTime => fun y : NSSpace => q s y) t =
        fun x : NSSpace =>
          ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x := by
    rw [pressureEnergyPairing_schwartzPressureSlice]
    funext x
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hslice x]
    simp [hCoordEq i x]
  have hTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (coord i)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (q t))).integrable
  have hDivTermIntegrable (i : Fin 3) :
      Integrable
        (fun x : NSSpace =>
          (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x) := by
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply] using
      (SchwartzMap.pairing
        (ContinuousLinearMap.mul ℝ ℝ)
        (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i))
        (q t)).integrable
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
    ∫ x, ∑ i : Fin 3, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x ∂volume
        = ∑ i : Fin 3,
            ∫ x, coord i x * (∂_{EuclideanSpace.single i (1 : ℝ)} (q t)) x ∂volume := by
          rw [integral_finset_sum]
          intro i hi
          exact hTermIntegrable i
    _ = ∑ i : Fin 3,
          (-∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x ∂volume) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
            (coord i) (q t) (EuclideanSpace.single i (1 : ℝ))]
    _ = -∑ i : Fin 3,
          ∫ x, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x ∂volume := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x,
          ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x ∂volume := by
          congr 1
          rw [integral_finset_sum]
          intro i hi
          exact hDivTermIntegrable i
    _ = -∫ x, (0 : ℝ) ∂volume := by
          congr 1
          have hFun :
              (fun x : NSSpace =>
                ∑ i : Fin 3, (∂_{EuclideanSpace.single i (1 : ℝ)} (coord i)) x * q t x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [← Finset.sum_mul, hDivEq x]
            simp
          rw [hFun]
    _ = 0 := by simp

end NavierStokes
end FluidDynamics
end Mettapedia
