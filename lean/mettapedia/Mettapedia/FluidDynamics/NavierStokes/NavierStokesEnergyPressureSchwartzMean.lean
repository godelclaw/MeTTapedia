import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBasic

/-!
# Navier-Stokes Energy: Pressure-Schwartz Mean-Zero Lemmas

Semantic layer split from `NavierStokesEnergyPressureSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Concrete coordinate expansion of the Euclidean inner product on the
Navier-Stokes space `ℝ^3`. -/
theorem real_inner_eq_coord_sum (u c : NSSpace) :
    ⟪u, c⟫ = u nsCoord0 * c nsCoord0 +
      (u nsCoord1 * c nsCoord1 + u nsCoord2 * c nsCoord2) := by
  calc
    ⟪u, c⟫ = ∑ i : Fin 3, u i * c i := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    _ = u nsCoord0 * c nsCoord0 +
          (u nsCoord1 * c nsCoord1 + u nsCoord2 * c nsCoord2) := by
      simpa [nsCoord0, nsCoord1, nsCoord2, add_assoc] using
        (Fin.sum_univ_three (f := fun i : Fin 3 => u i * c i))

/-- A divergence-free Schwartz time slice has zero spatial mean in its `x₀`
component. This is the precise slice lemma needed to close the first explicit
nontrivial pressure class `p(t,x)=c*x₀`. -/
theorem integral_coord0_zero_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    ∫ x, (u t x) nsCoord0 ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  let x0 : NSSpace → ℝ := fun x => x nsCoord0
  let e0 : NSSpace := EuclideanSpace.single nsCoord0 (1 : ℝ)
  let e1 : NSSpace := EuclideanSpace.single nsCoord1 (1 : ℝ)
  let e2 : NSSpace := EuclideanSpace.single nsCoord2 (1 : ℝ)
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordFDeriv (i j : Fin 3) (x : NSSpace) :
      fderiv ℝ (coord i) x (EuclideanSpace.single j (1 : ℝ)) =
        fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply] using hproj
  have hx0_hasFDeriv (x : NSSpace) :
      HasFDerivAt x0 (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) x := by
    simpa [x0] using
      ((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).hasFDerivAt (x := x))
  have hx0_diff : Differentiable ℝ x0 := by
    intro x
    exact (hx0_hasFDeriv x).differentiableAt
  have hIntWeighted (i : Fin 3) :
      Integrable (fun x : NSSpace => x0 x * coord i x) := by
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (coord i)
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => x0 x * coord i x := by
      funext x
      simp [weighted, x0, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [← hWeighted]
    exact weighted.integrable
  have hIntWeightedDeriv (i : Fin 3) (v : NSSpace) :
      Integrable (fun x : NSSpace => x0 x * fderiv ℝ (coord i) x v) := by
    have hEq :
        (fun x : NSSpace => x0 x * fderiv ℝ (coord i) x v) =
          fun x : NSSpace => x0 x * (∂_{v} (coord i)) x := by
      funext x
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (∂_{v} (coord i))
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => x0 x * (∂_{v} (coord i)) x := by
      funext x
      simp [weighted, x0, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [hEq, ← hWeighted]
    exact weighted.integrable
  have hx0_e0 (x : NSSpace) : fderiv ℝ x0 x e0 = 1 := by
    rw [(hx0_hasFDeriv x).fderiv]
    simp [e0, nsCoord0]
  have hx0_e1 (x : NSSpace) : fderiv ℝ x0 x e1 = 0 := by
    rw [(hx0_hasFDeriv x).fderiv]
    simp [e1, nsCoord0, nsCoord1]
  have hx0_e2 (x : NSSpace) : fderiv ℝ x0 x e2 = 0 := by
    rw [(hx0_hasFDeriv x).fderiv]
    simp [e2, nsCoord0, nsCoord2]
  have hDivEq (x : NSSpace) :
      fderiv ℝ (coord nsCoord0) x e0 =
        -(fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2) := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun, Fin.sum_univ_three] at hx
    have hx' :
        fderiv ℝ (coord nsCoord0) x e0 +
            (fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2) = 0 := by
      rw [hCoordFDeriv nsCoord0 nsCoord0 x, hCoordFDeriv nsCoord1 nsCoord1 x,
        hCoordFDeriv nsCoord2 nsCoord2 x]
      simpa [e0, e1, e2, add_assoc] using hx
    exact eq_neg_of_add_eq_zero_left hx'
  have hIBP0 :
      ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume =
        - ∫ x, coord nsCoord0 x ∂volume := by
    have hIBP0raw :
        ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume =
          - ∫ x, fderiv ℝ x0 x e0 * coord nsCoord0 x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ x0 x e0 * coord nsCoord0 x) =
                fun x : NSSpace => coord nsCoord0 x := by
            funext x
            rw [hx0_e0 x]
            ring
          rw [hEq]
          exact (coord nsCoord0).integrable)
        (hIntWeightedDeriv nsCoord0 e0)
        (hIntWeighted nsCoord0)
        hx0_diff
        (fun x => (coord nsCoord0).differentiableAt)
    simpa [hx0_e0] using hIBP0raw
  have hIBP1 :
      ∫ x, x0 x * fderiv ℝ (coord nsCoord1) x e1 ∂volume = 0 := by
    have hIBP1raw :
        ∫ x, x0 x * fderiv ℝ (coord nsCoord1) x e1 ∂volume =
          - ∫ x, fderiv ℝ x0 x e1 * coord nsCoord1 x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ x0 x e1 * coord nsCoord1 x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [hx0_e1 x]
            simp
          rw [hEq]
          exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
        (hIntWeightedDeriv nsCoord1 e1)
        (hIntWeighted nsCoord1)
        hx0_diff
        (fun x => (coord nsCoord1).differentiableAt)
    simpa [hx0_e1] using hIBP1raw
  have hIBP2 :
      ∫ x, x0 x * fderiv ℝ (coord nsCoord2) x e2 ∂volume = 0 := by
    have hIBP2raw :
        ∫ x, x0 x * fderiv ℝ (coord nsCoord2) x e2 ∂volume =
          - ∫ x, fderiv ℝ x0 x e2 * coord nsCoord2 x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ x0 x e2 * coord nsCoord2 x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [hx0_e2 x]
            simp
          rw [hEq]
          exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
        (hIntWeightedDeriv nsCoord2 e2)
        (hIntWeighted nsCoord2)
        hx0_diff
        (fun x => (coord nsCoord2).differentiableAt)
    simpa [hx0_e2] using hIBP2raw
  have hCoord0Eq :
      (fun x : NSSpace => (u t x) nsCoord0) = coord nsCoord0 := by
    funext x
    rw [hslice x]
    exact hCoordEq nsCoord0 x
  have hIBP0' :
      ∫ x, coord nsCoord0 x ∂volume =
        - ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume := by
    have hneg := congrArg Neg.neg hIBP0
    simpa [neg_neg] using hneg.symm
  calc
    ∫ x, (u t x) nsCoord0 ∂volume = ∫ x, coord nsCoord0 x ∂volume := by
      rw [hCoord0Eq]
    _ = - ∫ x, x0 x * fderiv ℝ (coord nsCoord0) x e0 ∂volume := hIBP0'
    _ = ∫ x, -(x0 x * fderiv ℝ (coord nsCoord0) x e0) ∂volume := by
      rw [← integral_neg]
    _ = ∫ x, x0 x * (fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2) ∂volume := by
      congr 1
      funext x
      rw [hDivEq x]
      ring
    _ = ∫ x, x0 x * fderiv ℝ (coord nsCoord1) x e1 ∂volume +
          ∫ x, x0 x * fderiv ℝ (coord nsCoord2) x e2 ∂volume := by
      have hSplit :
          (fun x : NSSpace =>
            x0 x * (fderiv ℝ (coord nsCoord1) x e1 + fderiv ℝ (coord nsCoord2) x e2)) =
            (fun x : NSSpace => x0 x * fderiv ℝ (coord nsCoord1) x e1) +
              (fun x : NSSpace => x0 x * fderiv ℝ (coord nsCoord2) x e2) := by
        funext x
        simp [mul_add]
      rw [hSplit]
      simpa using
        integral_add
          (hIntWeightedDeriv nsCoord1 e1)
          (hIntWeightedDeriv nsCoord2 e2)
    _ = 0 := by rw [hIBP1, hIBP2]; ring

/-- A divergence-free Schwartz time slice has zero spatial mean in every
coordinate component. This is the correct pressure-side mean-zero theorem for
linear pressure classes on `ℝ^3`. -/
theorem integral_coord_zero_of_schwartzSlice_of_spatialDivergence_zero
    (u : NSVelocityField) (t : NSTime) (f : 𝓢(NSSpace, NSSpace))
    (hslice : ∀ x, u t x = f x)
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (k : Fin 3) :
    ∫ x, (u t x) k ∂volume = 0 := by
  let coord : Fin 3 → 𝓢(NSSpace, ℝ) := fun i =>
    SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.apply ℝ ℝ)
      (g := fun _ : NSSpace => (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
      (by fun_prop) f
  let xk : NSSpace → ℝ := fun x => x k
  let ek : NSSpace := EuclideanSpace.single k (1 : ℝ)
  let remainder : NSSpace → ℝ := fun x =>
    (Finset.univ.erase k).sum
      (fun i => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))
  have hsliceFun : (fun x : NSSpace => u t x) = (f : NSSpace → NSSpace) := funext hslice
  have hCoordEq (i : Fin 3) (x : NSSpace) : coord i x = (f x) i := by
    simp [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply]
  have hCoordFDeriv (i j : Fin 3) (x : NSSpace) :
      fderiv ℝ (coord i) x (EuclideanSpace.single j (1 : ℝ)) =
        fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) i := by
    have hproj :=
      congrArg
        (fun L : NSSpace →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ)))
        (((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp x
          (f.hasFDerivAt x)).fderiv)
    simpa [coord, SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_apply] using hproj
  have hxk_hasFDeriv (x : NSSpace) :
      HasFDerivAt xk (EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ) x := by
    simpa [xk] using
      ((EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ).hasFDerivAt (x := x))
  have hxk_diff : Differentiable ℝ xk := by
    intro x
    exact (hxk_hasFDeriv x).differentiableAt
  have hIntWeighted (i : Fin 3) :
      Integrable (fun x : NSSpace => xk x * coord i x) := by
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (coord i)
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => xk x * coord i x := by
      funext x
      simp [weighted, xk, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [← hWeighted]
    exact weighted.integrable
  have hIntWeightedDeriv (i : Fin 3) (v : NSSpace) :
      Integrable (fun x : NSSpace => xk x * fderiv ℝ (coord i) x v) := by
    have hEq :
        (fun x : NSSpace => xk x * fderiv ℝ (coord i) x v) =
          fun x : NSSpace => xk x * (∂_{v} (coord i)) x := by
      funext x
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    let weighted : 𝓢(NSSpace, ℝ) :=
      SchwartzMap.bilinLeftCLM
        (ContinuousLinearMap.mul ℝ ℝ)
        (g := (EuclideanSpace.proj k : NSSpace →L[ℝ] ℝ))
        (by fun_prop)
        (∂_{v} (coord i))
    have hWeighted :
        (weighted : NSSpace → ℝ) = fun x : NSSpace => xk x * (∂_{v} (coord i)) x := by
      funext x
      simp [weighted, xk, coord, SchwartzMap.bilinLeftCLM_apply]
      rw [mul_comm]
    rw [hEq, ← hWeighted]
    exact weighted.integrable
  have hxk_ek (x : NSSpace) : fderiv ℝ xk x ek = 1 := by
    rw [(hxk_hasFDeriv x).fderiv]
    simp [ek]
  have hxk_ei_zero (i : Fin 3) (hik : i ≠ k) (x : NSSpace) :
      fderiv ℝ xk x (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    rw [(hxk_hasFDeriv x).fderiv]
    simpa [eq_comm] using hik
  have hDivEq (x : NSSpace) :
      fderiv ℝ (coord k) x ek = - remainder x := by
    have hx : spatialDivergence u t x = 0 := hdiv x
    rw [spatialDivergence, spatialFDeriv, hsliceFun] at hx
    have hx' :
        (∑ i : Fin 3, fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ))) = 0 := by
      convert hx using 1
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hCoordFDeriv i i x
    have hsplit' :
        remainder x + fderiv ℝ (coord k) x ek = 0 := by
      have hsplit'' :
          (Finset.univ.erase k).sum
              (fun i => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ))) +
            fderiv ℝ (coord k) x (EuclideanSpace.single k (1 : ℝ)) = 0 := by
        rw [Finset.sum_erase_add (s := Finset.univ)
          (f := fun i : Fin 3 => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))
          (a := k) (by simp)]
        exact hx'
      simpa [remainder, ek] using hsplit''
    have hsplit :
        fderiv ℝ (coord k) x ek + remainder x = 0 := by
      simpa [add_comm] using hsplit'
    exact eq_neg_of_add_eq_zero_left hsplit
  have hIBPk :
      ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume =
        - ∫ x, coord k x ∂volume := by
    have hIBPkRaw :
        ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume =
          - ∫ x, fderiv ℝ xk x ek * coord k x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace => fderiv ℝ xk x ek * coord k x) =
                fun x : NSSpace => coord k x := by
            funext x
            rw [hxk_ek x]
            ring
          rw [hEq]
          exact (coord k).integrable)
        (hIntWeightedDeriv k ek)
        (hIntWeighted k)
        hxk_diff
        (fun x => (coord k).differentiableAt)
    simpa [hxk_ek] using hIBPkRaw
  have hIBPzero (i : Fin 3) (hik : i ≠ k) :
      ∫ x, xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume = 0 := by
    have hIBPRaw :
        ∫ x, xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume =
          - ∫ x, fderiv ℝ xk x (EuclideanSpace.single i (1 : ℝ)) * coord i x ∂volume := by
      exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (by
          have hEq :
              (fun x : NSSpace =>
                fderiv ℝ xk x (EuclideanSpace.single i (1 : ℝ)) * coord i x) =
                fun _ : NSSpace => 0 := by
            funext x
            rw [hxk_ei_zero i hik x]
            simp
          rw [hEq]
          exact integrable_zero NSSpace ℝ (volume : Measure NSSpace))
        (hIntWeightedDeriv i (EuclideanSpace.single i (1 : ℝ)))
        (hIntWeighted i)
        hxk_diff
        (fun x => (coord i).differentiableAt)
    simpa [hxk_ei_zero i hik] using hIBPRaw
  have hCoordkEq :
      (fun x : NSSpace => (u t x) k) = coord k := by
    funext x
    rw [hslice x]
    exact hCoordEq k x
  have hIBPk' :
      ∫ x, coord k x ∂volume =
        - ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume := by
    have hneg := congrArg Neg.neg hIBPk
    simpa [neg_neg] using hneg.symm
  calc
    ∫ x, (u t x) k ∂volume = ∫ x, coord k x ∂volume := by
      rw [hCoordkEq]
    _ = - ∫ x, xk x * fderiv ℝ (coord k) x ek ∂volume := hIBPk'
    _ = ∫ x, -(xk x * fderiv ℝ (coord k) x ek) ∂volume := by
      rw [← integral_neg]
    _ = ∫ x,
          xk x * remainder x ∂volume := by
      congr 1
      funext x
      rw [hDivEq x]
      ring
    _ = (Finset.univ.erase k).sum
          (fun i => ∫ x, xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)) ∂volume) := by
      have hSplit :
          (fun x : NSSpace => xk x * remainder x) =
            (fun x : NSSpace =>
              (Finset.univ.erase k).sum
                (fun i => xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))) := by
        have hSplit' :
            (fun x : NSSpace =>
              xk x *
                (Finset.univ.erase k).sum
                  (fun i => fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))) =
              (fun x : NSSpace =>
                (Finset.univ.erase k).sum
                  (fun i => xk x * fderiv ℝ (coord i) x (EuclideanSpace.single i (1 : ℝ)))) := by
          funext x
          rw [Finset.mul_sum]
        simpa [remainder] using hSplit'
      rw [hSplit, integral_finset_sum]
      intro i hi
      exact hIntWeightedDeriv i (EuclideanSpace.single i (1 : ℝ))
    _ = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact hIBPzero i (Finset.mem_erase.mp hi).1

end NavierStokes
end FluidDynamics
end Mettapedia
