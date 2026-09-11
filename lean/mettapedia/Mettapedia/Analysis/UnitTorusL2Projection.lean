import Mettapedia.Analysis.L2IntegralEnergy
import Mettapedia.Analysis.UnitTorusFourierEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite Fourier projection of L² torus fields

The inputs need only be square-integrable. The finite polynomial uses
their actual Fourier coefficients and converges in spatial L² energy.
The finite-vector version retains all components in one projection set.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.UnitTorusL2Projection

open MeasureTheory UnitAddTorus Filter
open scoped Topology

variable {d : Type*} [Fintype d]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projection (f : UnitAddTorus d → ℂ) (P : Finset (d → ℤ)) : C(UnitAddTorus d, ℂ) :=
  ∑ q ∈ P, mFourierCoeff f q • mFourier q

theorem toLp_projection (f : UnitAddTorus d → ℂ) (P : Finset (d → ℤ)) :
    (projection f P).toLp 2 volume ℂ = ∑ q ∈ P, mFourierCoeff f q • mFourierLp 2 q := by
  simp only [projection, map_sum, map_smul]

theorem tendsto_integral_projection_error (f : UnitAddTorus d → ℂ) (hf : MemLp f 2) :
    Tendsto (fun P : Finset (d → ℤ) ↦ ∫ x, ‖projection f P x - f x‖ ^ 2) atTop (𝓝 0) := by
  have hs : Tendsto (fun P : Finset (d → ℤ) ↦
      ∑ q ∈ P, mFourierCoeff (hf.toLp f) q • mFourierLp 2 q) atTop (𝓝 (hf.toLp f)) :=
    hasSum_mFourier_series_L2 (hf.toLp f)
  have hc (q : d → ℤ) := UnitTorusFourierEnergy.mFourierCoeff_congr_ae hf.coeFn_toLp q
  simp only [hc] at hs
  have he (P : Finset (d → ℤ)) : (∫ x, ‖projection f P x - f x‖ ^ 2) =
      ‖(∑ q ∈ P, mFourierCoeff f q • mFourierLp 2 q) - hf.toLp f‖ ^ 2 := by
    rw [← toLp_projection]
    have hp := (projection f P).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 2) (μ := volume)
    have hpeq : hp.toLp (projection f P) = (projection f P).toLp 2 volume ℂ := by
      apply Lp.ext
      filter_upwards [hp.coeFn_toLp, (projection f P).coeFn_toLp (p := 2) (𝕜 := ℂ) volume] with x hx hy
      rw [hx, hy]
    rw [← hpeq, L2IntegralEnergy.norm_sub_toLp_sq]
  have h := hs.sub_const (hf.toLp f)
  simp only [sub_self] at h
  simpa only [he, norm_zero, zero_pow (by decide : 2 ≠ 0)] using h.norm.pow 2

variable {ι : Type*} [Fintype ι]

def vectorProjection (f : UnitAddTorus d → EuclideanSpace ℂ ι) (P : Finset (d → ℤ)) :
    C(UnitAddTorus d, EuclideanSpace ℂ ι) :=
  ⟨fun x ↦ WithLp.toLp 2 (fun i ↦ projection (fun y ↦ f y i) P x),
    (PiLp.continuous_toLp 2 (fun _ : ι ↦ ℂ)).comp
      (continuous_pi (fun i ↦ (projection (fun y ↦ f y i) P).continuous))⟩

omit [Fintype ι] in
@[simp] theorem vectorProjection_apply (f : UnitAddTorus d → EuclideanSpace ℂ ι)
    (P : Finset (d → ℤ)) (x : UnitAddTorus d) (i : ι) :
    vectorProjection f P x i = projection (fun y ↦ f y i) P x := rfl

theorem mFourierCoeff_vector_apply (f : UnitAddTorus d → EuclideanSpace ℂ ι)
    (hf : Integrable f) (q : d → ℤ) (i : ι) :
    mFourierCoeff f q i = mFourierCoeff (fun x ↦ f x i) q := by
  have hi : Integrable (fun x ↦ mFourier (-q) x • f x) :=
    hf.bdd_smul 1 (mFourier (-q)).continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ ((mFourier (-q)).norm_coe_le_norm x).trans_eq mFourier_norm))
  exact eval_integral_piLp (fun j ↦ hi.eval_piLp j) i

theorem vectorProjection_eq_sum (f : UnitAddTorus d → EuclideanSpace ℂ ι)
    (hf : Integrable f) (P : Finset (d → ℤ)) (x : UnitAddTorus d) :
    vectorProjection f P x = ∑ q ∈ P, mFourier q x • mFourierCoeff f q := by
  ext i
  simp only [vectorProjection_apply, projection, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mFourierCoeff_vector_apply f hf]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

theorem integral_vectorProjection_error_eq (f : UnitAddTorus d → EuclideanSpace ℂ ι)
    (hf : MemLp f 2) (P : Finset (d → ℤ)) :
    (∫ x, ‖vectorProjection f P x - f x‖ ^ 2) =
      ∑ i, ∫ x, ‖projection (fun y ↦ f y i) P x - f x i‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, vectorProjection_apply]
  apply integral_finsetSum
  intro i _
  exact (((projection (fun y ↦ f y i) P).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (p := 2)).sub (hf.eval_piLp i)).norm.integrable_sq

theorem tendsto_integral_vectorProjection_error (f : UnitAddTorus d → EuclideanSpace ℂ ι)
    (hf : MemLp f 2) :
    Tendsto (fun P : Finset (d → ℤ) ↦ ∫ x, ‖vectorProjection f P x - f x‖ ^ 2) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ
    (fun i _ ↦ tendsto_integral_projection_error (fun x ↦ f x i) (hf.eval_piLp i))
  simpa only [Finset.sum_const_zero, integral_vectorProjection_error_eq f hf] using h

end Mettapedia.Analysis.UnitTorusL2Projection
