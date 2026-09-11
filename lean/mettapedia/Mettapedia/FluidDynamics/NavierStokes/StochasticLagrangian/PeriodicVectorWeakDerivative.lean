import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierGradientEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol
import Mettapedia.Analysis.FiniteSumEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Weak derivatives and divergence of real periodic vector fields

Coordinatewise weak derivatives are square-integrable and agree almost
everywhere with the actual vector derivative along coordinate shifts.
Their complex Fourier coefficients retain the physical unit-torus phase.
No divergence-free assumption is imposed on the vector field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative

open MeasureTheory PancakeHaarTransportRate PancakePeriodicWeakDerivative
open PeriodicFourierGradientEnergy PeriodicFourierWeakDerivative
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve
open PeriodicFourierTriad PancakePeriodicVorticityEquation
open FourierPressureTraceSymbol (complexifyVector)

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def coordinateRate (f : T3 → R3) (j : Fin 3) (x : T3) : R3 :=
  WithLp.toLp 2 (fun i ↦ shiftRate (fun y ↦ f y i) (coordinateShift j) x)

@[simp] theorem coordinateRate_apply (f : T3 → R3) (j i : Fin 3) (x : T3) :
    coordinateRate f j x i = shiftRate (fun y ↦ f y i) (coordinateShift j) x := rfl

theorem continuous_component (f : T3 → R3) (hf : Continuous f) (i : Fin 3) :
    Continuous (fun x ↦ f x i) := (PiLp.continuous_apply 2 _ i).comp hf

theorem locallyLipschitz_component (f : T3 → R3)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (i : Fin 3) :
    LocallyLipschitz (fun r : X3 ↦ f (torusPoint r) i) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).lipschitz.locallyLipschitz.comp hfL

theorem ae_hasDerivAt_coordinateRate (f : T3 → R3) (j : Fin 3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    ∀ᵐ x : T3, HasDerivAt (fun h ↦ f (x + coordinateShift j h)) (coordinateRate f j x) 0 := by
  have h (i : Fin 3) := ae_coordinate_differentiable (fun x ↦ f x i) j
    (continuous_component f hf i) (locallyLipschitz_component f hfL i)
  filter_upwards [ae_all_iff.mpr h] with x hx
  have hd : DifferentiableAt ℝ (fun h ↦ f (x + coordinateShift j h)) 0 :=
    (differentiableAt_piLp 2).mpr hx
  have heq : deriv (fun h ↦ f (x + coordinateShift j h)) 0 = coordinateRate f j x := by
    ext i
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt 0
      hd.hasDerivAt).deriv.symm
  exact heq ▸ hd.hasDerivAt

theorem memLp_coordinateRate (f : T3 → R3) (j : Fin 3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) : MemLp (coordinateRate f j) 2 := by
  apply MemLp.of_eval_piLp
  intro i
  exact PeriodicFourierGradientEnergy.memLp_coordinateRate (fun x ↦ f x i) j
    (continuous_component f hf i) (locallyLipschitz_component f hfL i)

theorem integrable_coordinateRate (f : T3 → R3) (j : Fin 3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) : Integrable (coordinateRate f j) := by
  apply Integrable.of_eval_piLp
  intro i
  exact (integral_coordinateRate_zero (fun x ↦ f x i) j
    (continuous_component f hf i) (locallyLipschitz_component f hfL i)).1

theorem integrable_complexify (f : T3 → R3) (hf : Integrable f) :
    Integrable (fun x ↦ complexifyVector (f x)) := by
  apply Integrable.of_eval_piLp
  intro i
  exact Complex.ofRealCLM.integrable_comp (hf.eval_piLp i)

theorem memLp_complexify (f : T3 → R3) {p : ENNReal} (hf : MemLp f p) :
    MemLp (fun x ↦ complexifyVector (f x)) p := by
  apply MemLp.of_eval_piLp
  intro i
  exact Complex.ofRealCLM.comp_memLp' (hf.eval_piLp i)

theorem integrable_character_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : T3 → E) (hf : Integrable f) (q : Wavevector) :
    Integrable (fun x ↦ UnitAddTorus.mFourier q x • f x) :=
  hf.bdd_smul ‖UnitAddTorus.mFourier q‖ (UnitAddTorus.mFourier q).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (UnitAddTorus.mFourier q).norm_coe_le_norm)

theorem mFourierCoeff_apply (f : T3 → C3) (hf : Integrable f) (q : Wavevector) (i : Fin 3) :
    UnitAddTorus.mFourierCoeff f q i = UnitAddTorus.mFourierCoeff (fun x ↦ f x i) q := by
  exact eval_integral_piLp (fun i ↦ (integrable_character_smul f hf (-q)).eval_piLp i) i

theorem mFourierCoeff_complexify_coordinateRate (f : T3 → R3) (j : Fin 3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (coordinateRate f j x)) q =
      (unitTorusDerivativePhase * (q j : ℂ)) •
        UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (f x)) q := by
  ext i
  rw [mFourierCoeff_apply _ (integrable_complexify _ (integrable_coordinateRate f j hf hfL))]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [mFourierCoeff_apply _ (integrable_complexify f
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))]
  exact mFourierCoeff_coordinateRate (fun x ↦ f x i) j
    (continuous_component f hf i) (locallyLipschitz_component f hfL i) q

def divergence (f : T3 → R3) (x : T3) : ℝ := ∑ j : Fin 3, coordinateRate f j x j

theorem memLp_divergence (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) : MemLp (divergence f) 2 :=
  memLp_finsetSum _ (fun j _ ↦ (memLp_coordinateRate f j hf hfL).eval_piLp j)

theorem integral_divergence_zero (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) :
    (∫ x : T3, divergence f x) = 0 := by
  unfold divergence
  rw [integral_finsetSum _ (fun j _ ↦ (integrable_coordinateRate f j hf hfL).eval_piLp j)]
  have h (j : Fin 3) : (∫ x : T3, coordinateRate f j x j) = 0 :=
    (integral_coordinateRate_zero (fun x ↦ f x j) j
      (continuous_component f hf j) (locallyLipschitz_component f hfL j)).2
  simp only [h, Finset.sum_const_zero]

theorem mFourierCoeff_divergence (f : T3 → R3) (hf : Continuous f)
    (hfL : LocallyLipschitz (fun r : X3 ↦ f (torusPoint r))) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (divergence f x : ℂ)) q =
      unitTorusDerivativePhase * ∑ j : Fin 3, (q j : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x ↦ complexifyVector (f x)) q j := by
  have hdi (j : Fin 3) : Integrable (fun x ↦ (coordinateRate f j x j : ℂ)) :=
    Complex.ofRealCLM.integrable_comp ((integrable_coordinateRate f j hf hfL).eval_piLp j)
  calc
    _ = ∑ j : Fin 3, UnitAddTorus.mFourierCoeff (fun x ↦ (coordinateRate f j x j : ℂ)) q := by
      simp only [UnitAddTorus.mFourierCoeff, divergence, Complex.ofReal_sum, Finset.smul_sum]
      exact integral_finsetSum _ (fun j _ ↦ integrable_character_smul _ (hdi j) (-q))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mFourierCoeff_apply _ (integrable_complexify f
        (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))]
      change UnitAddTorus.mFourierCoeff (fun x ↦ (shiftRate (fun y ↦ f y j) (coordinateShift j) x : ℂ)) q = _
      rw [mFourierCoeff_coordinateRate _ j (continuous_component f hf j) (locallyLipschitz_component f hfL j)]
      exact mul_assoc _ _ _

theorem divergence_sq_le (f : T3 → R3) (x : T3) :
    divergence f x ^ 2 ≤ 3 * ∑ j : Fin 3, ‖coordinateRate f j x‖ ^ 2 := by
  have h := Finset.norm_sum_sq_le_card_mul_sum_norm_sq Finset.univ
    (fun j : Fin 3 ↦ coordinateRate f j x j)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, Real.norm_eq_abs, sq_abs] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply Finset.sum_le_sum
  intro j _
  have hj := pow_le_pow_left₀ (norm_nonneg (coordinateRate f j x j))
    (PiLp.norm_apply_le (coordinateRate f j x) j) 2
  simpa only [Real.norm_eq_abs, sq_abs] using hj

end Mettapedia.FluidDynamics.NavierStokes.PeriodicVectorWeakDerivative
