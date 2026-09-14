import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousHeatEvaluation

/-!
# Reflection symmetries of the exact two-shear convolution

Reflections preserve the input support and commute with the heat symbol.
Both divergence factors acquire the same coordinate sign, so their signed
work is unchanged. The argument reindexes the complete input sums.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousReflection

open PeriodicFourierTriad PeriodicGradientFluxTriple
open TwoShearViscousData TwoShearViscousCoefficientEvaluation
open RationalStretchingFlux RationalStretchingFluxHeat RationalStretchingFluxContraction

def reflection (r : Fin 3 → Bool) (q : Wavevector) : Wavevector :=
  fun i ↦ if r i then -q i else q i

def reflectionSign (r : Fin 3 → Bool) (i : Fin 3) : ℚ := if r i then -1 else 1

theorem reflection_involutive (r : Fin 3 → Bool) (q : Wavevector) :
    reflection r (reflection r q) = q := by
  ext i
  simp only [reflection]
  split_ifs <;> simp

theorem reflection_sub (r : Fin 3 → Bool) (q k : Wavevector) :
    reflection r (q - k) = reflection r q - reflection r k := by
  ext i
  simp only [reflection, Pi.sub_apply]
  split_ifs <;> ring

theorem firstHorizontal_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    firstHorizontal (reflection r q) ↔ firstHorizontal q := by
  simp only [firstHorizontal, reflection]
  split_ifs <;> omega

theorem secondHorizontal_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    secondHorizontal (reflection r q) ↔ secondHorizontal q := by
  simp only [secondHorizontal, reflection]
  split_ifs <;> omega

theorem profile_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    profile (reflection r q 2) = profile (q 2) := by
  simp only [reflection]
  split_ifs <;> simp

theorem reflectedProfile_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    reflectedProfile (reflection r q 2) = reflectedProfile (q 2) := by
  simp only [reflection]
  split_ifs <;> simp

theorem mem_modes_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    reflection r q ∈ modes ↔ q ∈ modes := by
  have hz : (-3 ≤ reflection r q 2 ∧ reflection r q 2 ≤ 3) ↔ (-3 ≤ q 2 ∧ q 2 ≤ 3) := by
    simp only [reflection]
    split_ifs <;> omega
  simp only [mem_modes, firstHorizontal_reflection, secondHorizontal_reflection, hz]

theorem sum_reflection {E : Type*} [AddCommMonoid E] (r : Fin 3 → Bool) (f : Wavevector → E) :
    ∑ q ∈ modes, f (reflection r q) = ∑ q ∈ modes, f q := by
  apply Finset.sum_bij (fun q _ ↦ reflection r q)
  · intro q hq
    exact (mem_modes_reflection r q).mpr hq
  · intro q _ k _ h
    simpa only [reflection_involutive] using congrArg (reflection r) h
  · intro q hq
    exact ⟨reflection r q, (mem_modes_reflection r q).mpr hq, reflection_involutive r q⟩
  · intro q _
    rfl

theorem rationalData_reflection (r : Fin 3 → Bool) (q : Wavevector) (i : Fin 3) :
    rationalData (reflection r q) i =
      reflectionSign r 0 * reflectionSign r 1 * reflectionSign r i * rationalData q i := by
  fin_cases i <;>
    simp only [rationalData, firstHorizontal_reflection, secondHorizontal_reflection,
      profile_reflection, reflectedProfile_reflection]
  · cases h0 : r 0 <;> cases h1 : r 1 <;>
      simp [reflection, reflectionSign, h0, h1] <;> split_ifs <;> ring
  · cases h0 : r 0 <;> cases h1 : r 1 <;>
      simp [reflection, reflectionSign, h0, h1] <;> split_ifs <;> ring
  · simp

theorem rationalCurl_reflection (r : Fin 3 → Bool) (q : Wavevector) (i : Fin 3) :
    rationalCurl rationalData (reflection r q) i =
      reflectionSign r 2 * reflectionSign r i * rationalCurl rationalData q i := by
  fin_cases i <;>
    simp only [rationalCurl, rationalData_reflection]
  all_goals
    cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;>
      simp [reflection, reflectionSign, h0, h1, h2] <;> ring

theorem rationalModeSquare_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    rationalModeSquare (reflection r q) = rationalModeSquare q := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [reflection]
  split_ifs <;> simp

theorem tripleHeatWeight_reflection (r : Fin 3 → Bool) (k l m : Wavevector) :
    tripleHeatWeight (reflection r k, (reflection r l, reflection r m)) =
      tripleHeatWeight (k, (l, m)) := by
  simp [tripleHeatWeight, rationalModeSquare_reflection]

theorem divergenceInteraction_reflection (r : Fin 3 → Bool) (q k l m : Wavevector) (i : Fin 3) :
    divergenceInteraction rationalData (reflection r q)
        (reflection r k, (reflection r l, reflection r m)) i =
      (reflectionSign r 0 * reflectionSign r 1 * reflectionSign r i) *
        divergenceInteraction rationalData q (k, (l, m)) i := by
  simp only [divergenceInteraction_eq, rationalCurl_reflection, rationalData_reflection,
    Fin.sum_univ_three]
  fin_cases i <;>
    cases h0 : r 0 <;> cases h1 : r 1 <;> cases h2 : r 2 <;>
      simp [reflection, reflectionSign, h0, h1, h2] <;> ring_nf <;> simp

theorem divergence_reflection (r : Fin 3 → Bool) (q : Wavevector) (i : Fin 3) :
    rationalDivergenceCoefficient modes rationalData (reflection r q) i =
      (reflectionSign r 0 * reflectionSign r 1 * reflectionSign r i) *
        rationalDivergenceCoefficient modes rationalData q i := by
  simp only [divergence_eq_double_sum]
  rw [← sum_reflection r (fun k ↦ ∑ l ∈ modes,
    divergenceInteraction rationalData (reflection r q) (k, (l, reflection r q - k - l)) i)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← sum_reflection r (fun l ↦
    divergenceInteraction rationalData (reflection r q)
      (reflection r k, (l, reflection r q - reflection r k - l)) i)]
  simp only [← reflection_sub, divergenceInteraction_reflection]

theorem heat_divergence_reflection (r : Fin 3 → Bool) (q : Wavevector) (i : Fin 3) :
    rationalHeatDivergenceCoefficient modes rationalData (reflection r q) i =
      (reflectionSign r 0 * reflectionSign r 1 * reflectionSign r i) *
        rationalHeatDivergenceCoefficient modes rationalData q i := by
  simp only [heat_divergence_eq_double_sum]
  rw [← sum_reflection r (fun k ↦ ∑ l ∈ modes,
    tripleHeatWeight (k, (l, reflection r q - k - l)) *
      divergenceInteraction rationalData (reflection r q) (k, (l, reflection r q - k - l)) i)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← sum_reflection r (fun l ↦
    tripleHeatWeight (reflection r k, (l, reflection r q - reflection r k - l)) *
      divergenceInteraction rationalData (reflection r q)
        (reflection r k, (l, reflection r q - reflection r k - l)) i)]
  simp only [← reflection_sub, tripleHeatWeight_reflection, divergenceInteraction_reflection]
  apply Finset.sum_congr rfl
  intro l _
  ring

def workCoefficient (q : Wavevector) : ℚ :=
  (∑ i, rationalDivergenceCoefficient modes rationalData q i *
    rationalHeatDivergenceCoefficient modes rationalData q i) / rationalModeSquare q

theorem workCoefficient_reflection (r : Fin 3 → Bool) (q : Wavevector) :
    workCoefficient (reflection r q) = workCoefficient q := by
  simp only [workCoefficient, rationalModeSquare_reflection,
    divergence_reflection, heat_divergence_reflection]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hs : (reflectionSign r 0 * reflectionSign r 1 * reflectionSign r i) ^ 2 = 1 := by
    simp only [reflectionSign]
    split_ifs <;> norm_num
  calc
    _ = (reflectionSign r 0 * reflectionSign r 1 * reflectionSign r i) ^ 2 *
      (rationalDivergenceCoefficient modes rationalData q i *
        rationalHeatDivergenceCoefficient modes rationalData q i) := by ring
    _ = _ := by rw [hs, one_mul]

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousReflection
