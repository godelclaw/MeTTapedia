import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RationalStretchingFluxFiniteWork
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousReflection

/-!
# Exhaustive output grid for the two-shear work

Every triple of supported input modes lands in this grid. The grid may
include zero coefficients; their contribution is proved zero by the
finite-support theorem, not discarded by a numerical threshold.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousOutputGrid

open PeriodicFourierTriad PeriodicGradientFluxTriple
open StretchingFluxFiniteCoefficients RationalStretchingFluxHeat RationalStretchingFluxFiniteWork
open TwoShearViscousData TwoShearViscousCoefficientEvaluation TwoShearViscousReflection

def outputHorizontals : Finset (ℤ × ℤ) :=
  {(-3, 0), (-2, -1), (-2, 1), (-1, -2), (-1, 0), (-1, 2),
    (0, -3), (0, -1), (0, 1), (0, 3), (1, -2), (1, 0), (1, 2),
    (2, -1), (2, 1), (3, 0)}

def outputGrid : Finset Wavevector :=
  (outputHorizontals ×ˢ Finset.Icc (-9 : ℤ) 9).image (fun p ↦ ![p.1.1, p.1.2, p.2])

theorem horizontal_of_mem (q : Wavevector) (hq : q ∈ modes) :
    (q 0, q 1) ∈ horizontalModes := by
  obtain ⟨⟨⟨a, b⟩, k⟩, hp, rfl⟩ := Finset.mem_image.mp hq
  exact (Finset.mem_product.mp hp).1

theorem horizontal_sum_mem (a b c : ℤ × ℤ)
    (ha : a ∈ horizontalModes) (hb : b ∈ horizontalModes) (hc : c ∈ horizontalModes) :
    a + (b + c) ∈ outputHorizontals := by
  simp only [horizontalModes, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num [outputHorizontals]

theorem output_modes_subset : outputModes modes ⊆ outputGrid := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_product.mp hp with ⟨h1, h23⟩
  rcases Finset.mem_product.mp h23 with ⟨h2, h3⟩
  refine Finset.mem_image.mpr ⟨
    ((tripleFrequency p 0, tripleFrequency p 1), tripleFrequency p 2), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · simpa [tripleFrequency] using horizontal_sum_mem _ _ _
        (horizontal_of_mem _ h1) (horizontal_of_mem _ h2) (horizontal_of_mem _ h3)
    · have hz1 := (mem_modes _).mp h1
      have hz2 := (mem_modes _).mp h2
      have hz3 := (mem_modes _).mp h3
      apply Finset.mem_Icc.mpr
      simp only [tripleFrequency, Pi.add_apply]
      constructor <;> omega
  · ext i
    fin_cases i <;> rfl

theorem sum_outputGrid {E : Type*} [AddCommMonoid E] (f : Wavevector → E) :
    ∑ q ∈ outputGrid, f q =
      ∑ h ∈ outputHorizontals, ∑ k ∈ Finset.Icc (-9 : ℤ) 9, f ![h.1, h.2, k] := by
  classical
  rw [outputGrid, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro a _ b _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    exact Prod.ext (Prod.ext h0 h1) h2

theorem rationalWork_eq_grid :
    rationalHeatWork modes rationalData =
      ∑ h ∈ outputHorizontals, ∑ k ∈ Finset.Icc (-9 : ℤ) 9, workCoefficient ![h.1, h.2, k] := by
  calc
    rationalHeatWork modes rationalData = ∑ q ∈ outputGrid, workCoefficient q :=
      heatWork_eq_sum_of_output_subset modes outputGrid rationalData rationalData_supported
        output_modes_subset
    _ = _ := sum_outputGrid workCoefficient

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousOutputGrid
