import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeakIncompressibleTransport

/-!
# Splitting the actual material derivative into time and transport

At real spacetime differentiability points the derivative in direction
(1,v) splits into the time direction and the three coordinate directions.
All scalar rates below are derivatives of the actual periodic field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialChainRule

open scoped Topology NNReal
open MeasureTheory
open PancakeFourierMaterialPaths PancakeFourierStrainGradient PancakeFourierTranslationCurve
open PancakeMeasurableMaterialRate PancakeCompactMeanDerivative PancakePeriodicLipschitz
open PancakeHaarTransportRate PancakeWeakIncompressibleTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "ST" => ℝ × X3

def scalarMaterialRate (f : ℝ → T3 → ℝ) (v : T3 → R3) (t : ℝ) (x : T3) : ℝ :=
  deriv (fun h ↦ f (t + h) (x + materialShift (v x) h)) 0

theorem linear_materialDirection (L : ST →L[ℝ] ℝ) (v : R3) :
    L (1, fun j ↦ v j) = L (1, 0) + ∑ j : Fin 3, L (0, Pi.single j 1) * v j := by
  have he : ((1 : ℝ), fun j : Fin 3 ↦ v j) = (1, 0) +
      ∑ j : Fin 3, v j • ((0 : ℝ), Pi.single j (1 : ℝ)) := by
    apply Prod.ext
    · simp [Fin.sum_univ_three]
    · funext i
      fin_cases i <;> simp [Fin.sum_univ_three]
  rw [he, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul, smul_eq_mul, mul_comm]

theorem hasDerivAt_real_material_path (t : ℝ) (r : X3) (v : R3) :
    HasDerivAt (fun h : ℝ ↦ (t + h, fun i : Fin 3 ↦ r i + h * v i))
      ((1 : ℝ), fun i : Fin 3 ↦ v i) 0 := by
  apply HasDerivAt.prodMk ((hasDerivAt_id (0 : ℝ)).const_add t)
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (r i)

theorem hasDerivAt_real_coordinate_path (t : ℝ) (r : X3) (j : Fin 3) :
    HasDerivAt (fun h : ℝ ↦ (t, coordinateLine r j h))
      ((0 : ℝ), Pi.single j (1 : ℝ)) 0 := by
  apply HasDerivAt.prodMk (hasDerivAt_const 0 t)
  apply hasDerivAt_pi.mpr
  intro i
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (if i = j then 1 else 0 : ℝ)).const_add (r i)
  simpa only [coordinateLine, Pi.single_apply, eq_comm, id_eq, one_mul] using hd

theorem materialRate_split_of_real_fderiv
    (f : ℝ → T3 → ℝ) (v : T3 → R3) (t : ℝ) (r : X3)
    (hf : DifferentiableAt ℝ (fun z : ST ↦ f z.1 (torusPoint z.2)) (t, r)) :
    DifferentiableAt ℝ (fun h ↦ f h (torusPoint r)) t ∧
      scalarMaterialRate f v t (torusPoint r) = parameterRate f t (torusPoint r) +
        coordinateTransport (f t) (fun j x ↦ v x j) (torusPoint r) := by
  let F : ST → ℝ := fun z ↦ f z.1 (torusPoint z.2)
  let L := fderiv ℝ F (t, r)
  have ht : HasDerivAt (fun h : ℝ ↦ f h (torusPoint r)) (L (1, 0)) t := by
    have hp := (hasDerivAt_id t).prodMk (hasDerivAt_const t r)
    exact hf.hasFDerivAt.comp_hasDerivAt t hp
  have hc : ∀ j : Fin 3, shiftRate (f t) (coordinateShift j) (torusPoint r) = L (0, Pi.single j 1) := by
    intro j
    have hF : HasFDerivAt F L (t, coordinateLine r j 0) := by
      rw [coordinateLine_zero]
      exact hf.hasFDerivAt
    have hd := hF.comp_hasDerivAt 0 (hasDerivAt_real_coordinate_path t r j)
    simpa only [shiftRate, Function.comp_def, F, torusPoint_coordinateLine] using hd.deriv
  have hm : scalarMaterialRate f v t (torusPoint r) = L (1, fun j ↦ v (torusPoint r) j) := by
    have hF : HasFDerivAt F L (t + 0, fun i : Fin 3 ↦ r i + 0 * v (torusPoint r) i) := by
      simpa only [add_zero, zero_mul] using hf.hasFDerivAt
    have hd := hF.comp_hasDerivAt 0 (hasDerivAt_real_material_path t r (v (torusPoint r)))
    simpa only [scalarMaterialRate, Function.comp_def, F, torusPoint_line] using hd.deriv
  refine ⟨ht.differentiableAt, ?_⟩
  rw [hm, linear_materialDirection]
  change L (1, 0) + _ = deriv (fun h ↦ f h (torusPoint r)) t + _
  rw [ht.deriv]
  simp only [coordinateTransport, hc]

end Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialChainRule
