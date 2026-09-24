import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityTangency
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalClusterAnisotropy

/-!
# Full vorticity differentiated along the actual frozen material path

The curve has the instantaneous full velocity. The previously constructed
trajectory and tangency theorem supplies its vorticity derivative without
treating the frozen curve as a flow line at other times.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalFrozenVorticity

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeMeasurableMaterialRate PancakeMaterialChainRule
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeLocalSpatialVelocity
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing LocalMeanAlignmentBalance

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def frozenVorticity (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) (h : ℝ) : R3 :=
  fullVorticity (u (t + h)) (x + materialShift (velocity (u t) x) h)

theorem frozenVorticity_zero (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) :
    frozenVorticity u t x 0 = fullVorticity (u t) x := by
  have hs : materialShift (velocity (u t) x) 0 = 0 := by ext i; simp [materialShift, torusPoint]
  simp only [frozenVorticity, add_zero, hs]

theorem hasDerivAt_frozenVorticity {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : T3) :
    HasDerivAt (fun h ↦ frozenVorticity s.coefficients t x h)
      (fullStrainOperator (s.coefficients t) x (fullVorticity (s.coefficients t) x) +
        nu • fullVorticityLaplacian (s.coefficients t) x) 0 := by
  obtain ⟨r, rfl⟩ := torusPoint_surjective x
  let v := velocity (s.coefficients t) (torusPoint r)
  let X : ℝ → X3 := fun τ i ↦ r i + (τ - t) * v i
  have hXt : X t = r := by funext i; simp only [X, sub_self, zero_mul, add_zero]
  have hX : HasDerivAt X (liftedVelocity s t (X t)) t := by
    rw [hXt]
    apply hasDerivAt_pi.mpr
    intro i
    have h := (((hasDerivAt_id t).sub_const t).mul_const (v i)).const_add (r i)
    simpa only [X, id_eq, one_mul, v, velocity, liftedVelocity, spatialField,
      complexRealPartEuclideanCLM_apply, complexRealPartEuclidean, PiLp.toLp_apply] using h
  have hw := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  rw [hXt] at hw
  have h := hw.scomp_of_eq 0 (h := fun h : ℝ ↦ t + h)
    ((hasDerivAt_id (0 : ℝ)).const_add t) (add_zero t).symm
  simpa only [frozenVorticity, Function.comp_def, id_eq, add_zero, one_smul, X,
    add_sub_cancel_left, torusPoint_line, v] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalFrozenVorticity
