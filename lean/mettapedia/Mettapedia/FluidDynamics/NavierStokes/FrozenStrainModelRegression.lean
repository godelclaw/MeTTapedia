import Mettapedia.FluidDynamics.NavierStokes.FrozenStrainModel

/-!
# Frozen-strain model: regression checks

Theorem-level checks for the frozen-strain vorticity model: initial
conditions of the exact solution, re-export of the solution property, and
concrete numeric instances of the uniform-depletion counterexample and the
aperture coverage gap.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace FrozenStrainModelRegression

open scoped RealInnerProductSpace

/-- The wave number starts at `k₀`. -/
theorem frozenStrainWaveNumber_zero (k₀ γ : ℝ) :
    frozenStrainWaveNumber k₀ γ 0 = k₀ := by
  unfold frozenStrainWaveNumber
  simp

/-- The amplification starts at `1`. -/
theorem frozenStrainAmplification_zero (ν k₀ γ : ℝ) :
    frozenStrainAmplification ν k₀ γ 0 = 1 := by
  unfold frozenStrainAmplification frozenStrainExponent
  simp

/-- The packet starts at the initial datum `a₀ sin(k₀ x₁) e₀`. -/
theorem frozenStrainVorticity_zero (a₀ ν k₀ γ : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    frozenStrainVorticity a₀ ν k₀ γ 0 x =
      (a₀ * Real.sin (k₀ *
        ⟪(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 3)), x⟫)) •
        (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)) := by
  rw [frozenStrainVorticity_apply, frozenStrainWaveNumber_zero]
  unfold frozenStrainAmplitude
  rw [frozenStrainAmplification_zero, mul_one]

/-- Re-export: the packet is an exact solution (positive strain). -/
theorem frozenStrainVorticity_solves_pos (a₀ ν k₀ : ℝ) {γ : ℝ}
    (hγ : 0 < γ) :
    SolvesFrozenStrainVorticityEq γ ν (frozenStrainVorticity a₀ ν k₀ γ) :=
  frozenStrainVorticity_solves a₀ ν k₀ (ne_of_gt hγ)

/-- Concrete instance: at unit viscosity and unit frequency some strain and
time drive the amplification beyond `10⁶`. -/
theorem frozenStrain_amplification_exceeds_million :
    ∃ γ t : ℝ, 0 < γ ∧ 0 < t ∧
      (10 : ℝ) ^ 6 < frozenStrainAmplification 1 1 γ t :=
  frozenStrain_no_uniform_amplification_bound 1 1 one_pos one_pos ((10 : ℝ) ^ 6)

/-- Concrete instance of the coverage gap: at `ν = 1`, `λ = 4`, `γ = 9` the
(AC)-failure aperture exceeds the Bernstein aperture. -/
theorem coverage_gap_concrete :
    (Real.sqrt 4)⁻¹ < Real.sqrt ((9 : ℝ) / 1) / 4 :=
  (anisotropic_coverage_gap (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Concrete non-instance: at `ν = 1`, `λ = 4`, `γ = 2` (weak strain) there
is no gap. -/
theorem coverage_gap_concrete_weak_strain :
    ¬ ((Real.sqrt 4)⁻¹ < Real.sqrt ((2 : ℝ) / 1) / 4) := by
  intro h
  have := (anisotropic_coverage_gap (by norm_num) (by norm_num)).mp h
  norm_num at this

end FrozenStrainModelRegression
end NavierStokes
end FluidDynamics
end Mettapedia
