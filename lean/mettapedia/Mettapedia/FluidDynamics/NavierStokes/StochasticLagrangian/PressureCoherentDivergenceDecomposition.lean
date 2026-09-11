import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairMisalignment

/-!
# Exact pressure decomposition with divergence defects

The two mixed terms retain the quadratic low-output prefactor. The coherent
term is replaced by the divergence of each input minus the divergence of
its transverse remainder. The latter terms have a linear prefactor. This
identity does not assume that localization preserves divergence freedom.
It is a symbol identity, not a bound for the corresponding field operator.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceDecomposition

open PressureLowOutputCutoff (ratio receiver)
open PancakeAnisotropyDepletion (lineRemainder)
open CoherentPressurePair (tiltPair)
open scoped RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "P" => R3 × R3

theorem retained_pressure_eq_mixed_add_divergence
    (t : ℝ) (e w v : R3) (i : Fin 3) (p : P) :
    PressureDyadicSymbol.retained t p * tiltPair e p.1 (receiver t p) w v i =
      (ratio t) ^ 2 * PressureDyadicSymbol.entry t e (lineRemainder e w) v i p +
      (ratio t) ^ 2 * ⟪e, w⟫ * PressureDyadicSymbol.entry t e e (lineRemainder e v) i p +
      ratio t * PressureCoherentDivergenceSymbol.entry t e i p *
        ((⟪p.1, w⟫ - ⟪p.1, lineRemainder e w⟫) * ⟪e, v⟫ +
          ⟪e, w⟫ * (⟪receiver t p, v⟫ - ⟪receiver t p, lineRemainder e v⟫)) := by
  have hd := congrArg (fun z : R3 ↦ z i)
    (PressurePairMisalignment.tiltPair_decomposition e p.1 (receiver t p) w v)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hd
  calc
    _ = (⟪e, w⟫ * ⟪e, v⟫) *
          (PressureDyadicSymbol.retained t p * tiltPair e p.1 (receiver t p) e e i) +
        ⟪e, w⟫ * (PressureDyadicSymbol.retained t p *
          tiltPair e p.1 (receiver t p) e (lineRemainder e v) i) +
        PressureDyadicSymbol.retained t p * tiltPair e p.1 (receiver t p) (lineRemainder e w) v i := by
      rw [hd]
      ring
    _ = _ := by
      rw [PressureCoherentDivergenceSymbol.retained_pressure_eq,
        PressureDyadicSymbol.entry_eq_pressure, PressureDyadicSymbol.entry_eq_pressure]
      simp only [lineRemainder, inner_sub_right, real_inner_smul_right]
      ring

/-- Removing actual divergence defects still leaves differentiated transverse inputs. -/
theorem retained_pressure_eq_mixed_sub_transverse_divergence
    (t : ℝ) (e w v : R3) (i : Fin 3) (p : P)
    (hw : ⟪p.1, w⟫ = 0) (hv : ⟪receiver t p, v⟫ = 0) :
    PressureDyadicSymbol.retained t p * tiltPair e p.1 (receiver t p) w v i =
      (ratio t) ^ 2 * PressureDyadicSymbol.entry t e (lineRemainder e w) v i p +
      (ratio t) ^ 2 * ⟪e, w⟫ * PressureDyadicSymbol.entry t e e (lineRemainder e v) i p -
      ratio t * PressureCoherentDivergenceSymbol.entry t e i p *
        (⟪p.1, lineRemainder e w⟫ * ⟪e, v⟫ +
          ⟪e, w⟫ * ⟪receiver t p, lineRemainder e v⟫) := by
  rw [retained_pressure_eq_mixed_add_divergence, hw, hv]
  ring

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceDecomposition
