import Mettapedia.Analysis.DyadicAnnulusCorrection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputSymbol

/-!
# Exact dyadic normalization of the low-output pressure symbol

Both spatial annuli are normalized by their dyadic sums. The globally smooth
correction preserves the existing pressure identity and its common compact
support. This changes the kernels: pointwise multiplier comparison is not
used to infer any Fourier-kernel norm bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol

open Mettapedia.Analysis.DyadicAnnulus
open PressureLowOutputCutoff
open PressureLowOutputSymbol (pairEquiv commonSupport isCompact_commonSupport)
open scoped ContDiff SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3
local notation "A" => ℝ × R3

def retained (t : ℝ) (p : P) : ℝ :=
  parameterCutoff t * normalizedCutoff p.1 * normalizedCutoff p.2

theorem retained_eq_corrected (t : ℝ) (p : P) :
    retained t p = PressureLowOutputCutoff.retained t p *
      smoothCorrection p.1 * smoothCorrection p.2 := by
  simp only [retained, PressureLowOutputCutoff.retained, normalizedCutoff_eq_mul_smoothCorrection]
  ring

def entry (t : ℝ) (e w v : R3) (i : Fin 3) (p : P) : ℝ :=
  PressureLowOutputSymbol.entry t e w v i p * smoothCorrection p.1 * smoothCorrection p.2

theorem entry_eq_pressure (t : ℝ) (e w v : R3) (i : Fin 3) (p : P) :
    retained t p * CoherentPressurePair.tiltPair e p.1 (receiver t p) w v i =
      (ratio t) ^ 2 * entry t e w v i p := by
  rw [retained_eq_corrected]
  calc
    _ = (PressureLowOutputCutoff.retained t p *
        CoherentPressurePair.tiltPair e p.1 (receiver t p) w v i) *
        smoothCorrection p.1 * smoothCorrection p.2 := by ring
    _ = _ := by rw [PressureLowOutputSymbol.entry_eq_pressure]; unfold entry; ring

theorem contDiff_entry (w v : R3) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × P ↦ entry z.1.1 z.1.2 w v i z.2) :=
  ((PressureLowOutputSymbol.contDiff_entry w v i).mul
    (contDiff_smoothCorrection.comp (contDiff_fst.comp contDiff_snd))).mul
    (contDiff_smoothCorrection.comp (contDiff_snd.comp contDiff_snd))

theorem tsupport_entry_subset (t : ℝ) (e w v : R3) (i : Fin 3) :
    tsupport (entry t e w v i) ⊆ Metric.closedBall (0 : R3) 4 ×ˢ Metric.closedBall (0 : R3) 4 := by
  exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans
    (PressureLowOutputSymbol.tsupport_entry_subset t e w v i)

def symbol (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  let f : E6 → ℂ := fun x ↦ (entry a.1 a.2 w v i (pairEquiv x) : ℂ)
  have hcompact : HasCompactSupport f := by
    have hreal : HasCompactSupport (entry a.1 a.2 w v i) :=
      ((isCompact_closedBall (0 : R3) 4).prod (isCompact_closedBall (0 : R3) 4)).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_entry_subset a.1 a.2 w v i)
    exact (hreal.comp_homeomorph pairEquiv.toHomeomorph).comp_left Complex.ofReal_zero
  have hcont : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_entry w v i).comp (contDiff_const.prodMk pairEquiv.contDiff))
  hcompact.toSchwartzMap hcont

@[simp] theorem symbol_apply (a : A) (w v : R3) (i : Fin 3) (x : E6) :
    symbol a w v i x = (entry a.1 a.2 w v i (pairEquiv x) : ℂ) := rfl

theorem contDiff_symbol (w v : R3) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × E6 ↦ symbol z.1 w v i z.2) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_entry w v i).comp (contDiff_fst.prodMk (pairEquiv.contDiff.comp contDiff_snd)))

theorem tsupport_symbol_subset (a : A) (w v : R3) (i : Fin 3) :
    tsupport (symbol a w v i) ⊆ commonSupport := by
  apply closure_minimal _ isCompact_commonSupport.isClosed
  intro x hx
  apply tsupport_entry_subset a.1 a.2 w v i
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

end Mettapedia.FluidDynamics.NavierStokes.PressureDyadicSymbol
