import Mettapedia.Analysis.EuclideanCrossProductCalculus
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicSymbol

/-!
# Coherent pressure as a sum of longitudinal input factors

Removing the longitudinal output factor from the normalized coherent
symbol leaves a jointly smooth, compactly supported family. Multiplying
it by the sum of the longitudinal input frequencies recovers the retained
pressure exactly, without division by an angle or by the output/input ratio.
The resulting prefactor is linear in that ratio, not quadratic.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceSymbol

open Mettapedia.Analysis.SmoothAnnulus Mettapedia.Analysis.DyadicAnnulus
open Mettapedia.Analysis.EuclideanCrossProduct
open PressureLowOutputCutoff
open PressureLowOutputSymbol (pairEquiv commonSupport isCompact_commonSupport)
open scoped ContDiff RealInnerProductSpace SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3
local notation "A" => ℝ × R3

/-- The coherent normalized symbol with its longitudinal output factor removed. -/
def entry (t : ℝ) (e : R3) (i : Fin 3) (p : P) : ℝ :=
  PressureLowOutputCutoff.retained t p *
    ((⟪p.2, cross p.1 e⟫ * ⟪p.2, cross (receiver t p) e⟫ /
      (denominator p.1 * receiverDenominator t p)) /
      denominator p.2 * (p.2 i - ⟪e, p.2⟫ * e i)) *
    smoothCorrection p.1 * smoothCorrection p.2

theorem coherent_entry_eq (t : ℝ) (e : R3) (i : Fin 3) (p : P) :
    PressureDyadicSymbol.entry t e e e i p = ⟪p.2, e⟫ * entry t e i p := by
  unfold PressureDyadicSymbol.entry PressureLowOutputSymbol.entry entry
  ring

theorem longitudinal_receiver_add (t : ℝ) (e : R3) (p : P) :
    ⟪p.1, e⟫ + ⟪receiver t p, e⟫ = ratio t * ⟪p.2, e⟫ := by
  simp only [receiver, inner_sub_left, real_inner_smul_left]
  ring

/-- Exact factorization, including zero ratio and zero longitudinal frequencies. -/
theorem retained_pressure_eq (t : ℝ) (e : R3) (i : Fin 3) (p : P) :
    PressureDyadicSymbol.retained t p *
        CoherentPressurePair.tiltPair e p.1 (receiver t p) e e i =
      ratio t * entry t e i p * (⟪p.1, e⟫ + ⟪receiver t p, e⟫) := by
  rw [PressureDyadicSymbol.entry_eq_pressure, coherent_entry_eq, longitudinal_receiver_add]
  ring

theorem contDiff_entry (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × P ↦ entry z.1.1 z.1.2 i z.2) := by
  have htp : ContDiff ℝ ∞ (fun z : A × P ↦ (z.1.1, z.2)) := by fun_prop
  have hr := contDiff_receiver.comp htp
  have hret := contDiff_retained.comp htp
  have hdenp := contDiff_receiverDenominator.comp htp
  have hdenk : ContDiff ℝ ∞ (fun z : A × P ↦ denominator z.2.1) := by
    unfold denominator
    exact ((contDiff_norm_sq ℝ).comp (contDiff_fst.comp contDiff_snd)).add
      (contDiff_const.sub (contDiff_buffer.comp (contDiff_fst.comp contDiff_snd)))
  have hdenq : ContDiff ℝ ∞ (fun z : A × P ↦ denominator z.2.2) := by
    unfold denominator
    exact ((contDiff_norm_sq ℝ).comp (contDiff_snd.comp contDiff_snd)).add
      (contDiff_const.sub (contDiff_buffer.comp (contDiff_snd.comp contDiff_snd)))
  have he : ContDiff ℝ ∞ (fun z : A × P ↦ z.1.2) := by fun_prop
  have hk : ContDiff ℝ ∞ (fun z : A × P ↦ z.2.1) := by fun_prop
  have hq : ContDiff ℝ ∞ (fun z : A × P ↦ z.2.2) := by fun_prop
  have hcrossk : ContDiff ℝ ∞ (fun z : A × P ↦ cross z.2.1 z.1.2) := by
    simpa only [Function.comp_def] using contDiff_cross.comp (hk.prodMk he)
  have hcrossp : ContDiff ℝ ∞ (fun z : A × P ↦ cross (receiver z.1.1 z.2) z.1.2) := by
    simpa only [Function.comp_def] using contDiff_cross.comp (hr.prodMk he)
  have htrace := ((hq.inner ℝ hcrossk).mul (hq.inner ℝ hcrossp)).div
    (hdenk.mul hdenp) (fun z ↦ mul_ne_zero
      (denominator_pos z.2.1).ne' (receiverDenominator_pos z.1.1 z.2).ne')
  have htilt : ContDiff ℝ ∞ (fun z : A × P ↦ z.2.2 i - ⟪z.1.2, z.2.2⟫ * z.1.2 i) :=
    (by fun_prop : ContDiff ℝ ∞ (fun z : A × P ↦ z.2.2 i)).sub
      ((he.inner ℝ hq).mul (by fun_prop))
  exact ((hret.mul ((htrace.div hdenq (fun z ↦ (denominator_pos z.2.2).ne')).mul htilt)).mul
    (contDiff_smoothCorrection.comp hk)).mul (contDiff_smoothCorrection.comp hq)

theorem tsupport_entry_subset (t : ℝ) (e : R3) (i : Fin 3) :
    tsupport (entry t e i) ⊆ Metric.closedBall (0 : R3) 4 ×ˢ Metric.closedBall (0 : R3) 4 := by
  exact (tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans
    tsupport_mul_subset_left)).trans (tsupport_retained_subset t)

def symbol (a : A) (i : Fin 3) : 𝓢(E6, ℂ) :=
  let f : E6 → ℂ := fun x ↦ (entry a.1 a.2 i (pairEquiv x) : ℂ)
  have hcompact : HasCompactSupport f := by
    have hreal : HasCompactSupport (entry a.1 a.2 i) :=
      ((isCompact_closedBall (0 : R3) 4).prod (isCompact_closedBall (0 : R3) 4)).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_entry_subset a.1 a.2 i)
    exact (hreal.comp_homeomorph pairEquiv.toHomeomorph).comp_left Complex.ofReal_zero
  have hcont : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_entry i).comp (contDiff_const.prodMk pairEquiv.contDiff))
  hcompact.toSchwartzMap hcont

@[simp] theorem symbol_apply (a : A) (i : Fin 3) (x : E6) :
    symbol a i x = (entry a.1 a.2 i (pairEquiv x) : ℂ) := rfl

theorem contDiff_symbol (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × E6 ↦ symbol z.1 i z.2) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_entry i).comp (contDiff_fst.prodMk (pairEquiv.contDiff.comp contDiff_snd)))

theorem tsupport_symbol_subset (a : A) (i : Fin 3) :
    tsupport (symbol a i) ⊆ commonSupport := by
  apply closure_minimal _ isCompact_commonSupport.isClosed
  intro x hx
  apply tsupport_entry_subset a.1 a.2 i
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceSymbol
