import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputCutoff
import Mettapedia.Analysis.CompactSchwartzFamily

/-!
# A smooth normalized low-output pressure symbol

The normalization removes the quadratic output/input ratio before taking
Fourier transforms. The buffered denominators equal the physical ones on
the retained annuli. Unit frozen directions form a compact parameter set.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol

open Mettapedia.Analysis Mettapedia.Analysis.SmoothAnnulus
open Mettapedia.Analysis.EuclideanCrossProduct
open PressureLowOutputCutoff PressureLowOutputCoordinates
open PressureTiltSymbol PancakeAnisotropyDepletion
open scoped ContDiff RealInnerProductSpace FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3
local notation "A" => ℝ × R3

def entry (t : ℝ) (e w v : R3) (i : Fin 3) (p : P) : ℝ :=
  retained t p *
    ((⟪p.2, cross p.1 w⟫ * ⟪p.2, cross (receiver t p) v⟫ /
      (denominator p.1 * receiverDenominator t p)) *
      (⟪p.2, e⟫ / denominator p.2) * (p.2 i - ⟪e, p.2⟫ * e i))

theorem entry_eq_pressure (t : ℝ) (e w v : R3) (i : Fin 3) (p : P) :
    retained t p * CoherentPressurePair.tiltPair e p.1 (receiver t p) w v i =
      (ratio t) ^ 2 * entry t e w v i p := by
  by_cases hr : retained t p = 0
  · simp [entry, hr]
  · have hb := buffers_eq_one_of_retained_ne_zero t p hr
    have hk : denominator p.1 = ‖p.1‖ ^ 2 := by simp [denominator, hb.1]
    have hq : denominator p.2 = ‖p.2‖ ^ 2 := by simp [denominator, hb.2.1]
    rw [show receiver t p = ratio t • p.2 - p.1 from rfl,
      tiltPair_eq_lowOutput]
    simp only [entry, hk, hq, receiverDenominator_eq_of_retained_ne_zero t p hr,
      normalizedTrace, tiltSymbol, lineRemainder, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    unfold receiver
    ring

private theorem contDiff_cross_right (w : R3) :
    ContDiff ℝ ∞ (fun k : R3 ↦ cross k w) := by
  let L : R3 →ₗ[ℝ] R3 :=
    { toFun := fun k ↦ cross k w
      map_add' := fun x y ↦ cross_add_left x y w
      map_smul' := fun a x ↦ cross_smul_left a x w }
  exact L.toContinuousLinearMap.contDiff

theorem contDiff_entry (w v : R3) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × P ↦ entry z.1.1 z.1.2 w v i z.2) := by
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
  have hcrossk : ContDiff ℝ ∞ (fun z : A × P ↦ cross z.2.1 w) := by
    exact (contDiff_cross_right w).comp (contDiff_fst.comp contDiff_snd)
  have hcrossp : ContDiff ℝ ∞ (fun z : A × P ↦ cross (receiver z.1.1 z.2) v) := by
    exact (contDiff_cross_right v).comp hr
  unfold entry
  apply hret.mul
  apply ContDiff.mul
  · apply ContDiff.mul
    · apply ContDiff.div
      · exact ((contDiff_snd.comp contDiff_snd).inner ℝ hcrossk).mul
          ((contDiff_snd.comp contDiff_snd).inner ℝ hcrossp)
      · exact hdenk.mul hdenp
      · intro z
        exact mul_ne_zero (denominator_pos z.2.1).ne' (receiverDenominator_pos z.1.1 z.2).ne'
    · exact ((contDiff_snd.comp contDiff_snd).inner ℝ (contDiff_snd.comp contDiff_fst)).div
        hdenq (fun z ↦ (denominator_pos z.2.2).ne')
  · have heq : ContDiff ℝ ∞ (fun z : A × P ↦ ⟪z.1.2, z.2.2⟫) :=
      (contDiff_snd.comp contDiff_fst).inner ℝ (contDiff_snd.comp contDiff_snd)
    exact (by fun_prop : ContDiff ℝ ∞ (fun z : A × P ↦ z.2.2 i)).sub
      (heq.mul (by fun_prop : ContDiff ℝ ∞ (fun z : A × P ↦ z.1.2 i)))

theorem tsupport_entry_subset (t : ℝ) (e w v : R3) (i : Fin 3) :
    tsupport (entry t e w v i) ⊆ Metric.closedBall (0 : R3) 4 ×ˢ Metric.closedBall (0 : R3) 4 := by
  exact (tsupport_mul_subset_left (f := retained t) (g := fun p ↦
    (⟪p.2, cross p.1 w⟫ * ⟪p.2, cross (receiver t p) v⟫ /
      (denominator p.1 * receiverDenominator t p)) *
      (⟪p.2, e⟫ / denominator p.2) * (p.2 i - ⟪e, p.2⟫ * e i))).trans
    (tsupport_retained_subset t)

def pairLinearEquiv : E6 ≃ₗ[ℝ] P where
  toFun x := (WithLp.toLp 2 ![x 0, x 1, x 2], WithLp.toLp 2 ![x 3, x 4, x 5])
  invFun p := WithLp.toLp 2 ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv p := by apply Prod.ext <;> ext i <;> fin_cases i <;> simp
  map_add' x y := by apply Prod.ext <;> ext i <;> fin_cases i <;> simp
  map_smul' c x := by apply Prod.ext <;> ext i <;> fin_cases i <;> simp

def pairEquiv : E6 ≃L[ℝ] P := pairLinearEquiv.toContinuousLinearEquiv

def symbol (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  let f : E6 → ℂ := fun x ↦ (entry a.1 a.2 w v i (pairEquiv x) : ℂ)
  have hcompact : HasCompactSupport f := by
    have hreal : HasCompactSupport (entry a.1 a.2 w v i) :=
      ((isCompact_closedBall (0 : R3) 4).prod (isCompact_closedBall (0 : R3) 4)).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_entry_subset a.1 a.2 w v i)
    exact (hreal.comp_homeomorph pairEquiv.toHomeomorph).comp_left Complex.ofReal_zero
  have hcont : ContDiff ℝ ∞ f := by
    exact Complex.ofRealCLM.contDiff.comp
      ((contDiff_entry w v i).comp (contDiff_const.prodMk pairEquiv.contDiff))
  hcompact.toSchwartzMap hcont

@[simp] theorem symbol_apply (a : A) (w v : R3) (i : Fin 3) (x : E6) :
    symbol a w v i x = (entry a.1 a.2 w v i (pairEquiv x) : ℂ) := rfl

theorem contDiff_symbol (w v : R3) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × E6 ↦ symbol z.1 w v i z.2) := by
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_entry w v i).comp (contDiff_fst.prodMk (pairEquiv.contDiff.comp contDiff_snd)))

def commonSupport : Set E6 :=
  pairEquiv ⁻¹' (Metric.closedBall (0 : R3) 4 ×ˢ Metric.closedBall (0 : R3) 4)

theorem isCompact_commonSupport : IsCompact commonSupport :=
  pairEquiv.toHomeomorph.isCompact_preimage.mpr
    ((isCompact_closedBall (0 : R3) 4).prod (isCompact_closedBall (0 : R3) 4))

theorem tsupport_symbol_subset (a : A) (w v : R3) (i : Fin 3) :
    tsupport (symbol a w v i) ⊆ commonSupport := by
  apply closure_minimal _ isCompact_commonSupport.isClosed
  intro x hx
  apply tsupport_entry_subset a.1 a.2 w v i
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

end Mettapedia.FluidDynamics.NavierStokes.PressureLowOutputSymbol
