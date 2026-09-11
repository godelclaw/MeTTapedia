import Mettapedia.Analysis.CompactFourierEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceKernel
import Mathlib.Tactic.DeriveFintype

/-!
# Smooth coherent pressure channels with input-frequency factors

The undifferentiated symbol and its six normalized input-coordinate
multiples share a compact frequency support. One continuous integrable
envelope dominates all inverse transforms, all channels, and all unit
directions. Derivatives of transverse inputs can therefore be transferred
to these kernels without assuming pointwise multiplier bounds control
operator norms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannel

open MeasureTheory Mettapedia.Analysis.CompactFourierEnvelope
open PressureLowOutputCutoff (receiver contDiff_receiver)
open PressureLowOutputSymbol (pairEquiv commonSupport isCompact_commonSupport)
open PressureLowOutputKernel (parameterSet isCompact_parameterSet mem_parameterSet)
open scoped ContDiff SchwartzMap FourierTransform

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3
local notation "A" => ℝ × R3

inductive Factor where
  | undifferentiated
  | first (coordinate : Fin 3)
  | second (coordinate : Fin 3)
  deriving DecidableEq, Fintype

def multiplier : Factor → ℝ → P → ℝ
  | .undifferentiated, _, _ => 1
  | .first j, _, p => p.1 j
  | .second j, t, p => receiver t p j

theorem contDiff_multiplier (c : Factor) :
    ContDiff ℝ ∞ (fun z : A × P ↦ multiplier c z.1.1 z.2) := by
  cases c with
  | undifferentiated => exact contDiff_const
  | first j => change ContDiff ℝ ∞ (fun z : A × P ↦ z.2.1 j); fun_prop
  | second j =>
    have hm : ContDiff ℝ ∞ (fun z : A × P ↦ (z.1.1, z.2)) := by fun_prop
    have hr : ContDiff ℝ ∞ (fun z : A × P ↦ receiver z.1.1 z.2) := by
      simpa only [Function.comp_def] using contDiff_receiver.comp hm
    exact (contDiff_piLp 2).1 hr j

def entry (t : ℝ) (e : R3) (c : Factor) (i : Fin 3) (p : P) : ℝ :=
  multiplier c t p * PressureCoherentDivergenceSymbol.entry t e i p

theorem contDiff_entry (c : Factor) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × P ↦ entry z.1.1 z.1.2 c i z.2) :=
  (contDiff_multiplier c).mul (PressureCoherentDivergenceSymbol.contDiff_entry i)

theorem tsupport_entry_subset (t : ℝ) (e : R3) (c : Factor) (i : Fin 3) :
    tsupport (entry t e c i) ⊆ Metric.closedBall (0 : R3) 4 ×ˢ Metric.closedBall (0 : R3) 4 :=
  tsupport_mul_subset_right.trans (PressureCoherentDivergenceSymbol.tsupport_entry_subset t e i)

def symbol (a : A) (c : Factor) (i : Fin 3) : 𝓢(E6, ℂ) :=
  let f : E6 → ℂ := fun x ↦ (entry a.1 a.2 c i (pairEquiv x) : ℂ)
  have hcompact : HasCompactSupport f := by
    have hreal : HasCompactSupport (entry a.1 a.2 c i) :=
      ((isCompact_closedBall (0 : R3) 4).prod (isCompact_closedBall (0 : R3) 4)).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_entry_subset a.1 a.2 c i)
    exact (hreal.comp_homeomorph pairEquiv.toHomeomorph).comp_left Complex.ofReal_zero
  have hcont : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_entry c i).comp (contDiff_const.prodMk pairEquiv.contDiff))
  hcompact.toSchwartzMap hcont

@[simp] theorem symbol_apply (a : A) (c : Factor) (i : Fin 3) (x : E6) :
    symbol a c i x = (entry a.1 a.2 c i (pairEquiv x) : ℂ) := rfl

theorem contDiff_symbol (c : Factor) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × E6 ↦ symbol z.1 c i z.2) :=
  Complex.ofRealCLM.contDiff.comp
    ((contDiff_entry c i).comp (contDiff_fst.prodMk (pairEquiv.contDiff.comp contDiff_snd)))

theorem tsupport_symbol_subset (a : A) (c : Factor) (i : Fin 3) :
    tsupport (symbol a c i) ⊆ commonSupport := by
  apply closure_minimal _ isCompact_commonSupport.isClosed
  intro x hx
  apply tsupport_entry_subset a.1 a.2 c i
  apply subset_tsupport
  intro hz
  exact hx (by simp [hz])

@[simp] theorem symbol_undifferentiated (a : A) (i : Fin 3) :
    symbol a .undifferentiated i = PressureCoherentDivergenceSymbol.symbol a i := by
  ext x
  simp [entry, multiplier]

def kernel (a : A) (c : Factor) (i : Fin 3) : 𝓢(E6, ℂ) := 𝓕⁻ (symbol a c i)

@[simp] theorem fourier_kernel (a : A) (c : Factor) (i : Fin 3) :
    𝓕 (kernel a c i) = symbol a c i := FourierTransform.fourier_fourierInv_eq _

@[simp] theorem kernel_undifferentiated (a : A) (i : Fin 3) :
    kernel a .undifferentiated i = PressureCoherentDivergenceKernel.kernel a i := by
  simp [kernel, PressureCoherentDivergenceKernel.kernel]

theorem exists_uniform_envelope (m : ℕ) :
    ∃ H : E6 → ℝ, (∀ x, 0 ≤ H x) ∧ Continuous H ∧ Integrable H ∧
      Integrable (fun x ↦ ‖x‖ ^ m * H x) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 →
      ∀ c : Factor, ∀ i : Fin 3, ∀ x, ‖kernel (t, e) c i x‖ ≤ H x := by
  classical
  choose H hn hc hi hm hb using fun a : Factor × Fin 3 ↦
    exists_uniform_fourierInv_envelope (fun p ↦ symbol p a.1 a.2)
      (contDiff_symbol a.1 a.2) parameterSet isCompact_parameterSet
      commonSupport isCompact_commonSupport (fun p ↦ tsupport_symbol_subset p a.1 a.2) m
  refine ⟨fun x ↦ ∑ a, H a x, fun x ↦ Finset.sum_nonneg (fun a _ ↦ hn a x),
    continuous_finsetSum _ (fun a _ ↦ hc a), integrable_finsetSum _ (fun a _ ↦ hi a), ?_, ?_⟩
  · simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun a _ ↦ hm a)
  · intro t ht e he c i x
    exact (hb (c, i) (t, e) (mem_parameterSet t ht e he) x).trans
      (Finset.single_le_sum (fun a _ ↦ hn a x) (Finset.mem_univ (c, i)))

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannel
