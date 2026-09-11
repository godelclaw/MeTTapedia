import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureDyadicSymbol
import Mettapedia.Analysis.CompactFourierEnvelope

/-!
# An exact smooth secant family for pressure directions

The normalized pressure symbol is linear minus cubic in its direction.
A centered cubic-exact derivative stencil, followed by Simpson's identity,
factors its direction difference without division by the direction gap.
The secant family has the same compact frequency support as the original
symbol. Its inverse Fourier kernels therefore have uniform moments.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureDirectionSecant

open MeasureTheory PressureDyadicSymbol PressureLowOutputSymbol
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "A" => ℝ × R3 × R3 × R3

def directionalStencil (t : ℝ) (e h w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  (1 / 2 : ℝ) • (PressureDyadicSymbol.symbol (t, e + h) w v i -
    PressureDyadicSymbol.symbol (t, e - h) w v i) -
  (1 / 6 : ℝ) • (PressureDyadicSymbol.symbol (t, (2 : ℝ) • h) w v i -
    (2 : ℝ) • PressureDyadicSymbol.symbol (t, h) w v i)

def symbol (a : A) (w v : R3) (i : Fin 3) : 𝓢(E6, ℂ) :=
  (1 / 6 : ℝ) • (directionalStencil a.1 a.2.1 a.2.2.2 w v i +
    (4 : ℝ) • directionalStencil a.1 ((1 / 2 : ℝ) • (a.2.1 + a.2.2.1)) a.2.2.2 w v i +
    directionalStencil a.1 a.2.2.1 a.2.2.2 w v i)

theorem symbol_sub_eq_smul (t : ℝ) (e f h w v : R3) (i : Fin 3) (d : ℝ)
    (hd : e - f = d • h) :
    PressureDyadicSymbol.symbol (t, e) w v i - PressureDyadicSymbol.symbol (t, f) w v i =
      d • symbol (t, e, f, h) w v i := by
  have he : e = f + d • h := by rw [← hd]; abel
  rw [he]
  ext x
  simp only [symbol, directionalStencil, sub_apply, add_apply,
    smul_apply, PressureDyadicSymbol.symbol_apply, PressureDyadicSymbol.entry,
    PressureLowOutputSymbol.entry, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, PiLp.add_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem contDiff_symbol (w v : R3) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : A × E6 ↦ symbol z.1 w v i z.2) := by
  have hs (g : A × E6 → R3) (hg : ContDiff ℝ ∞ g) :
      ContDiff ℝ ∞ (fun z : A × E6 ↦ PressureDyadicSymbol.symbol (z.1.1, g z) w v i z.2) := by
    have hm : ContDiff ℝ ∞ (fun z : A × E6 ↦ ((z.1.1, g z), z.2)) := by fun_prop
    simpa only [Function.comp_def] using (PressureDyadicSymbol.contDiff_symbol w v i).comp hm
  have hd (g : A × E6 → R3) (hg : ContDiff ℝ ∞ g) :
      ContDiff ℝ ∞ (fun z : A × E6 ↦ directionalStencil z.1.1 (g z) z.1.2.2.2 w v i z.2) := by
    have hh : ContDiff ℝ ∞ (fun z : A × E6 ↦ z.1.2.2.2) := by fun_prop
    exact (((hs _ (hg.add hh)).sub (hs _ (hg.sub hh))).const_smul (1 / 2 : ℝ)).sub
      (((hs _ (hh.const_smul (2 : ℝ))).sub ((hs _ hh).const_smul (2 : ℝ))).const_smul (1 / 6 : ℝ))
  exact (((hd _ (by fun_prop)).add ((hd _ (by fun_prop)).const_smul (4 : ℝ))).add
    (hd _ (by fun_prop))).const_smul (1 / 6 : ℝ)

theorem tsupport_symbol_subset (a : A) (w v : R3) (i : Fin 3) :
    tsupport (symbol a w v i) ⊆ commonSupport := by
  apply closure_minimal _ isCompact_commonSupport.isClosed
  intro x hx
  by_contra hn
  have hz (b : ℝ × R3) : PressureDyadicSymbol.symbol b w v i x = 0 := by
    by_contra h
    exact hn (PressureDyadicSymbol.tsupport_symbol_subset b w v i (subset_tsupport _ h))
  apply hx
  simp [symbol, directionalStencil, hz]

def parameterSet : Set A := Set.Icc (0 : ℝ) (1 / 2) ×ˢ
  Metric.closedBall (0 : R3) 1 ×ˢ Metric.closedBall (0 : R3) 1 ×ˢ Metric.closedBall (0 : R3) 1

theorem isCompact_parameterSet : IsCompact parameterSet :=
  isCompact_Icc.prod ((isCompact_closedBall (0 : R3) 1).prod
    ((isCompact_closedBall (0 : R3) 1).prod (isCompact_closedBall (0 : R3) 1)))

theorem mem_parameterSet (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2))
    (e f h : R3) (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1) (hh : ‖h‖ ≤ 1) :
    (t, e, f, h) ∈ parameterSet := by
  simpa only [parameterSet, Set.mem_prod, Metric.mem_closedBall, dist_zero_right] using
    And.intro ht (And.intro he (And.intro hf hh))

theorem exists_uniform_moment (w v : R3) (i : Fin 3) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e f h : R3,
      ‖e‖ ≤ 1 → ‖f‖ ≤ 1 → ‖h‖ ≤ 1 →
      (∫ x : E6, ‖x‖ ^ m * ‖(𝓕⁻ (symbol (t, e, f, h) w v i)) x‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := Mettapedia.Analysis.CompactSchwartzFamily.exists_uniform_fourierInv_moment
    (fun a ↦ symbol a w v i) (contDiff_symbol w v i) parameterSet isCompact_parameterSet
    commonSupport isCompact_commonSupport (fun a ↦ tsupport_symbol_subset a w v i) m
  exact ⟨C, hC, fun t ht e f h he hf hh ↦ hb _ (mem_parameterSet t ht e f h he hf hh)⟩

end Mettapedia.FluidDynamics.NavierStokes.PressureDirectionSecant
