import Mettapedia.CognitiveArchitecture.Attention.Spreading

/-!
# Restart-walk views of caller-scheduled STI dynamics

The ECAN library exposes separate stimulate, source-local spread and decay
operations. It has no fixed cycle order. A fixed kernel here is a hypothesis
about a caller's repeated linear schedule, not a claim that the runtime performs
synchronous global sweeps. Stimulate/spread/decay has effective input ρ M u;
spread/decay/stimulate has effective input u. Variable inputs are unrolled below.
Consolidation does not change STI. Reserves and the slower tiers are not modelled
by this affine slice; their conservation laws remain in ThreeTimescale.
-/

noncomputable section
namespace Mettapedia.CognitiveArchitecture.Attention.Equilibrium
open scoped BigOperators Classical
open Matrix Finset
open Mettapedia.ProbabilityTheory.MarkovChain
open Restart
open FiniteMassTransport (Kernel restartingWalk)
variable {ι : Type*} [Fintype ι]

/-- A lazy outgoing kernel, constructed in mathlib's row-stochastic submonoid. -/
def lazyKernel (P : Kernel ι) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) : Kernel ι :=
  ⟨(fun i j => (1-d) * (if i = j then 1 else 0) +
      d * FiniteMassTransport.Kernel.share P i j),
    Matrix.mem_rowStochastic_iff_sum.mpr ⟨by
      intro i j
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hd1) (by
        split <;> norm_num))
        (mul_nonneg hd0 (FiniteMassTransport.Kernel.nonneg P i j)), by
      intro i
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ j, if i = j then (1:ℝ) else 0) = 1 by simp,
        FiniteMassTransport.Kernel.row_sum P i]
      ring⟩⟩

theorem lazy_transport (P : Kernel ι) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (x : ι → ℝ) (i : ι) :
    FiniteMassTransport.transport (lazyKernel P d hd0 hd1) x i =
      (1-d) * x i + d * FiniteMassTransport.transport P x i := by
  simp [FiniteMassTransport.transport, lazyKernel, FiniteMassTransport.Kernel.share,
    mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, mul_comm,
    mul_left_comm]

def continuation (ρ d : ℝ) : ℝ := ρ * d / (1 - ρ + ρ * d)

theorem continuation_nonneg (ρ d : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd : 0 ≤ d) :
    0 ≤ continuation ρ d := by
  exact div_nonneg (mul_nonneg hρ0 hd)
    (by linarith [mul_nonneg hρ0 hd] : 0 ≤ 1 - ρ + ρ*d)

theorem continuation_lt_one (ρ d : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd : 0 ≤ d) :
    continuation ρ d < 1 := by
  have hden : 0 < 1 - ρ + ρ*d := by linarith [mul_nonneg hρ0 hd]
  exact (div_lt_one hden).mpr (by linarith)

/-- Laziness changes the effective restart parameter, not the equilibrium seed. -/
theorem lazy_ppr_eq_ppr (P : Kernel ι) (d ρ : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (s : ι → ℝ) :
    (restartingWalk (lazyKernel P d hd0 hd1) ρ hρ0 hρ1).ppr s =
    (restartingWalk P (continuation ρ d)
      (continuation_nonneg ρ d hρ0 hρ1 hd0)
      (continuation_lt_one ρ d hρ0 hρ1 hd0)).ppr s := by
  let L := restartingWalk (lazyKernel P d hd0 hd1) ρ hρ0 hρ1
  let x := L.ppr s
  apply Restart.RestartWalk.ppr_unique
  rw [← FiniteMassTransport.restart_eq_walk_step]
  funext i
  have hf : FiniteMassTransport.restart (lazyKernel P d hd0 hd1) ρ s x = x := by
    rw [FiniteMassTransport.restart_eq_walk_step _ _ hρ0 hρ1]
    exact L.ppr_fixed s
  have hfi := congrFun hf i
  dsimp only [FiniteMassTransport.restart] at hfi ⊢
  rw [lazy_transport] at hfi
  have hd : 1 - ρ + ρ*d ≠ 0 := ne_of_gt (by linarith [mul_nonneg hρ0 hd0])
  unfold continuation
  field_simp
  nlinarith [hfi]

/-- Geometric mean hops after removing lazy self-steps. -/
theorem mean_hops (ρ d : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hd0 : 0 ≤ d) :
    continuation ρ d / (1 - continuation ρ d) = ρ*d / (1-ρ) := by
  have hden : 1 - ρ + ρ*d ≠ 0 := ne_of_gt (by linarith [mul_nonneg hρ0 hd0])
  have hρ : 1 - ρ ≠ 0 := ne_of_gt (sub_pos.mpr hρ1)
  unfold continuation
  field_simp [hden, hρ]
  ring

/-- Discounted transport, not a second definition of restart or l1. -/
def impulse (W : RestartWalk ι) (n : ℕ) (v : ι → ℝ) : ι → ℝ :=
  (1-W.α)^n • ((W.P^n) *ᵥ v)

@[simp] theorem impulse_zero (W : RestartWalk ι) (v : ι → ℝ) : impulse W 0 v = v := by
  simp [impulse]

theorem impulse_add (W : RestartWalk ι) (n : ℕ) (x y : ι → ℝ) :
    impulse W n (x+y) = impulse W n x + impulse W n y := by
  simp [impulse, Matrix.mulVec_add, smul_add]

theorem impulse_succ (W : RestartWalk ι) (n : ℕ) (v : ι → ℝ) :
    impulse W 1 (impulse W n v) = impulse W (n+1) v := by
  simp [impulse, Matrix.mulVec_smul, smul_smul,
    ← Matrix.mulVec_mulVec, pow_succ']

def stiRun (W : RestartWalk ι) (u : ℕ → ι → ℝ) (v : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => v
  | t+1 => W.step (W.α⁻¹ • u t) (stiRun W u v t)

theorem sti_cycle (W : RestartWalk ι) (u v : ι → ℝ) :
    W.step (W.α⁻¹ • u) v = u + impulse W 1 v := by
  simp [Restart.RestartWalk.step, impulse, smul_smul, ne_of_gt W.α_pos]

/-- Stimulus before spread and decay is itself spread and decayed. -/
theorem stimulate_spread_decay (W : RestartWalk ι) (raw v : ι → ℝ) :
    impulse W 1 (v + raw) =
      W.step (W.α⁻¹ • impulse W 1 raw) v := by
  rw [sti_cycle, impulse_add, add_comm]

/-- Arbitrary effective inputs, in the caller's chosen fixed linear schedule. -/
theorem sti_unroll (W : RestartWalk ι) (u : ℕ → ι → ℝ) (v : ι → ℝ) (t : ℕ) :
    stiRun W u v t = impulse W t v +
      ∑ τ ∈ Finset.range t, impulse W (t-1-τ) (u τ) := by
  induction t with
  | zero => simp [stiRun]
  | succ t ih =>
    rw [stiRun, sti_cycle, ih, impulse_add, impulse_succ, Finset.sum_range_succ]
    have hsum : impulse W 1 (∑ τ ∈ range t, impulse W (t-1-τ) (u τ)) =
        ∑ τ ∈ range t, impulse W (t-τ) (u τ) := by
      simp only [impulse, Matrix.mulVec_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro τ hτ
      have ht : t-τ = (t-1-τ)+1 := by have := mem_range.mp hτ; omega
      rw [ht]
      exact impulse_succ W (t-1-τ) (u τ)
    rw [hsum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, impulse_zero]
    abel

/-- Constant effective input has the scaled PPR equilibrium and a geometric
error bound. It does not claim an arbitrary caller uses this schedule. -/
theorem sti_steady_state (W : RestartWalk ι) (u v : ι → ℝ) (t : ℕ) :
    l1 (stiRun W (fun _ => u) v t - W.α⁻¹ • W.ppr u) ≤
      (1-W.α)^t * l1 (v - W.α⁻¹ • W.ppr u) := by
  have hi : stiRun W (fun _ => u) v t = (W.step (W.α⁻¹ • u))^[t] v := by
    induction t with
    | zero => rfl
    | succ t ih => simp [stiRun, ih, Function.iterate_succ_apply']
  rw [hi, ← W.ppr_smul]
  exact W.iterate_error _ _ _

/-- Hops are counted in the non-lazy graph, with effective continuation c. -/
theorem lazy_ppr_tail (P : Kernel ι) (d ρ : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (k : ℕ) :
    let V := restartingWalk P (continuation ρ d)
      (continuation_nonneg ρ d hρ0 hρ1 hd0)
      (continuation_lt_one ρ d hρ0 hρ1 hd0)
    ∑ i ∈ (V.reach s k)ᶜ, (restartingWalk (lazyKernel P d hd0 hd1) ρ hρ0 hρ1).ppr s i ≤
      (continuation ρ d)^(k+1) * mass s := by
  dsimp only
  rw [lazy_ppr_eq_ppr]
  simpa [restartingWalk] using (restartingWalk P (continuation ρ d)
    (continuation_nonneg ρ d hρ0 hρ1 hd0)
    (continuation_lt_one ρ d hρ0 hρ1 hd0)).mass_outside_reach hs k

end Mettapedia.CognitiveArchitecture.Attention.Equilibrium
