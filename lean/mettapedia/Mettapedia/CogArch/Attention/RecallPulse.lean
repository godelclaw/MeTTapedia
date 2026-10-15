import Mettapedia.CogArch.Attention.Spreading

/-!
# One-hop attention from recall

A new recall pulse spreads once. Transporting it does not manufacture another
recall event. The source of a pulse and the semantic associations remain choices
of the consumer; these laws do not assert retrieval usefulness or truth.
The real-number model does not certify floating-point arithmetic.
-/

noncomputable section
namespace Mettapedia.CogArch.Attention.RecallPulse
open Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def update (P : Kernel ι) (retention spread : ℝ) (old pulse : ι → ℝ) (j : ι) : ℝ :=
  retention * old j + step P spread pulse j

theorem update_mass (P : Kernel ι) (r d : ℝ) (old pulse : ι → ℝ) :
    mass (update P r d old pulse) = r * mass old + mass pulse := by
  simp only [update, mass, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact congrArg (fun x => r * mass old + x) (step_mass P d pulse)

theorem update_nonneg (P : Kernel ι) (r d : ℝ) (hr : 0 ≤ r)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (old pulse : ι → ℝ)
    (ho : ∀ i, 0 ≤ old i) (hu : ∀ i, 0 ≤ pulse i) (j : ι) :
    0 ≤ update P r d old pulse j :=
  add_nonneg (mul_nonneg hr (ho j)) (step_nonneg P d hd0 hd1 pulse hu j)

theorem direct_contribution (P : Kernel ι) (r d : ℝ) (hr : 0 ≤ r)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (old pulse : ι → ℝ)
    (ho : ∀ k, 0 ≤ old k) (hu : ∀ k, 0 ≤ pulse k) (i j : ι) :
    d * (pulse i * Kernel.share P i j) ≤ update P r d old pulse j := by
  have hterm : pulse i * Kernel.share P i j ≤ transport P pulse j :=
    Finset.single_le_sum (fun k _ => mul_nonneg (hu k) (Kernel.nonneg P k j))
      (Finset.mem_univ i)
  have hscaled := mul_le_mul_of_nonneg_left hterm hd0
  have hret := mul_nonneg hr (ho j)
  have hself := mul_nonneg (sub_nonneg.mpr hd1) (hu j)
  unfold update step
  linarith

theorem no_incoming_pulse (P : Kernel ι) (d : ℝ) (pulse : ι → ℝ) (j : ι)
    (hself : pulse j = 0) (hedges : ∀ i, pulse i * Kernel.share P i j = 0) :
    step P d pulse j = 0 := by
  simp [step, transport, hself, hedges]

/-- The pulse is paid from the STI reserve; other horizons are unchanged. -/
def pay (P : Kernel ι) (d : ℝ) (pulse : ι → ℝ)
    (b : ThreeTimescale.Bank ι) : ThreeTimescale.Bank ι where
  values i h := match h with
    | .sti => b.values i .sti + step P d pulse i
    | .mti => b.values i .mti
    | .lti => b.values i .lti
  reserve h := match h with
    | .sti => b.reserve .sti - mass pulse
    | .mti => b.reserve .mti
    | .lti => b.reserve .lti

theorem pay_total (P : Kernel ι) (d : ℝ) (pulse : ι → ℝ)
    (b : ThreeTimescale.Bank ι) (h : ThreeTimescale.Horizon) :
    ThreeTimescale.total (pay P d pulse b) h = ThreeTimescale.total b h := by
  cases h with
  | sti =>
    simp only [ThreeTimescale.total, pay, Finset.sum_add_distrib]
    change b.reserve .sti - mass pulse + (mass (fun i => b.values i .sti) +
      mass (step P d pulse)) = b.reserve .sti + mass (fun i => b.values i .sti)
    rw [step_mass]
    ring
  | mti => rfl
  | lti => rfl

/-- A semantic prior fills an absent key and preserves an existing association. -/
def initializeEdge [DecidableEq ι] (edges : (ι × ι) → Option ℝ) (edge : ι × ι)
    (weight : ℝ) : (ι × ι) → Option ℝ :=
  if (edges edge).isSome then edges else Function.update edges edge (some weight)

omit [Fintype ι] in
theorem initializeEdge_idempotent [DecidableEq ι] (edges : (ι × ι) → Option ℝ)
    (edge : ι × ι) (weight : ℝ) :
    initializeEdge (initializeEdge edges edge weight) edge weight = initializeEdge edges edge weight := by
  cases h : edges edge <;> simp [initializeEdge, h]

end Mettapedia.CogArch.Attention.RecallPulse
