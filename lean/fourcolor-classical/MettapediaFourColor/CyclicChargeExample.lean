import MettapediaFourColor.CyclicFanContinuation
import MettapediaFourColor.ChainBoundaryGeometry

/-! Two receiver degrees consume the same cyclic charge law on the
retained finite triangulation. No minimal-counterexample assumption is
made for these examples. Exact full charges are checked separately. -/

namespace FourColor.CyclicChargeExample

open ChainBoundaryExample CyclicCharge

set_option maxRecDepth 65536

theorem eight_degree : graph.degree 69 = 8 := by decide +kernel
theorem seven_degree : graph.degree 150 = 7 := by decide +kernel

set_option maxHeartbeats 0 in
-- Replay the finite neighbourhood and its shared outer tips in the kernel.
theorem eight_low : ∀ w, graph.Adj 69 w → 5 ≤ graph.degree w ∧ graph.degree w ≤ 6 := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Replay the finite neighbourhood and its shared outer tips in the kernel.
theorem seven_low : ∀ w, graph.Adj 150 w → 5 ≤ graph.degree w ∧ graph.degree w ≤ 6 := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Replay the finite neighbourhood and its shared outer tips in the kernel.
theorem eight_counts : fiveCount (G := graph) 69 = 5 ∧ tipCount rotation 69 = 1 := by
  decide +kernel
set_option maxHeartbeats 0 in
-- Replay the finite neighbourhood and its shared outer tips in the kernel.
theorem seven_counts : fiveCount (G := graph) 150 = 4 ∧ tipCount rotation 150 = 1 := by
  decide +kernel

theorem eight_positive : 2 ≤ NearLinearCharge.finalCharge rotation 69 := by
  have h := lower rotation triangular 69 (by rw [eight_degree]; decide) eight_low
  rw [eight_degree, eight_counts.1, eight_counts.2] at h
  convert h using 1
  norm_num

theorem seven_positive : 8 ≤ NearLinearCharge.finalCharge rotation 150 := by
  have h := lower rotation triangular 150 (by rw [seven_degree]) seven_low
  rw [seven_degree, seven_counts.1, seven_counts.2] at h
  convert h using 1
  norm_num

end FourColor.CyclicChargeExample
