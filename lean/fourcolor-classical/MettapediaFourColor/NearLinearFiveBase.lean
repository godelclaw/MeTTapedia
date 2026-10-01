import MettapediaFourColor.NearLinearFiveData
import MettapediaFourColor.BoundaryTriangleRepair
import FourColor.Bulk.Cfg.Grp14_02

/-!
# The retained classical base for five near-linear entries

Configuration 225's existing certified rank planes, after colour permutations,
cover every proper fourteen-port trace. A single bit-mask comparison checks
that fact. The certificate soundness and reconstruction are reused from the
audited Emery/Gonthier development; no complete Four Colour theorem is used.
-/

namespace FourColor.NearLinearFiveBase

open Color KempeBoundarySplit NearLinearFiveData

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Compare the fourteen-port masks once, using the kernel’s big-natural operations.
theorem coverage_mask :
    (((2 ^ 3 ^ 13 - 1) ^^^ Bulk.xaccAt 13 13 0) &&&
      ((2 ^ 3 ^ 13 - 1) ^^^ Bulk.knownMask 13 Bulk.Cfg224.R)) = 0 := by
  decide +kernel

theorem base_coverage (j : ℕ) (hj : j < 3 ^ 13)
    (hs : (Bulk.partialOf 13 j).sum ≠ 0) :
    (Bulk.knownMask 13 Bulk.Cfg224.R).testBit j = true := by
  have h := congrArg (fun x => x.testBit j) coverage_mask
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Bulk.testBit_xaccAt (le_refl 13), hj, hs, and_false, decide_false,
    decide_true, Bool.xor_false, Bool.true_and, Nat.zero_testBit] at h
  cases hk : (Bulk.knownMask 13 Bulk.Cfg224.R).testBit j <;> simp_all

/-- The entire proper zero-sum domain, not merely the original contract's image. -/
theorem reference_repair :
    Repairs ((cfmap cf225).map.RingTrace (cfring cf225).reverse) 14 := by
  intro et hlen hzero hsum
  have htlen : et.tail.length = 13 := by simp [List.length_tail, hlen]
  have htzero : (0 : Color) ∉ et.tail := fun h => hzero (List.mem_of_mem_tail h)
  let j := Bulk.indexOf 13 et.tail
  have hj := Bulk.indexOf_lt 13 et.tail
  have hpartial : Bulk.partialOf 13 j = et.tail := Bulk.partialOf_indexOf htlen htzero
  have hrot : et.rotate 1 = Bulk.traceOf 13 j := by
    rw [Bulk.traceOf, hpartial]
    cases et with
    | nil => simp at hlen
    | cons e t =>
      rw [List.sum_cons] at hsum
      rw [List.rotate_cons_succ, List.rotate_zero, List.tail_cons, completeTrace,
        Color.add_eq_zero_iff.mp hsum]
  have hproper : (Bulk.partialOf 13 j).sum ≠ 0 := by
    intro hz
    have hzmem : (0 : Color) ∈ et.rotate 1 := by
      rw [hrot, Bulk.traceOf, completeTrace, hz]
      simp
    exact hzero (List.mem_rotate.mp hzmem)
  have hknown := Bulk.known_coclosure Bulk.Cfg224.cf 13 Bulk.Cfg224.hcf
    Bulk.Cfg224.R Bulk.Cfg224.H Bulk.Cfg224.C
    (by rw [Bulk.Cfg224.hH, Bulk.length_minPerm]) (by decide)
    Bulk.Cfg224.hH Bulk.Cfg224.hgood Bulk.Cfg224.hchoice Bulk.Cfg224.hpairs
    j hj (base_coverage j hj hproper)
  rw [← hrot] at hknown
  have hcf : Bulk.Cfg224.cf = cf225 := by rfl
  rw [hcf] at hknown
  have h := ring_rotate_back hknown
  simpa only [cfring, List.reverse_reverse] using h

theorem repair0604 : Repairs (GraphTrace input0604.graph boundary0604) 14 := by
  apply BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0604.graph)) boundary0604 boundary225 4
    (by decide +kernel)
  intro et hlen hzero hsum Q hQ hq
  obtain ⟨es, hs, hqs⟩ := reference_repair et hlen hzero hsum Q hQ hq
  exact ⟨es, (reducibilityTrace225 es).mp hs, hqs⟩

end FourColor.NearLinearFiveBase
