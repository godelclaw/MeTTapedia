import MettapediaFourColor.KempeBoundarySplit
import FourColor.Bulk.Reducible

/-!
# From complete rank coverage to joint boundary repair

The certified rank planes of a configuration sometimes cover every proper
zero-sum boundary trace, even when its recorded reducibility uses a contract.
This theorem exposes that stronger conclusion without using the contract.
The rank certificate and its soundness are from the Emery/Gonthier development.
-/

namespace FourColor.FullRankRepair

open Color KempeBoundarySplit

theorem coverage {m : ℕ} {R : List ℕ}
    (mask : (((2 ^ 3 ^ m - 1) ^^^ Bulk.xaccAt m m 0) &&&
      ((2 ^ 3 ^ m - 1) ^^^ Bulk.knownMask m R)) = 0)
    (j : ℕ) (hj : j < 3 ^ m) (hs : (Bulk.partialOf m j).sum ≠ 0) :
    (Bulk.knownMask m R).testBit j = true := by
  have h := congrArg (fun x => x.testBit j) mask
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Bulk.testBit_xaccAt (le_refl m), hj, hs, and_false, decide_false,
    decide_true, Bool.xor_false, Bool.true_and, Nat.zero_testBit] at h
  cases hk : (Bulk.knownMask m R).testBit j <;> simp_all

/-- Full proper-domain coverage gives repair against the same Kempe-closed
exterior relation. No assumption about a contracted graph is needed. -/
theorem repairs (cf : Config) (m : ℕ) (hcf : cprsize cf.prog = m + 1)
    (R H C : List ℕ) (hlenH : R.length = H.length) (hClen : m < 2 ^ C.length)
    (hH : H = Bulk.minPerm m R) (hgood : Bulk.goodCheck m R cf.prog = true)
    (hchoice : Bulk.choiceCheck m R C = true) (hpairs : Bulk.allPairs m R H C = true)
    (mask : (((2 ^ 3 ^ m - 1) ^^^ Bulk.xaccAt m m 0) &&&
      ((2 ^ 3 ^ m - 1) ^^^ Bulk.knownMask m R)) = 0) :
    Repairs ((cfmap cf).map.RingTrace (cfring cf).reverse) (m + 1) := by
  intro et hlen hzero hsum
  have htlen : et.tail.length = m := by simp [List.length_tail, hlen]
  have htzero : (0 : Color) ∉ et.tail := fun h => hzero (List.mem_of_mem_tail h)
  let j := Bulk.indexOf m et.tail
  have hj := Bulk.indexOf_lt m et.tail
  have hpartial : Bulk.partialOf m j = et.tail := Bulk.partialOf_indexOf htlen htzero
  have hrot : et.rotate 1 = Bulk.traceOf m j := by
    rw [Bulk.traceOf, hpartial]
    cases et with
    | nil => simp at hlen
    | cons e t =>
      rw [List.sum_cons] at hsum
      rw [List.rotate_cons_succ, List.rotate_zero, List.tail_cons, completeTrace,
        Color.add_eq_zero_iff.mp hsum]
  have hproper : (Bulk.partialOf m j).sum ≠ 0 := by
    intro hz
    have hzmem : (0 : Color) ∈ et.rotate 1 := by
      rw [hrot, Bulk.traceOf, completeTrace, hz]
      simp
    exact hzero (List.mem_rotate.mp hzmem)
  have hknown := Bulk.known_coclosure cf m hcf R H C hlenH hClen
    hH hgood hchoice hpairs j hj (coverage mask j hj hproper)
  rw [← hrot] at hknown
  simpa only [cfring, List.reverse_reverse] using ring_rotate_back hknown

end FourColor.FullRankRepair
