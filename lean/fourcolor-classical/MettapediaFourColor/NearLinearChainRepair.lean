import MettapediaFourColor.NearLinearChainData
import MettapediaFourColor.BoundaryTriangleRepair
import FourColor.Bulk.Cfg.Grp09_00

/-!
# Repair of a three-triangle chain by boundary transfer

Configuration 7's existing certified rank planes, after colour permutations,
cover every proper nine-port trace. A single bit-mask comparison checks
that fact. The certificate soundness and reconstruction are reused from the
audited Emery/Gonthier development; no complete Four Colour theorem is used.
-/

namespace FourColor.NearLinearChainRepair

open Color KempeBoundarySplit NearLinearChainData

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Compare the nine-port masks once, using the kernel’s big-natural operations.
theorem coverage_mask :
    (((2 ^ 3 ^ 8 - 1) ^^^ Bulk.xaccAt 8 8 0) &&&
      ((2 ^ 3 ^ 8 - 1) ^^^ Bulk.knownMask 8 Bulk.Cfg006.R)) = 0 := by
  decide +kernel

theorem base_coverage (j : ℕ) (hj : j < 3 ^ 8)
    (hs : (Bulk.partialOf 8 j).sum ≠ 0) :
    (Bulk.knownMask 8 Bulk.Cfg006.R).testBit j = true := by
  have h := congrArg (fun x => x.testBit j) coverage_mask
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Bulk.testBit_xaccAt (le_refl 8), hj, hs, and_false, decide_false,
    decide_true, Bool.xor_false, Bool.true_and, Nat.zero_testBit] at h
  cases hk : (Bulk.knownMask 8 Bulk.Cfg006.R).testBit j <;> simp_all

/-- The entire proper zero-sum domain, not merely the original contract's image. -/
theorem reference_repair :
    Repairs ((cfmap cf007).map.RingTrace (cfring cf007).reverse) 9 := by
  intro et hlen hzero hsum
  have htlen : et.tail.length = 8 := by simp [List.length_tail, hlen]
  have htzero : (0 : Color) ∉ et.tail := fun h => hzero (List.mem_of_mem_tail h)
  let j := Bulk.indexOf 8 et.tail
  have hj := Bulk.indexOf_lt 8 et.tail
  have hpartial : Bulk.partialOf 8 j = et.tail := Bulk.partialOf_indexOf htlen htzero
  have hrot : et.rotate 1 = Bulk.traceOf 8 j := by
    rw [Bulk.traceOf, hpartial]
    cases et with
    | nil => simp at hlen
    | cons e t =>
      rw [List.sum_cons] at hsum
      rw [List.rotate_cons_succ, List.rotate_zero, List.tail_cons, completeTrace,
        Color.add_eq_zero_iff.mp hsum]
  have hproper : (Bulk.partialOf 8 j).sum ≠ 0 := by
    intro hz
    have hzmem : (0 : Color) ∈ et.rotate 1 := by
      rw [hrot, Bulk.traceOf, completeTrace, hz]
      simp
    exact hzero (List.mem_rotate.mp hzmem)
  have hknown := Bulk.known_coclosure Bulk.Cfg006.cf 8 Bulk.Cfg006.hcf
    Bulk.Cfg006.R Bulk.Cfg006.H Bulk.Cfg006.C
    (by rw [Bulk.Cfg006.hH, Bulk.length_minPerm]) (by decide)
    Bulk.Cfg006.hH Bulk.Cfg006.hgood Bulk.Cfg006.hchoice Bulk.Cfg006.hpairs
    j hj (base_coverage j hj hproper)
  rw [← hrot] at hknown
  have hcf : Bulk.Cfg006.cf = cf007 := by rfl
  rw [hcf] at hknown
  have h := ring_rotate_back hknown
  simpa only [cfring, List.reverse_reverse] using h

theorem repair0006 : Repairs (GraphTrace input0006.graph boundary0006) 9 := by
  apply BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0006.graph)) boundary0006 boundary007 1
    (by decide +kernel)
  intro et hlen hzero hsum Q hQ hq
  obtain ⟨es, hs, hqs⟩ := reference_repair et hlen hzero hsum Q hQ hq
  exact ⟨es, (reducibilityTrace007 es).mp hs, hqs⟩


/-- The exact boundary subdivision transports repair from nine to eight ports.
The two new edge colours remain jointly constrained throughout Kempe closure. -/
theorem transfer46
    (base : Repairs (GraphTrace input0006.graph boundary0006) 9) :
    Repairs (GraphTrace input0004.graph boundary0004) 8 := by
  have split : Repairs (GraphTrace
      (Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.subdivide input0004.graph 5 4 10)
      (BoundaryTriangleRepair.ports 5 4 [3, 2, 1, 0, 7, 6])) 9 :=
    BoundaryRepairTransport.repairs insert46 _ boundary0006 4 (by decide +kernel) base
  have collapsed := BoundaryTriangleRepair.repair input0004.graph 5 4 10 [3, 2, 1, 0, 7, 6] split
  exact BoundaryRepairTransport.repairs (SimpleGraph.Iso.refl (G := input0004.graph)) boundary0004
    (5 :: 4 :: [3, 2, 1, 0, 7, 6]) 2 (by decide +kernel) collapsed

/-- D0004 needs no separate rank or colouring table. -/
theorem repair0004 : Repairs (GraphTrace input0004.graph boundary0004) 8 :=
  transfer46 repair0006

/-- The repair produces a genuine colouring compatible with the same joint
exterior relation. Realizing that relation in an ambient map is separate. -/
theorem reconstruct (et : List Color) (length : et.length = 8)
    (proper : (0 : Color) ∉ et) (conserved : et.sum = 0)
    (Q : List Color → Prop) (closed : KempeClosed Q) (outside : Q et) :
    ∃ k : input0004.graph.Coloring Color, Q (trace (boundary0004.map k)) := by
  obtain ⟨es, ⟨k, rfl⟩, hQ⟩ := repair0004 et length proper conserved Q closed outside
  exact ⟨k, hQ⟩

end FourColor.NearLinearChainRepair
