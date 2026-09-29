import MettapediaFourColor.KempeBoundarySplit
import MettapediaFourColor.DiamondContract
import FourColor.Bulk.Cfg.Grp07_00

/-!
# Repair descends through the first diamond insertion

Configuration 2's reference certificate covers every proper boundary trace.
The boundary-splitting law transfers that repair to configuration 1. Actual
graph colourings restrict across the inserted boundary triangle, and the
ordered ring traces collapse exactly. Configuration 1 therefore needs no
independent reducibility certificate.

The base certificate and its checker are Chris Emery's Lean realization of
the Robertson--Sanders--Seymour--Thomas and Gonthier--Werner mathematics. The
transfer does not assert that insertion in the opposite direction preserves
reducibility, or that the same contract works for longer fans.
-/

namespace FourColor.DiamondSplitRepair

open Color DiamondConfigurations KempeBoundarySplit

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Inspect the 729 positions of the existing rank planes once.
/-- The existing base ranks cover all 546 proper seven-port traces. -/
theorem base_coverage : ∀ j : Fin (3 ^ 6),
    (Bulk.partialOf 6 j.val).sum ≠ 0 →
      (Bulk.knownMask 6 Bulk.Cfg001.R).testBit j.val = true := by
  decide +kernel

/-- Configuration 2 provides D-repair, using its existing certified rank planes. -/
theorem base_repair : Repairs ((cfmap cf002).map.RingTrace (cfring cf002).reverse) 7 := by
  intro et hlen hzero hsum
  have htlen : et.tail.length = 6 := by simp [List.length_tail, hlen]
  have htzero : (0 : Color) ∉ et.tail := fun h => hzero (List.mem_of_mem_tail h)
  let j := Bulk.indexOf 6 et.tail
  have hj := Bulk.indexOf_lt 6 et.tail
  have hpartial : Bulk.partialOf 6 j = et.tail := Bulk.partialOf_indexOf htlen htzero
  have hrot : et.rotate 1 = Bulk.traceOf 6 j := by
    rw [Bulk.traceOf, hpartial]
    cases et with
    | nil => simp at hlen
    | cons e t =>
      rw [List.sum_cons] at hsum
      rw [List.rotate_cons_succ, List.rotate_zero, List.tail_cons, completeTrace,
        Color.add_eq_zero_iff.mp hsum]
  have hproper : (Bulk.partialOf 6 j).sum ≠ 0 := by
    intro hz
    have hzmem : (0 : Color) ∈ et.rotate 1 := by
      rw [hrot, Bulk.traceOf, completeTrace, hz]
      simp
    exact hzero (List.mem_rotate.mp hzmem)
  have hknown := Bulk.known_coclosure Bulk.Cfg001.cf 6 Bulk.Cfg001.hcf
    Bulk.Cfg001.R Bulk.Cfg001.H Bulk.Cfg001.C
    (by rw [Bulk.Cfg001.hH, Bulk.length_minPerm]) (by decide)
    Bulk.Cfg001.hH Bulk.Cfg001.hgood Bulk.Cfg001.hchoice Bulk.Cfg001.hpairs
    j hj (base_coverage ⟨j, hj⟩ hproper)
  rw [← hrot] at hknown
  have hcf : Bulk.Cfg001.cf = cf002 := by rfl
  rw [hcf] at hknown
  have h := ring_rotate_back hknown
  simpa only [cfring, List.reverse_reverse] using h

/-- Delete the inserted boundary vertex, restoring the edge whose ends differ. -/
def restrict12 (k : graph002.Coloring Color) (distinct : k 0 ≠ k 2) : graph001.Coloring Color :=
  Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.restrict graph001 0 1 6
    (SimpleGraph.coloringCongr DiamondInsertion.insert12.symm (Equiv.refl _) k) distinct

/-- Collapse the two ordered edge colours, retaining an actual colouring witness. -/
theorem reconstruct (a b : Color) (t : List Color) (_ha : a ≠ 0) (_hb : b ≠ 0)
    (hab : a ≠ b) (h : GraphTrace graph002 [0, 1, 2, 3, 4, 5, 6] (a :: b :: t)) :
    GraphTrace graph001 [0, 1, 2, 3, 4, 5] ((a + b) :: t) := by
  obtain ⟨k, hk⟩ := h
  have ha := congrArg (fun et => et.getD 0 0) hk
  have hb := congrArg (fun et => et.getD 1 0) hk
  have ht := congrArg (List.drop 2) hk
  change a = k 0 + k 1 at ha
  change b = k 1 + k 2 at hb
  have distinct : k 0 ≠ k 2 := by
    intro heq
    apply hab
    rw [ha, hb, heq, add_comm]
  refine ⟨restrict12 k distinct, ?_⟩
  rw [ha, hb]
  change t = (trace ([0, 1, 2, 3, 4, 5, 6].map k)).drop 2 at ht
  rw [ht]
  change (k 0 + k 1 + (k 1 + k 2)) ::
    (trace [k 0, k 1, k 2, k 3, k 4, k 5, k 6]).drop 2 =
    trace [k 0, k 2, k 3, k 4, k 5, k 6]
  simp only [trace_cons, List.cons_append, List.nil_append, pairmap_cons, pairmap_nil]
  congr 1
  rw [add_assoc, ← add_assoc (k 1), add_self, zero_add]

/-- Configuration 1 inherits all its repair from configuration 2 through one split law. -/
theorem transferred_repair : Repairs ((cfmap cf001).map.RingTrace (cfring cf001).reverse) 6 := by
  have hbase : Repairs (GraphTrace graph002 [0, 1, 2, 3, 4, 5, 6]) 7 := by
    intro et hlen hzero hsum outside hclosed hold
    obtain ⟨et', ht', ho⟩ := base_repair et hlen hzero hsum outside hclosed hold
    exact ⟨et', (reducibilityTrace002 _).mp ht', ho⟩
  have htransfer := repairs_collapse reconstruct (by decide : 0 < 6) hbase
  intro et hlen hzero hsum outside hclosed hold
  have hr : KempeCoclosure (GraphTrace graph001 boundary001.reverse) et := by
    apply graph_rotate_back 2
    change KempeCoclosure (GraphTrace graph001 [0, 1, 2, 3, 4, 5]) (et.rotate 2)
    apply htransfer
    · simpa using hlen
    · exact fun h => hzero (List.mem_rotate.mp h)
    · rwa [(List.rotate_perm et 2).sum_eq]
  obtain ⟨et', ht', ho⟩ := hr outside hclosed hold
  exact ⟨et', (reducibilityTrace001 _).mpr ht', ho⟩

set_option maxRecDepth 32768 in
/-- Every boundary edge survives the specified contraction. -/
theorem boundary_edges : ∀ i : Fin 6, ∃ d : Fin 42,
    vertex001 (table001.map.edge d) = i.castLE (by decide) ∧
    vertex001 d = (i + 1).castLE (by decide) ∧
      d ∉ table001.map.insertE DiamondContract.darts001 := by
  decide +kernel

theorem contract_proper (et : List Color)
    (h : (cfmap cf001).map.CcRingTrace (cfcontract cf001) (cfring cf001).reverse et) :
    et.length = 6 ∧ (0 : Color) ∉ et ∧ et.sum = 0 := by
  obtain ⟨k, rfl⟩ := (DiamondContract.contractTrace001 et).mp h
  have adjacent (i : Fin 6) :
      k.val (i.castLE (by decide)) ≠ k.val ((i + 1).castLE (by decide)) := by
    obtain ⟨d, hd, hd', hnot⟩ := boundary_edges i
    rw [← hd, ← hd']
    exact fun heq => hnot ((k.property d).mp heq)
  refine ⟨by simp [boundary001], ?_, sum_trace _⟩
  have h0 := adjacent 0
  have h1 := adjacent 1
  have h2 := adjacent 2
  have h3 := adjacent 3
  have h4 := adjacent 4
  have h5 := adjacent 5
  change k.val 0 ≠ k.val 1 at h0
  change k.val 1 ≠ k.val 2 at h1
  change k.val 2 ≠ k.val 3 at h2
  change k.val 3 ≠ k.val 4 at h3
  change k.val 4 ≠ k.val 5 at h4
  change k.val 5 ≠ k.val 0 at h5
  change (0 : Color) ∉ trace [k.val 4, k.val 5, k.val 0, k.val 1, k.val 2, k.val 3]
  simpa only [trace_cons, List.cons_append, List.nil_append, pairmap_cons, pairmap_nil,
    List.mem_cons, List.not_mem_nil, or_false, not_or, eq_comm (a := (0 : Color)),
    Color.add_eq_zero_iff] using And.intro h4 (And.intro h5
      (And.intro h0 (And.intro h1 (And.intro h2 h3))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Decode the geometric contract once; no reducibility certificate is checked here.
theorem valid_contract : (cfmap cf001).map.ValidContract (cfring cf001) (cfcontract cf001) := by
  have hs : (contractCtree cf001).isSome = true := by decide +kernel
  cases hc : contractCtree cf001 with
  | none => simp [hc] at hs
  | some ct => exact (contract_ctreeP hc).1

/-- The actual reference contract is reducible by the transferred family repair. -/
theorem reducible : CfReducible cf001 := by
  refine ⟨valid_contract, fun et ht => ?_⟩
  obtain ⟨hlen, hzero, hsum⟩ := contract_proper et ht
  exact transferred_repair et hlen hzero hsum

end FourColor.DiamondSplitRepair
