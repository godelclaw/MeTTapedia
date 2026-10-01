import MettapediaFourColor.TwoDiamondConfigurations
import MettapediaFourColor.KempeBoundarySplit
import Mettapedia.GraphTheory.FourColor.BoundaryTriangleAlternatives
import FourColor.Bulk.Cfg.Grp09_00

/-!
# Shared-tip diamond repair descends from configuration 6 to configuration 3

The actual embedded graphs differ by a boundary-triangle insertion. All
colouring branches are kept in the construction equivalence. For repair in
the reverse direction, the chromogram split law forces the retained endpoints
to differ and therefore supplies a genuine smaller colouring.

Configuration 6's existing certified rank planes supply the base repair.
Configuration 3's separate rank certificate is not used. This replaces one
proof dependency; it does not change the unavoidable catalogue.

The base certificate and checker are reused from Chris Emery's MIT-licensed
realization of the Gonthier--Werner and RSST proof.
-/

namespace FourColor.TwoDiamondSplitRepair

open Color TwoDiamondConfigurations KempeBoundarySplit ConfigurationFaceGraph
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

local instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (subdivide G a b c).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [subdivide, removed] <;> infer_instance

/-- The old shared tip and both diamonds are retained by this exact map. -/
def insert36 : subdivide graph003 7 0 13 ≃g graph006 where
  toEquiv := ((finSuccEquiv' (8 : Fin 16)).symm).trans
    ((Equiv.swap 10 14).trans ((Equiv.swap 11 13).trans (Equiv.swap 12 15)))
  map_rel_iff' := by decide +kernel

theorem rotation36 : ∀ v : Option (Fin 15), ∃ shift : Fin 9,
    stars006 (insert36 v) =
      ((triangleStar stars003 7 0 13 v).map insert36).rotate shift.val := by
  decide +kernel

theorem boundary36 :
    (triangleBoundary boundary003 7).map insert36 = boundary006 := by decide +kernel

/-- Both the unequal and equal old-endpoint branches reconstruct actual colourings. -/
def alternatives36 :
    (graph003.Coloring (Fin 4) ⊕ EqualChoice graph003 7 0 13 (by decide)) ≃
      graph006.Coloring (Fin 4) :=
  (alternativesEquiv graph003 7 0 13 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      (SimpleGraph.coloringCongr insert36 (Equiv.refl _))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- Reuse the existing rank planes for every proper nine-port input. -/
theorem base_coverage : ∀ j : Fin (3 ^ 8),
    (Bulk.partialOf 8 j.val).sum ≠ 0 →
      (Bulk.knownMask 8 Bulk.Cfg005.R).testBit j.val = true := by
  decide +kernel

theorem base_repair : Repairs ((cfmap cf006).map.RingTrace (cfring cf006).reverse) 9 := by
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
  have hknown := Bulk.known_coclosure Bulk.Cfg005.cf 8 Bulk.Cfg005.hcf
    Bulk.Cfg005.R Bulk.Cfg005.H Bulk.Cfg005.C
    (by rw [Bulk.Cfg005.hH, Bulk.length_minPerm]) (by decide)
    Bulk.Cfg005.hH Bulk.Cfg005.hgood Bulk.Cfg005.hchoice Bulk.Cfg005.hpairs
    j hj (base_coverage ⟨j, hj⟩ hproper)
  rw [← hrot] at hknown
  have hcf : Bulk.Cfg005.cf = cf006 := by rfl
  rw [hcf] at hknown
  have h := ring_rotate_back hknown
  simpa only [cfring, List.reverse_reverse] using h

def restrict36 (k : graph006.Coloring Color) (distinct : k 7 ≠ k 0) :
    graph003.Coloring Color :=
  Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision.restrict graph003 7 0 13
    (SimpleGraph.coloringCongr insert36.symm (Equiv.refl _) k) distinct

/-- The retained ordered colours collapse to the boundary of a genuine witness. -/
theorem reconstruct (a b : Color) (t : List Color) (_ha : a ≠ 0) (_hb : b ≠ 0)
    (hab : a ≠ b)
    (h : GraphTrace graph006 [7, 8, 0, 1, 2, 3, 4, 5, 6] (a :: b :: t)) :
    GraphTrace graph003 [7, 0, 1, 2, 3, 4, 5, 6] ((a + b) :: t) := by
  obtain ⟨k, hk⟩ := h
  have ha := congrArg (fun et => et.getD 0 0) hk
  have hb := congrArg (fun et => et.getD 1 0) hk
  have ht := congrArg (List.drop 2) hk
  change a = k 7 + k 8 at ha
  change b = k 8 + k 0 at hb
  have distinct : k 7 ≠ k 0 := by
    intro heq
    apply hab
    rw [ha, hb, heq, add_comm]
  refine ⟨restrict36 k distinct, ?_⟩
  rw [ha, hb]
  change t = (trace ([7, 8, 0, 1, 2, 3, 4, 5, 6].map k)).drop 2 at ht
  rw [ht]
  change (k 7 + k 8 + (k 8 + k 0)) ::
    (trace [k 7, k 8, k 0, k 1, k 2, k 3, k 4, k 5, k 6]).drop 2 =
    trace [k 7, k 0, k 1, k 2, k 3, k 4, k 5, k 6]
  simp only [trace_cons, List.cons_append, List.nil_append, pairmap_cons, pairmap_nil]
  congr 1
  rw [add_assoc, ← add_assoc (k 8), add_self, zero_add]

theorem transferred_repair : Repairs ((cfmap cf003).map.RingTrace (cfring cf003).reverse) 8 := by
  have hbase : Repairs (GraphTrace graph006 [7, 8, 0, 1, 2, 3, 4, 5, 6]) 9 := by
    intro et hlen hzero hsum
    apply graph_rotate_back 2
    change KempeCoclosure (GraphTrace graph006 boundary006) (et.rotate 2)
    intro Q hQ hq
    obtain ⟨es, hs, ho⟩ := base_repair (et.rotate 2) (by simpa using hlen)
      (fun h => hzero (List.mem_rotate.mp h))
      (by rwa [(List.rotate_perm et 2).sum_eq]) Q hQ hq
    exact ⟨es, (reducibilityTrace006 es).mp hs, ho⟩
  have htransfer := repairs_collapse reconstruct (by decide : 0 < 8) hbase
  intro et hlen hzero hsum Q hQ hq
  have hc : KempeCoclosure (GraphTrace graph003 boundary003) et := by
    apply graph_rotate_back 7
    change KempeCoclosure (GraphTrace graph003 [7, 0, 1, 2, 3, 4, 5, 6]) (et.rotate 7)
    apply htransfer
    · simpa using hlen
    · exact fun h => hzero (List.mem_rotate.mp h)
    · rwa [(List.rotate_perm et 7).sum_eq]
  obtain ⟨es, hs, ho⟩ := hc Q hQ hq
  exact ⟨es, (reducibilityTrace003 es).mpr hs, ho⟩

set_option maxRecDepth 32768 in
theorem boundary_edges : ∀ i : Fin 8, ∃ d : Fin 68,
    vertex003 (table003.map.edge d) = i.castLE (by decide) ∧
    vertex003 d = (i + 1).castLE (by decide) ∧
      d ∉ table003.map.insertE darts003 := by
  decide +kernel

theorem contract_proper (et : List Color)
    (h : (cfmap cf003).map.CcRingTrace (cfcontract cf003) (cfring cf003).reverse et) :
    et.length = 8 ∧ (0 : Color) ∉ et ∧ et.sum = 0 := by
  obtain ⟨k, rfl⟩ := (contractTrace003 et).mp h
  have adjacent (i : Fin 8) :
      k.val (i.castLE (by decide)) ≠ k.val ((i + 1).castLE (by decide)) := by
    obtain ⟨d, hd, hd', hnot⟩ := boundary_edges i
    rw [← hd, ← hd']
    exact fun heq => hnot ((k.property d).mp heq)
  refine ⟨by simp [boundary003], ?_, sum_trace _⟩
  have h0 := adjacent 0
  have h1 := adjacent 1
  have h2 := adjacent 2
  have h3 := adjacent 3
  have h4 := adjacent 4
  have h5 := adjacent 5
  have h6 := adjacent 6
  have h7 := adjacent 7
  change k.val 0 ≠ k.val 1 at h0
  change k.val 1 ≠ k.val 2 at h1
  change k.val 2 ≠ k.val 3 at h2
  change k.val 3 ≠ k.val 4 at h3
  change k.val 4 ≠ k.val 5 at h4
  change k.val 5 ≠ k.val 6 at h5
  change k.val 6 ≠ k.val 7 at h6
  change k.val 7 ≠ k.val 0 at h7
  change (0 : Color) ∉ trace [k.val 0, k.val 1, k.val 2, k.val 3,
    k.val 4, k.val 5, k.val 6, k.val 7]
  simpa only [trace_cons, List.cons_append, List.nil_append, pairmap_cons, pairmap_nil,
    List.mem_cons, List.not_mem_nil, or_false, not_or, eq_comm (a := (0 : Color)),
    Color.add_eq_zero_iff] using
      And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
        (And.intro h4 (And.intro h5 (And.intro h6 h7))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- Decode the actual geometric contract, without checking a repair certificate. -/
theorem valid_contract : (cfmap cf003).map.ValidContract (cfring cf003) (cfcontract cf003) := by
  have hs : (contractCtree cf003).isSome = true := by decide +kernel
  cases hc : contractCtree cf003 with
  | none => simp [hc] at hs
  | some ct => exact (contract_ctreeP hc).1

theorem reducible003 : CfReducible cf003 := by
  refine ⟨valid_contract, fun et ht => ?_⟩
  obtain ⟨hlen, hzero, hsum⟩ := contract_proper et ht
  exact transferred_repair et hlen hzero hsum

end FourColor.TwoDiamondSplitRepair
