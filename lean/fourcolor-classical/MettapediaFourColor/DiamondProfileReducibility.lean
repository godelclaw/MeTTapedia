import MettapediaFourColor.DiamondProfileFamilyRepair
import MettapediaFourColor.DiamondSplitRepair
import MettapediaFourColor.DiamondJointRepair

/-!
# Actual configuration reductions from joint-profile descent

The profile law reconstructs genuine colourings of the same four-vertex core
in configurations 1, 2 and 4. Ordered boundary transport and the proved
reference contract decoder connect it to the classical reduction theorem.
The former configuration-specific repair certificates are not used.
-/

namespace FourColor.DiamondProfileReducibility

open Color DiamondConfigurations DiamondProfile DiamondProfileFamilyRepair KempeBoundarySplit

theorem supports_graph {V : Type*} {G : SimpleGraph V} (s : Shape)
    (e : DiamondBoundarySummary.fan (left s) (right s) ≃g G) (et : List Color)
    (h : Supports s et) :
    GraphTrace G ((List.finRange (6 + left s + right s)).map (fun v => e (.inl v))) et := by
  obtain ⟨k, hk⟩ :=
    (DiamondBoundarySummary.trace_iff e (List.finRange (6 + left s + right s)) et).mpr h
  refine ⟨k, ?_⟩
  rw [List.map_map]
  exact hk

theorem repair001 : Repairs ((cfmap cf001).map.RingTrace (cfring cf001).reverse) 6 := by
  intro et hlen hzero hsum outside hclosed hold
  have hc : KempeCoclosure (GraphTrace graph001 boundary001.reverse) et := by
    apply graph_rotate_back 2
    change KempeCoclosure (GraphTrace graph001 [0, 1, 2, 3, 4, 5]) (et.rotate 2)
    intro Q hQ hq
    obtain ⟨es, hp, hqs⟩ := repair0 (et.rotate 2) (by simpa using hlen)
      (fun h => hzero (List.mem_rotate.mp h)) (by rwa [(List.rotate_perm et 2).sum_eq]) Q hQ hq
    exact ⟨es, supports_graph 0 DiamondBoundarySummary.graph001Iso es hp, hqs⟩
  obtain ⟨es, hg, ho⟩ := hc outside hclosed hold
  exact ⟨es, (reducibilityTrace001 es).mpr hg, ho⟩

theorem repair002 : Repairs ((cfmap cf002).map.RingTrace (cfring cf002).reverse) 7 := by
  intro et hlen hzero hsum Q hQ hq
  obtain ⟨es, hp, hqs⟩ := repair1 et hlen hzero hsum Q hQ hq
  exact ⟨es, (DiamondBoundarySummary.reference002 es).mpr hp, hqs⟩

/-- Retain the general split transfer, now supplied by the shared profile base. -/
theorem transferred001 : Repairs ((cfmap cf001).map.RingTrace (cfring cf001).reverse) 6 := by
  have hbase : Repairs (GraphTrace graph002 [0, 1, 2, 3, 4, 5, 6]) 7 := by
    intro et hlen hzero hsum Q hQ hq
    obtain ⟨es, hp, hqs⟩ := repair002 et hlen hzero hsum Q hQ hq
    exact ⟨es, (reducibilityTrace002 es).mp hp, hqs⟩
  have htransfer := repairs_collapse DiamondSplitRepair.reconstruct (by decide : 0 < 6) hbase
  intro et hlen hzero hsum Q hQ hq
  have hc : KempeCoclosure (GraphTrace graph001 boundary001.reverse) et := by
    apply graph_rotate_back 2
    change KempeCoclosure (GraphTrace graph001 [0, 1, 2, 3, 4, 5]) (et.rotate 2)
    apply htransfer
    · simpa using hlen
    · exact fun h => hzero (List.mem_rotate.mp h)
    · rwa [(List.rotate_perm et 2).sum_eq]
  obtain ⟨es, hg, hqs⟩ := hc Q hQ hq
  exact ⟨es, (reducibilityTrace001 es).mpr hg, hqs⟩

theorem repair004 (et : List Color)
    (h : (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et) :
    KempeCoclosure ((cfmap cf004).map.RingTrace (cfring cf004).reverse) et := by
  obtain ⟨a, b, x, y, z, w, ha, rfl⟩ := DiamondJointContract.contractTrace_iff et |>.mp h
  obtain ⟨hab, hxa, hzb, hya, hyb, hwa, hwb⟩ := ha
  have hc : KempeCoclosure (GraphTrace graph004 boundary004.reverse)
      (trace [a, x, a, y, b, z, b, w]) := by
    apply graph_rotate_back 4
    rw [← trace_rotate]
    change KempeCoclosure (GraphTrace graph004 [0, 1, 2, 3, 4, 5, 6, 7])
      (trace [b, z, b, w, a, x, a, y])
    intro Q hQ hq
    obtain ⟨es, hp, hqs⟩ := repair2 b a z w x y
      ⟨Ne.symm hab, hzb, hxa, hwb, hwa, hyb, hya⟩ Q hQ hq
    exact ⟨es, supports_graph 2 DiamondBoundarySummary.graph004Iso es hp, hqs⟩
  intro Q hQ hq
  obtain ⟨es, hg, hqs⟩ := hc Q hQ hq
  exact ⟨es, (reducibilityTrace004 es).mpr hg, hqs⟩

set_option maxRecDepth 32768 in
theorem boundary_edges002 : ∀ i : Fin 7, ∃ d : Fin 46,
    vertex002 (table002.map.edge d) = i.castLE (by decide) ∧
    vertex002 d = (i + 1).castLE (by decide) ∧
      d ∉ table002.map.insertE DiamondContract.darts002 := by
  decide +kernel

theorem contract_proper002 (et : List Color)
    (h : (cfmap cf002).map.CcRingTrace (cfcontract cf002) (cfring cf002).reverse et) :
    et.length = 7 ∧ (0 : Color) ∉ et ∧ et.sum = 0 := by
  obtain ⟨k, rfl⟩ := (DiamondContract.contractTrace002 et).mp h
  have adjacent (i : Fin 7) :
      k.val (i.castLE (by decide)) ≠ k.val ((i + 1).castLE (by decide)) := by
    obtain ⟨d, hd, hd', hnot⟩ := boundary_edges002 i
    rw [← hd, ← hd']
    exact fun heq => hnot ((k.property d).mp heq)
  refine ⟨by simp [boundary002], ?_, sum_trace _⟩
  have h0 := adjacent 0
  have h1 := adjacent 1
  have h2 := adjacent 2
  have h3 := adjacent 3
  have h4 := adjacent 4
  have h5 := adjacent 5
  have h6 := adjacent 6
  change k.val 0 ≠ k.val 1 at h0
  change k.val 1 ≠ k.val 2 at h1
  change k.val 2 ≠ k.val 3 at h2
  change k.val 3 ≠ k.val 4 at h3
  change k.val 4 ≠ k.val 5 at h4
  change k.val 5 ≠ k.val 6 at h5
  change k.val 6 ≠ k.val 0 at h6
  change (0 : Color) ∉ trace [k.val 0, k.val 1, k.val 2, k.val 3, k.val 4, k.val 5, k.val 6]
  simpa only [trace_cons, List.cons_append, List.nil_append, pairmap_cons, pairmap_nil,
    List.mem_cons, List.not_mem_nil, or_false, not_or, eq_comm (a := (0 : Color)),
    Color.add_eq_zero_iff] using And.intro h0 (And.intro h1 (And.intro h2
      (And.intro h3 (And.intro h4 (And.intro h5 h6)))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Decode the specified geometric contract; no reducibility certificate is used.
theorem valid_contract002 : (cfmap cf002).map.ValidContract (cfring cf002) (cfcontract cf002) := by
  have hs : (contractCtree cf002).isSome = true := by decide +kernel
  cases hc : contractCtree cf002 with
  | none => simp [hc] at hs
  | some ct => exact (contract_ctreeP hc).1

theorem reducible001 : CfReducible cf001 := by
  refine ⟨DiamondSplitRepair.valid_contract, fun et ht => ?_⟩
  obtain ⟨hlen, hzero, hsum⟩ := DiamondSplitRepair.contract_proper et ht
  exact transferred001 et hlen hzero hsum

theorem reducible002 : CfReducible cf002 := by
  refine ⟨valid_contract002, fun et ht => ?_⟩
  obtain ⟨hlen, hzero, hsum⟩ := contract_proper002 et ht
  exact repair002 et hlen hzero hsum

theorem reducible004 : CfReducible cf004 := ⟨DiamondJointRepair.valid_contract, repair004⟩

/-- The repaired colouring retains a compatible GSLT history through both insertions. -/
theorem compatible_history {Q : List Color → Prop} (closed : KempeClosed Q)
    (et : List Color)
    (contract : (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et)
    (outside : Q et) :
    ∃ et', ∃ k : DiamondInsertionGSLT.State .reference,
      ∃ x : DiamondInsertionGSLT.State .alternatives,
      Q et' ∧ et' = trace ((cfring cf004).reverse.map k.val) ∧
        DiamondInsertionGSLT.semantics.Supports DiamondInsertionGSLT.route x k := by
  obtain ⟨et', ⟨k, hk, htrace⟩, hQ⟩ := repair004 et contract Q closed outside
  obtain ⟨x, hx⟩ := DiamondInsertionGSLT.every_coloring ⟨k, hk⟩
  exact ⟨et', ⟨k, hk⟩, x, hQ, htrace, hx⟩

end FourColor.DiamondProfileReducibility
