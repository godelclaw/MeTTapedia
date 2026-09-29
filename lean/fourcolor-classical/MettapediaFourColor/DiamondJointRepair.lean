import MettapediaFourColor.DiamondBoundaryRepair
import MettapediaFourColor.DiamondJointContract
import MettapediaFourColor.DiamondInsertionGSLT

/-!
# Joint repair of the two diamond insertions

The abstract boundary law is instantiated with actual colourings of the
configuration graph. Exact contract elimination supplies its input relation.
Together they prove C-reducibility without the original configuration
certificate or a global Kempe fixed-point computation. The resulting matching
colouring also has a compatible history through both insertion alternatives.
-/

namespace FourColor.DiamondJointRepair

open DiamondConfigurations DiamondBoundaryRepair

/-- Full vertex colourings, in the order of the twenty-three terminal traces. -/
def coloringCodes : String :=
  "020301011232 010132323201 010232322101 020132323201 020232323101 \
  030232322101 010132313202 010232313102 012032313102 023132311202 \
  020132311202 020232313102 030132311202 010301022131 013201022131 \
  020301023121 030101021323 030301022131 023210131032 020310131232 \
  030310131232 013210232031 013023122103"

def assignment (i : Fin 23) (v : Fin 12) : Color :=
  colorAt coloringCodes (13 * i.val + v.val)

set_option maxRecDepth 32768 in
/-- Each witness separates the endpoints of every literal map edge. -/
theorem assignment_valid : ∀ (i : Fin 23) (d : Fin 50),
    assignment i (vertex004 (table004.map.edge d)) ≠ assignment i (vertex004 d) := by
  decide +kernel

def coloring (i : Fin 23) : graph004.Coloring Color :=
  .mk (assignment i) (by
    intro v w h
    obtain ⟨d, rfl, rfl⟩ := (faces004.adjacent v w).mp h
    exact (assignment_valid i d).symm)

set_option maxRecDepth 32768 in
theorem coloring_trace : ∀ i : Fin 23,
    trace (boundary004.reverse.map (assignment i)) = wordAt terminalCodes i.val := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Every terminal trace is realized by an actual reference-map colouring. -/
theorem terminal_realized (et : List Color) (h : et ∈ words terminalCodes) :
    (cfmap cf004).map.RingTrace (cfring cf004).reverse et := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  have hi := List.mem_range.mp hi
  change i < 23 at hi
  apply (reducibilityTrace004 _).mpr
  exact ⟨coloring ⟨i, hi⟩, (coloring_trace ⟨i, hi⟩).symm⟩

/-- All joint contract traces meet every compatible Kempe-closed exterior. -/
theorem contract_repair (et : List Color)
    (h : (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et) :
    KempeCoclosure ((cfmap cf004).map.RingTrace (cfring cf004).reverse) et := by
  obtain ⟨a, b, x, y, z, w, ha, rfl⟩ := DiamondJointContract.contractTrace_iff et |>.mp h
  exact DiamondBoundaryRepair.repair terminal_realized a b x y z w ha

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Unfold the reference construction and its four-edge contract once.
/-- The reference's proved contract decoder verifies the geometric side conditions. -/
theorem valid_contract : (cfmap cf004).map.ValidContract (cfring cf004) (cfcontract cf004) := by
  have hs : (contractCtree cf004).isSome = true := by decide +kernel
  cases hc : contractCtree cf004 with
  | none => simp [hc] at hs
  | some ct => exact (contract_ctreeP hc).1

/-- Reducibility now follows from the coupled boundary law and actual witnesses. -/
theorem reducible : CfReducible cf004 :=
  ⟨valid_contract, contract_repair⟩

/-- The selected matching colouring retains a compatible GSLT insertion history. -/
theorem compatible_history {Q : List Color → Prop} (closed : KempeClosed Q)
    (et : List Color)
    (contract : (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et)
    (outside : Q et) :
    ∃ et', ∃ k : DiamondInsertionGSLT.State .reference,
      ∃ x : DiamondInsertionGSLT.State .alternatives,
      Q et' ∧ et' = trace ((cfring cf004).reverse.map k.val) ∧
        DiamondInsertionGSLT.semantics.Supports DiamondInsertionGSLT.route x k := by
  obtain ⟨et', ⟨k, hk, htrace⟩, hQ⟩ := contract_repair et contract Q closed outside
  obtain ⟨x, hx⟩ := DiamondInsertionGSLT.every_coloring ⟨k, hk⟩
  exact ⟨et', ⟨k, hk⟩, x, hQ, htrace, hx⟩

end FourColor.DiamondJointRepair
