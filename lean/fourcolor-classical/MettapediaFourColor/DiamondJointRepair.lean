import MettapediaFourColor.DiamondBoundaryRepair
import MettapediaFourColor.DiamondJointContract
import MettapediaFourColor.DiamondBoundarySummary

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
open Mettapedia.GraphTheory.FourColor

/-- Full vertex colourings, in the order of the twenty-three terminal traces. -/
def coloringCodes : String :=
  "020301011232 010132323201 010232322101 020132323201 020232323101 \
  030232322101 010132313202 010232313102 012032313102 023132311202 \
  020132311202 020232313102 030132311202 010301022131 013201022131 \
  020301023121 030101021323 030301022131 023210131032 020310131232 \
  030310131232 013210232031 013023122103"

def assignment (i : Fin 23) (v : Fin 12) : Color :=
  colorAt coloringCodes (13 * i.val + v.val)

def boundaryAssignment (i : Fin 23) (v : Fin 8) : Color :=
  assignment i (DiamondBoundarySummary.graph004Iso (.inl v))

def interiorAssignment (i : Fin 23) (j : Fin 4) : Color :=
  assignment i (DiamondBoundarySummary.graph004Iso (.inr j))

set_option maxRecDepth 32768 in
theorem boundary_valid : ∀ (i : Fin 23) (v w : Fin 8),
    (SimpleGraph.cycleGraph 8).Adj v w → boundaryAssignment i v ≠ boundaryAssignment i w := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Check the common four-vertex core and its attachments to the boundary. -/
theorem interior_valid : ∀ i : Fin 23,
    (∀ j, DiamondBoundaryElimination.Allows (DiamondBoundarySummary.attachments 1 1)
      (boundaryAssignment i) j (interiorAssignment i j)) ∧
    (∀ j k, DiamondBoundaryElimination.coreAdj j k →
      interiorAssignment i j ≠ interiorAssignment i k) := by
  unfold DiamondBoundaryElimination.Allows
  decide +kernel

def boundaryColoring (i : Fin 23) : (SimpleGraph.cycleGraph 8).Coloring Color :=
  .mk (boundaryAssignment i) (boundary_valid i _ _)

set_option maxRecDepth 32768 in
def interiorSummary (i : Fin 23) :
    DiamondBoundaryElimination.Summary (DiamondBoundarySummary.attachments 1 1)
      (boundaryColoring i) where
  first := interiorAssignment i 0
  second := interiorAssignment i 2
  centres_ne := (interior_valid i).2 0 2 (by decide)
  first_allowed := (interior_valid i).1 0
  second_allowed := (interior_valid i).1 2
  lower := ⟨interiorAssignment i 1, (interior_valid i).1 1,
    (interior_valid i).2 1 0 (by decide), (interior_valid i).2 1 2 (by decide)⟩
  upper := ⟨interiorAssignment i 3, (interior_valid i).1 3,
    (interior_valid i).2 3 0 (by decide), (interior_valid i).2 3 2 (by decide)⟩

def plan (i : Fin 23) : DiamondBoundarySummary.Plan 1 1 Color :=
  ⟨boundaryColoring i, interiorSummary i⟩

/-- Actual witnesses are reconstructed by the same law used for all three diamonds. -/
def coloring (i : Fin 23) : graph004.Coloring Color :=
  (DiamondBoundarySummary.planEquiv DiamondBoundarySummary.graph004Iso).symm (plan i)

set_option maxRecDepth 32768 in
theorem coloring_assignment : ∀ (i : Fin 23) (v : Fin 12),
    coloring i v = assignment i v := by
  decide +kernel

/-- Reconstruction also verifies every edge of the literal reference map. -/
theorem assignment_valid (i : Fin 23) (d : Fin 50) :
    assignment i (vertex004 (table004.map.edge d)) ≠ assignment i (vertex004 d) := by
  rw [← coloring_assignment, ← coloring_assignment]
  exact ((coloring i).valid ((faces004.adjacent _ _).mpr ⟨d, rfl, rfl⟩)).symm

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
  apply (DiamondBoundarySummary.reference004 _).mpr
  refine ⟨plan ⟨i, hi⟩, ?_⟩
  have ht := coloring_trace ⟨i, hi⟩
  rw [← DiamondBoundarySummary.ring004, List.map_map] at ht
  exact ht.symm

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
