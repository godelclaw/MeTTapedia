import MettapediaFourColor.ExecutableContract
import MettapediaFourColor.ConfigurationContract
import MettapediaFourColor.DiamondInsertion

/-!
# The specified contracts of the three diamond configurations

The marked darts below are proved equal to the actual reference contracts.
Their face endpoints and complete contract-colouring boundary traces are
therefore available in the same graph coordinates as the insertion theorems.
-/

namespace FourColor.DiamondContract

open ExecutableConfiguration ConfigurationTable DiamondConfigurations

def darts001 : List (Fin 42) := [41]
def darts002 : List (Fin 46) := [45]
def darts004 : List (Fin 50) := [12, 25, 32, 39]

theorem enumeration001 :
    (ctrenum cf001.prog).map realization001.numbering = numberedKernelEdges program001 :=
  Realization.map_numbering_of_heq (n := 42) (t := table001) (p := 0)
    { numbering := (index program001).symm
      map_eq := numbered001
      point_eq := by decide +kernel }
    reference001 (kernelEdges_heq program001)

theorem enumeration002 :
    (ctrenum cf002.prog).map realization002.numbering = numberedKernelEdges program002 :=
  Realization.map_numbering_of_heq (n := 46) (t := table002) (p := 0)
    { numbering := (index program002).symm
      map_eq := numbered002
      point_eq := by decide +kernel }
    reference002 (kernelEdges_heq program002)

theorem enumeration004 :
    (ctrenum cf004.prog).map realization004.numbering = numberedKernelEdges program004 :=
  Realization.map_numbering_of_heq (n := 50) (t := table004) (p := 0)
    { numbering := (index program004).symm
      map_eq := numbered004
      point_eq := by decide +kernel }
    reference004 (kernelEdges_heq program004)

set_option maxRecDepth 32768 in
theorem contract001 : (cfcontract cf001).map realization001.numbering = darts001 := by
  unfold cfcontract
  erw [← listMask_map, enumeration001]
  decide +kernel

set_option maxRecDepth 32768 in
theorem contract002 : (cfcontract cf002).map realization002.numbering = darts002 := by
  unfold cfcontract
  erw [← listMask_map, enumeration002]
  decide +kernel

set_option maxRecDepth 32768 in
theorem contract004 : (cfcontract cf004).map realization004.numbering = darts004 := by
  unfold cfcontract
  erw [← listMask_map, enumeration004]
  decide +kernel

theorem endpoints001 :
    darts001.map (fun d => (vertex001 d, vertex001 (table001.map.edge d))) = [(6, 7)] := by
  decide +kernel

theorem endpoints002 :
    darts002.map (fun d => (vertex002 d, vertex002 (table002.map.edge d))) = [(10, 7)] := by
  decide +kernel

theorem endpoints004 :
    darts004.map (fun d => (vertex004 d, vertex004 (table004.map.edge d))) =
      [(4, 10), (10, 6), (0, 8), (8, 2)] := by
  decide +kernel

/-- The endpoints of the actual reference contract, in graph coordinates. -/
theorem referenceEndpoints001 :
    (cfcontract cf001).map (fun d =>
      (vertex001 (realization001.numbering d),
        vertex001 (table001.map.edge (realization001.numbering d)))) = [(6, 7)] := by
  have h := congrArg (List.map fun d =>
    (vertex001 d, vertex001 (table001.map.edge d))) contract001
  simpa only [List.map_map, Function.comp_def, endpoints001] using h

theorem referenceEndpoints002 :
    (cfcontract cf002).map (fun d =>
      (vertex002 (realization002.numbering d),
        vertex002 (table002.map.edge (realization002.numbering d)))) = [(10, 7)] := by
  have h := congrArg (List.map fun d =>
    (vertex002 d, vertex002 (table002.map.edge d))) contract002
  simpa only [List.map_map, Function.comp_def, endpoints002] using h

theorem referenceEndpoints004 :
    (cfcontract cf004).map (fun d =>
      (vertex004 (realization004.numbering d),
        vertex004 (table004.map.edge (realization004.numbering d)))) =
      [(4, 10), (10, 6), (0, 8), (8, 2)] := by
  have h := congrArg (List.map fun d =>
    (vertex004 d, vertex004 (table004.map.edge d))) contract004
  simpa only [List.map_map, Function.comp_def, endpoints004] using h

/-- The first insertion's old vertices, retained through both operations. -/
def originalVertex (v : Fin 10) : Fin 12 :=
  DiamondInsertion.insert24 (some (DiamondInsertion.insert12 (some v)))

/-- The specified contract selects the two old triangle sides at each insertion. -/
theorem referenceContract_insertions :
    (cfcontract cf004).map (fun d =>
      (vertex004 (realization004.numbering d),
        vertex004 (table004.map.edge (realization004.numbering d)))) =
      [(DiamondInsertion.insert24 (some 4), DiamondInsertion.insert24 (some 9)),
       (DiamondInsertion.insert24 (some 9), DiamondInsertion.insert24 (some 5)),
       (originalVertex 0, originalVertex 6), (originalVertex 6, originalVertex 1)] := by
  rw [referenceEndpoints004]
  decide +kernel

theorem contractTrace001 (et : List Color) :
    (cfmap cf001).map.CcRingTrace (cfcontract cf001) (cfring cf001).reverse et ↔
      ∃ k : faces001.ContractAssignment darts001,
        et = trace (boundary001.reverse.map k.val) := by
  rw [realization001.ccRingTrace, contract001, cfring, List.reverse_reverse,
    realization001.ring, cpring001, faces001.ccRingTrace_iff]
  rfl

theorem contractTrace002 (et : List Color) :
    (cfmap cf002).map.CcRingTrace (cfcontract cf002) (cfring cf002).reverse et ↔
      ∃ k : faces002.ContractAssignment darts002,
        et = trace (boundary002.reverse.map k.val) := by
  rw [realization002.ccRingTrace, contract002, cfring, List.reverse_reverse,
    realization002.ring, cpring002, faces002.ccRingTrace_iff]
  rfl

theorem contractTrace004 (et : List Color) :
    (cfmap cf004).map.CcRingTrace (cfcontract cf004) (cfring cf004).reverse et ↔
      ∃ k : faces004.ContractAssignment darts004,
        et = trace (boundary004.reverse.map k.val) := by
  rw [realization004.ccRingTrace, contract004, cfring, List.reverse_reverse,
    realization004.ring, cpring004, faces004.ccRingTrace_iff]
  rfl

end FourColor.DiamondContract
