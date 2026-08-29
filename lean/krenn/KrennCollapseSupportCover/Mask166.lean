import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask166

def activeValue : BitVec 14 := BitVec.ofNat 14 4120

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1286113, component := 26 },
    { zero := BitVec.ofNat 26 1806305, component := 33 },
    { zero := BitVec.ofNat 26 3382241, component := 52 },
    { zero := BitVec.ofNat 26 3902433, component := 42 },
    { zero := BitVec.ofNat 26 1547617, component := 49 },
    { zero := BitVec.ofNat 26 2067809, component := 37 },
    { zero := BitVec.ofNat 26 3643745, component := 49 },
    { zero := BitVec.ofNat 26 4163937, component := 26 },
    { zero := BitVec.ofNat 26 1294304, component := 26 },
    { zero := BitVec.ofNat 26 1814496, component := 33 },
    { zero := BitVec.ofNat 26 3390432, component := 65 },
    { zero := BitVec.ofNat 26 3910624, component := 42 },
    { zero := BitVec.ofNat 26 1555936, component := 62 },
    { zero := BitVec.ofNat 26 2076128, component := 37 },
    { zero := BitVec.ofNat 26 3652064, component := 62 },
    { zero := BitVec.ofNat 26 4172256, component := 26 }
]

def data : ActiveCover := {
  active := activeValue
  strata := strataData
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroCovered (pattern : Fin 26 → Prop)
    (feasible : Feasible pattern)
    (activePattern : ActiveMatches data.active pattern) :
    ∃ stratum ∈ data.strata, ZeroMatches stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [Feasible, relationLeftActive,
    relationRightActive] at feasible
  change ActiveMatches activeValue pattern at activePattern
  simp (config := { maxSteps := 1000000 }) only [activeValue, ActiveMatches,
    relationLeftActive] at activePattern
  change ∃ stratum ∈ strataData, ZeroMatches stratum.zero pattern
  simp (config := { maxSteps := 1000000 }) only [strataData, ZeroMatches,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

end Krenn.CollapseSupportCover.Mask166
