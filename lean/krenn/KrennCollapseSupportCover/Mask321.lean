import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask321

def activeValue : BitVec 14 := BitVec.ofNat 14 12312

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1187809, component := 26 },
    { zero := BitVec.ofNat 26 3283937, component := 52 },
    { zero := BitVec.ofNat 26 1449825, component := 49 },
    { zero := BitVec.ofNat 26 3545953, component := 49 },
    { zero := BitVec.ofNat 26 1196000, component := 26 },
    { zero := BitVec.ofNat 26 3292128, component := 65 }
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

end Krenn.CollapseSupportCover.Mask321
