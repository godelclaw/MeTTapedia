import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask109

def activeValue : BitVec 14 := BitVec.ofNat 14 2604

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 51073185, component := 25 },
    { zero := BitVec.ofNat 26 51101857, component := 25 },
    { zero := BitVec.ofNat 26 51081376, component := 25 },
    { zero := BitVec.ofNat 26 51110048, component := 25 }
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

end Krenn.CollapseSupportCover.Mask109
