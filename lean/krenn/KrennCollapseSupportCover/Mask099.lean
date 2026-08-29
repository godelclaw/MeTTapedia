import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask099

def activeValue : BitVec 14 := BitVec.ofNat 14 2112

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18072527, component := 26 },
    { zero := BitVec.ofNat 26 18334031, component := 26 },
    { zero := BitVec.ofNat 26 51626951, component := 24 },
    { zero := BitVec.ofNat 26 51888455, component := 23 },
    { zero := BitVec.ofNat 26 26461133, component := 9 },
    { zero := BitVec.ofNat 26 26722637, component := 17 },
    { zero := BitVec.ofNat 26 60015557, component := 3 },
    { zero := BitVec.ofNat 26 60277061, component := 4 }
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

end Krenn.CollapseSupportCover.Mask099
