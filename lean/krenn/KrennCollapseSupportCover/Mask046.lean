import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask046

def activeValue : BitVec 14 := BitVec.ofNat 14 644

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 60906549, component := 2 },
    { zero := BitVec.ofNat 26 61036597, component := 2 },
    { zero := BitVec.ofNat 26 60914709, component := 2 },
    { zero := BitVec.ofNat 26 65092629, component := 2 },
    { zero := BitVec.ofNat 26 61044757, component := 2 },
    { zero := BitVec.ofNat 26 65222677, component := 2 },
    { zero := BitVec.ofNat 26 65084465, component := 26 },
    { zero := BitVec.ofNat 26 65214513, component := 43 }
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

end Krenn.CollapseSupportCover.Mask046
