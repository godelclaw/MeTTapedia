import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask037

def activeValue : BitVec 14 := BitVec.ofNat 14 548

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 59333797, component := 3 },
    { zero := BitVec.ofNat 26 59362469, component := 3 },
    { zero := BitVec.ofNat 26 63511713, component := 26 },
    { zero := BitVec.ofNat 26 63540385, component := 33 },
    { zero := BitVec.ofNat 26 59341956, component := 6 },
    { zero := BitVec.ofNat 26 63519876, component := 26 },
    { zero := BitVec.ofNat 26 59370628, component := 6 },
    { zero := BitVec.ofNat 26 63548548, component := 19 },
    { zero := BitVec.ofNat 26 63519904, component := 26 },
    { zero := BitVec.ofNat 26 63548576, component := 33 }
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

end Krenn.CollapseSupportCover.Mask037
