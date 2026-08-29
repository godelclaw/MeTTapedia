import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask070

def activeValue : BitVec 14 := BitVec.ofNat 14 1028

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 62474917, component := 18 },
    { zero := BitVec.ofNat 26 62736421, component := 3 },
    { zero := BitVec.ofNat 26 62744581, component := 3 },
    { zero := BitVec.ofNat 26 66922501, component := 26 },
    { zero := BitVec.ofNat 26 66652833, component := 42 },
    { zero := BitVec.ofNat 26 66914337, component := 26 },
    { zero := BitVec.ofNat 26 62483076, component := 20 },
    { zero := BitVec.ofNat 26 66660996, component := 20 },
    { zero := BitVec.ofNat 26 62744708, component := 6 },
    { zero := BitVec.ofNat 26 66922628, component := 26 },
    { zero := BitVec.ofNat 26 66661024, component := 42 },
    { zero := BitVec.ofNat 26 66922656, component := 26 }
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

end Krenn.CollapseSupportCover.Mask070
