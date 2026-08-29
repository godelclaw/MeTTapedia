import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask012

def activeValue : BitVec 14 := BitVec.ofNat 14 66

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17944526, component := 38 },
    { zero := BitVec.ofNat 26 22122446, component := 38 },
    { zero := BitVec.ofNat 26 18206158, component := 38 },
    { zero := BitVec.ofNat 26 22384078, component := 38 },
    { zero := BitVec.ofNat 26 20041422, component := 38 },
    { zero := BitVec.ofNat 26 24219342, component := 38 },
    { zero := BitVec.ofNat 26 20303054, component := 38 },
    { zero := BitVec.ofNat 26 24480974, component := 38 },
    { zero := BitVec.ofNat 26 51498950, component := 38 },
    { zero := BitVec.ofNat 26 55676870, component := 38 },
    { zero := BitVec.ofNat 26 51760582, component := 38 },
    { zero := BitVec.ofNat 26 55938502, component := 38 },
    { zero := BitVec.ofNat 26 53595846, component := 38 },
    { zero := BitVec.ofNat 26 57773766, component := 38 },
    { zero := BitVec.ofNat 26 53857478, component := 38 },
    { zero := BitVec.ofNat 26 58035398, component := 38 }
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

end Krenn.CollapseSupportCover.Mask012
