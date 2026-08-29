import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask315

def activeValue : BitVec 14 := BitVec.ofNat 14 12296

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1187833, component := 51 },
    { zero := BitVec.ofNat 26 3283961, component := 51 },
    { zero := BitVec.ofNat 26 1449849, component := 51 },
    { zero := BitVec.ofNat 26 3545977, component := 51 },
    { zero := BitVec.ofNat 26 1712057, component := 51 },
    { zero := BitVec.ofNat 26 3808185, component := 51 },
    { zero := BitVec.ofNat 26 1974073, component := 51 },
    { zero := BitVec.ofNat 26 4070201, component := 51 },
    { zero := BitVec.ofNat 26 1196024, component := 64 },
    { zero := BitVec.ofNat 26 3292152, component := 64 },
    { zero := BitVec.ofNat 26 1720248, component := 64 },
    { zero := BitVec.ofNat 26 3816376, component := 64 }
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

end Krenn.CollapseSupportCover.Mask315
