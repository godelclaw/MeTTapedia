import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask249

def activeValue : BitVec 14 := BitVec.ofNat 14 8194

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17850350, component := 26 },
    { zero := BitVec.ofNat 26 19947246, component := 41 },
    { zero := BitVec.ofNat 26 18374574, component := 39 },
    { zero := BitVec.ofNat 26 20471470, component := 42 },
    { zero := BitVec.ofNat 26 22028266, component := 26 },
    { zero := BitVec.ofNat 26 24125162, component := 29 },
    { zero := BitVec.ofNat 26 22552490, component := 31 },
    { zero := BitVec.ofNat 26 24649386, component := 30 }
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

end Krenn.CollapseSupportCover.Mask249
