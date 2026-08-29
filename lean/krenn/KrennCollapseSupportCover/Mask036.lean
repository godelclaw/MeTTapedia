import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask036

def activeValue : BitVec 14 := BitVec.ofNat 14 546

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 16899310, component := 38 },
    { zero := BitVec.ofNat 26 50945198, component := 25 },
    { zero := BitVec.ofNat 26 17419438, component := 33 },
    { zero := BitVec.ofNat 26 50420966, component := 24 },
    { zero := BitVec.ofNat 26 50973926, component := 38 },
    { zero := BitVec.ofNat 26 21077226, component := 36 },
    { zero := BitVec.ofNat 26 55123114, component := 31 },
    { zero := BitVec.ofNat 26 21597354, component := 32 },
    { zero := BitVec.ofNat 26 54598882, component := 26 },
    { zero := BitVec.ofNat 26 55151842, component := 33 }
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

end Krenn.CollapseSupportCover.Mask036
