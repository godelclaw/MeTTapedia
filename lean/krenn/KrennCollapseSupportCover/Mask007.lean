import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask007

def activeValue : BitVec 14 := BitVec.ofNat 14 10

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17948648, component := 26 },
    { zero := BitVec.ofNat 26 18210280, component := 37 },
    { zero := BitVec.ofNat 26 51994536, component := 39 },
    { zero := BitVec.ofNat 26 18468776, component := 39 },
    { zero := BitVec.ofNat 26 52256168, component := 25 },
    { zero := BitVec.ofNat 26 18730408, component := 33 },
    { zero := BitVec.ofNat 26 51470304, component := 26 },
    { zero := BitVec.ofNat 26 52023264, component := 25 },
    { zero := BitVec.ofNat 26 51731936, component := 23 },
    { zero := BitVec.ofNat 26 52284896, component := 37 }
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

end Krenn.CollapseSupportCover.Mask007
