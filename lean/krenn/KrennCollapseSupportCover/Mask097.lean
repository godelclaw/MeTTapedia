import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask097

def activeValue : BitVec 14 := BitVec.ofNat 14 2056

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18076649, component := 50 },
    { zero := BitVec.ofNat 26 18338153, component := 49 },
    { zero := BitVec.ofNat 26 52122537, component := 50 },
    { zero := BitVec.ofNat 26 18596777, component := 39 },
    { zero := BitVec.ofNat 26 52384041, component := 45 },
    { zero := BitVec.ofNat 26 18858281, component := 26 },
    { zero := BitVec.ofNat 26 51598305, component := 45 },
    { zero := BitVec.ofNat 26 52151265, component := 25 },
    { zero := BitVec.ofNat 26 51859809, component := 46 },
    { zero := BitVec.ofNat 26 52412769, component := 23 },
    { zero := BitVec.ofNat 26 18084840, component := 63 },
    { zero := BitVec.ofNat 26 18346472, component := 62 },
    { zero := BitVec.ofNat 26 52130728, component := 63 },
    { zero := BitVec.ofNat 26 18604968, component := 39 },
    { zero := BitVec.ofNat 26 52392360, component := 25 },
    { zero := BitVec.ofNat 26 18866600, component := 26 },
    { zero := BitVec.ofNat 26 51606496, component := 56 },
    { zero := BitVec.ofNat 26 52159456, component := 25 },
    { zero := BitVec.ofNat 26 51868128, component := 57 },
    { zero := BitVec.ofNat 26 52421088, component := 25 }
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

end Krenn.CollapseSupportCover.Mask097
