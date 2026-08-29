import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask105

def activeValue : BitVec 14 := BitVec.ofNat 14 2560

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17027583, component := 51 },
    { zero := BitVec.ofNat 26 51073471, component := 51 },
    { zero := BitVec.ofNat 26 17547711, component := 40 },
    { zero := BitVec.ofNat 26 50549239, component := 24 },
    { zero := BitVec.ofNat 26 51102199, component := 24 },
    { zero := BitVec.ofNat 26 21221883, component := 51 },
    { zero := BitVec.ofNat 26 55267771, component := 51 },
    { zero := BitVec.ofNat 26 21742011, component := 40 },
    { zero := BitVec.ofNat 26 54743539, component := 45 },
    { zero := BitVec.ofNat 26 55296499, component := 25 },
    { zero := BitVec.ofNat 26 25416189, component := 51 },
    { zero := BitVec.ofNat 26 59462077, component := 51 },
    { zero := BitVec.ofNat 26 25936317, component := 10 },
    { zero := BitVec.ofNat 26 58937845, component := 3 },
    { zero := BitVec.ofNat 26 59490805, component := 3 },
    { zero := BitVec.ofNat 26 29610489, component := 51 },
    { zero := BitVec.ofNat 26 63656377, component := 51 },
    { zero := BitVec.ofNat 26 30130617, component := 40 },
    { zero := BitVec.ofNat 26 63132145, component := 45 },
    { zero := BitVec.ofNat 26 63685105, component := 25 },
    { zero := BitVec.ofNat 26 17035742, component := 64 },
    { zero := BitVec.ofNat 26 51081630, component := 64 },
    { zero := BitVec.ofNat 26 17555870, component := 26 },
    { zero := BitVec.ofNat 26 50557398, component := 58 },
    { zero := BitVec.ofNat 26 51110358, component := 24 },
    { zero := BitVec.ofNat 26 21230074, component := 64 },
    { zero := BitVec.ofNat 26 55275962, component := 64 },
    { zero := BitVec.ofNat 26 21750202, component := 40 },
    { zero := BitVec.ofNat 26 54751730, component := 56 },
    { zero := BitVec.ofNat 26 55304690, component := 25 },
    { zero := BitVec.ofNat 26 25424348, component := 64 },
    { zero := BitVec.ofNat 26 59470236, component := 64 },
    { zero := BitVec.ofNat 26 25944476, component := 13 },
    { zero := BitVec.ofNat 26 58946004, component := 56 },
    { zero := BitVec.ofNat 26 59498964, component := 6 },
    { zero := BitVec.ofNat 26 29618680, component := 64 },
    { zero := BitVec.ofNat 26 63664568, component := 64 },
    { zero := BitVec.ofNat 26 30138808, component := 40 },
    { zero := BitVec.ofNat 26 63140336, component := 56 },
    { zero := BitVec.ofNat 26 63693296, component := 25 }
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

end Krenn.CollapseSupportCover.Mask105
