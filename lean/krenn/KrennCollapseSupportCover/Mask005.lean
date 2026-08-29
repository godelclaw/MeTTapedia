import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask005

def activeValue : BitVec 14 := BitVec.ofNat 14 8

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18079721, component := 50 },
    { zero := BitVec.ofNat 26 20175849, component := 50 },
    { zero := BitVec.ofNat 26 18341225, component := 49 },
    { zero := BitVec.ofNat 26 20437353, component := 49 },
    { zero := BitVec.ofNat 26 52125609, component := 50 },
    { zero := BitVec.ofNat 26 18599849, component := 39 },
    { zero := BitVec.ofNat 26 54221737, component := 50 },
    { zero := BitVec.ofNat 26 20695977, component := 39 },
    { zero := BitVec.ofNat 26 52387113, component := 45 },
    { zero := BitVec.ofNat 26 18861353, component := 26 },
    { zero := BitVec.ofNat 26 54483241, component := 45 },
    { zero := BitVec.ofNat 26 20957481, component := 26 },
    { zero := BitVec.ofNat 26 51601377, component := 45 },
    { zero := BitVec.ofNat 26 52154337, component := 25 },
    { zero := BitVec.ofNat 26 53697505, component := 52 },
    { zero := BitVec.ofNat 26 54250465, component := 42 },
    { zero := BitVec.ofNat 26 51862881, component := 46 },
    { zero := BitVec.ofNat 26 52415841, component := 37 },
    { zero := BitVec.ofNat 26 53959009, component := 46 },
    { zero := BitVec.ofNat 26 54511969, component := 23 },
    { zero := BitVec.ofNat 26 18087912, component := 63 },
    { zero := BitVec.ofNat 26 20184040, component := 63 },
    { zero := BitVec.ofNat 26 18349544, component := 62 },
    { zero := BitVec.ofNat 26 20445672, component := 62 },
    { zero := BitVec.ofNat 26 52133800, component := 63 },
    { zero := BitVec.ofNat 26 18608040, component := 39 },
    { zero := BitVec.ofNat 26 54229928, component := 63 },
    { zero := BitVec.ofNat 26 20704168, component := 39 },
    { zero := BitVec.ofNat 26 52395432, component := 25 },
    { zero := BitVec.ofNat 26 18869672, component := 33 },
    { zero := BitVec.ofNat 26 54491560, component := 25 },
    { zero := BitVec.ofNat 26 20965800, component := 26 },
    { zero := BitVec.ofNat 26 51609568, component := 56 },
    { zero := BitVec.ofNat 26 52162528, component := 25 },
    { zero := BitVec.ofNat 26 53705696, component := 65 },
    { zero := BitVec.ofNat 26 54258656, component := 42 },
    { zero := BitVec.ofNat 26 51871200, component := 57 },
    { zero := BitVec.ofNat 26 52424160, component := 37 },
    { zero := BitVec.ofNat 26 53967328, component := 57 },
    { zero := BitVec.ofNat 26 54520288, component := 25 }
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

end Krenn.CollapseSupportCover.Mask005
