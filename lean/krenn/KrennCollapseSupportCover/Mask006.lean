import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask006

def activeValue : BitVec 14 := BitVec.ofNat 14 9

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18349384, component := 62 },
    { zero := BitVec.ofNat 26 20445512, component := 62 },
    { zero := BitVec.ofNat 26 52395272, component := 56 },
    { zero := BitVec.ofNat 26 18869512, component := 26 },
    { zero := BitVec.ofNat 26 54491400, component := 56 },
    { zero := BitVec.ofNat 26 20965640, component := 26 },
    { zero := BitVec.ofNat 26 51871040, component := 57 },
    { zero := BitVec.ofNat 26 52424000, component := 37 },
    { zero := BitVec.ofNat 26 53967168, component := 57 },
    { zero := BitVec.ofNat 26 54520128, component := 23 }
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

end Krenn.CollapseSupportCover.Mask006
