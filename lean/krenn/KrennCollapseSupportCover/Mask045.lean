import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask045

def activeValue : BitVec 14 := BitVec.ofNat 14 641

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 21216538, component := 64 },
    { zero := BitVec.ofNat 26 54738202, component := 64 },
    { zero := BitVec.ofNat 26 31570970, component := 36 },
    { zero := BitVec.ofNat 26 65092634, component := 26 },
    { zero := BitVec.ofNat 26 23312410, component := 59 },
    { zero := BitVec.ofNat 26 56834074, component := 59 },
    { zero := BitVec.ofNat 26 29474072, component := 35 },
    { zero := BitVec.ofNat 26 62995736, component := 26 },
    { zero := BitVec.ofNat 26 31701272, component := 64 },
    { zero := BitVec.ofNat 26 65222936, component := 64 }
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

end Krenn.CollapseSupportCover.Mask045
