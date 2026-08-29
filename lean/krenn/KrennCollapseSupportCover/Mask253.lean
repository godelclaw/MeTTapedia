import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask253

def activeValue : BitVec 14 := BitVec.ofNat 14 8320

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17981231, component := 50 },
    { zero := BitVec.ofNat 26 28335663, component := 18 },
    { zero := BitVec.ofNat 26 20077103, component := 52 },
    { zero := BitVec.ofNat 26 17989391, component := 63 },
    { zero := BitVec.ofNat 26 22167311, component := 59 },
    { zero := BitVec.ofNat 26 28343823, component := 18 },
    { zero := BitVec.ofNat 26 32521743, component := 18 },
    { zero := BitVec.ofNat 26 20085263, component := 65 },
    { zero := BitVec.ofNat 26 24263183, component := 60 },
    { zero := BitVec.ofNat 26 22159147, component := 47 },
    { zero := BitVec.ofNat 26 32513579, component := 29 },
    { zero := BitVec.ofNat 26 24255019, component := 48 },
    { zero := BitVec.ofNat 26 26238765, component := 9 },
    { zero := BitVec.ofNat 26 28465965, component := 50 },
    { zero := BitVec.ofNat 26 26246925, component := 9 },
    { zero := BitVec.ofNat 26 30424845, component := 26 },
    { zero := BitVec.ofNat 26 28474125, component := 63 },
    { zero := BitVec.ofNat 26 32652045, component := 18 },
    { zero := BitVec.ofNat 26 30416681, component := 26 },
    { zero := BitVec.ofNat 26 32643881, component := 52 }
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

end Krenn.CollapseSupportCover.Mask253
