import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask042

def activeValue : BitVec 14 := BitVec.ofNat 14 608

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17026255, component := 38 },
    { zero := BitVec.ofNat 26 25283791, component := 38 },
    { zero := BitVec.ofNat 26 21204175, component := 38 },
    { zero := BitVec.ofNat 26 29461711, component := 38 },
    { zero := BitVec.ofNat 26 50580679, component := 38 },
    { zero := BitVec.ofNat 26 58838215, component := 38 },
    { zero := BitVec.ofNat 26 54758599, component := 38 },
    { zero := BitVec.ofNat 26 63016135, component := 38 }
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

end Krenn.CollapseSupportCover.Mask042
