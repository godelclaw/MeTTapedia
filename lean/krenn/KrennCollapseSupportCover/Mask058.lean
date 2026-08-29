import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask058

def activeValue : BitVec 14 := BitVec.ofNat 14 704

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17026335, component := 35 },
    { zero := BitVec.ofNat 26 21204255, component := 36 },
    { zero := BitVec.ofNat 26 27380767, component := 15 },
    { zero := BitVec.ofNat 26 31558687, component := 36 },
    { zero := BitVec.ofNat 26 19122207, component := 26 },
    { zero := BitVec.ofNat 26 23300127, component := 26 },
    { zero := BitVec.ofNat 26 25283869, component := 11 },
    { zero := BitVec.ofNat 26 29461789, component := 11 },
    { zero := BitVec.ofNat 26 27511069, component := 10 },
    { zero := BitVec.ofNat 26 31688989, component := 10 }
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

end Krenn.CollapseSupportCover.Mask058
