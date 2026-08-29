import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask327

def activeValue : BitVec 14 := BitVec.ofNat 14 12416

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1187647, component := 51 },
    { zero := BitVec.ofNat 26 11542079, component := 18 },
    { zero := BitVec.ofNat 26 3283519, component := 52 },
    { zero := BitVec.ofNat 26 1195807, component := 64 },
    { zero := BitVec.ofNat 26 11550239, component := 18 },
    { zero := BitVec.ofNat 26 3291679, component := 65 },
    { zero := BitVec.ofNat 26 9445181, component := 10 },
    { zero := BitVec.ofNat 26 11672381, component := 51 },
    { zero := BitVec.ofNat 26 9453341, component := 10 },
    { zero := BitVec.ofNat 26 11680541, component := 64 }
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

end Krenn.CollapseSupportCover.Mask327
