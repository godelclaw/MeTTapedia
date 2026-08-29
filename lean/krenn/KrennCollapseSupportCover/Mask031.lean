import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask031

def activeValue : BitVec 14 := BitVec.ofNat 14 520

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17030649, component := 51 },
    { zero := BitVec.ofNat 26 19126777, component := 51 },
    { zero := BitVec.ofNat 26 51076537, component := 51 },
    { zero := BitVec.ofNat 26 17550777, component := 34 },
    { zero := BitVec.ofNat 26 53172665, component := 51 },
    { zero := BitVec.ofNat 26 19646905, component := 40 },
    { zero := BitVec.ofNat 26 50552305, component := 45 },
    { zero := BitVec.ofNat 26 51105265, component := 25 },
    { zero := BitVec.ofNat 26 52648433, component := 43 },
    { zero := BitVec.ofNat 26 53201393, component := 22 },
    { zero := BitVec.ofNat 26 17038840, component := 64 },
    { zero := BitVec.ofNat 26 19134968, component := 64 },
    { zero := BitVec.ofNat 26 51084728, component := 64 },
    { zero := BitVec.ofNat 26 17558968, component := 34 },
    { zero := BitVec.ofNat 26 53180856, component := 64 },
    { zero := BitVec.ofNat 26 19655096, component := 40 },
    { zero := BitVec.ofNat 26 50560496, component := 56 },
    { zero := BitVec.ofNat 26 51113456, component := 25 },
    { zero := BitVec.ofNat 26 52656624, component := 53 },
    { zero := BitVec.ofNat 26 53209584, component := 22 }
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

end Krenn.CollapseSupportCover.Mask031
