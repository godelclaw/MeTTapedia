import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask107

def activeValue : BitVec 14 := BitVec.ofNat 14 2592

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17027311, component := 26 },
    { zero := BitVec.ofNat 26 51073199, component := 25 },
    { zero := BitVec.ofNat 26 17547439, component := 26 },
    { zero := BitVec.ofNat 26 50548967, component := 24 },
    { zero := BitVec.ofNat 26 51101927, component := 24 },
    { zero := BitVec.ofNat 26 21221611, component := 47 },
    { zero := BitVec.ofNat 26 55267499, component := 47 },
    { zero := BitVec.ofNat 26 21741739, component := 31 },
    { zero := BitVec.ofNat 26 54743267, component := 45 },
    { zero := BitVec.ofNat 26 55296227, component := 25 },
    { zero := BitVec.ofNat 26 17035470, component := 61 },
    { zero := BitVec.ofNat 26 51081358, component := 56 },
    { zero := BitVec.ofNat 26 17555598, component := 26 },
    { zero := BitVec.ofNat 26 50557126, component := 58 },
    { zero := BitVec.ofNat 26 51110086, component := 24 },
    { zero := BitVec.ofNat 26 21229802, component := 59 },
    { zero := BitVec.ofNat 26 55275690, component := 59 },
    { zero := BitVec.ofNat 26 21749930, component := 31 },
    { zero := BitVec.ofNat 26 54751458, component := 56 },
    { zero := BitVec.ofNat 26 55304418, component := 25 }
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

end Krenn.CollapseSupportCover.Mask107
