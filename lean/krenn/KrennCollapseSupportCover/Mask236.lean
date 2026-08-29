import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask236

def activeValue : BitVec 14 := BitVec.ofNat 14 5632

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 44632255, component := 2 },
    { zero := BitVec.ofNat 26 44632311, component := 2 },
    { zero := BitVec.ofNat 26 44632509, component := 2 },
    { zero := BitVec.ofNat 26 44632565, component := 2 },
    { zero := BitVec.ofNat 26 44640414, component := 5 },
    { zero := BitVec.ofNat 26 44640470, component := 5 },
    { zero := BitVec.ofNat 26 44640668, component := 5 },
    { zero := BitVec.ofNat 26 44640724, component := 5 }
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

end Krenn.CollapseSupportCover.Mask236
