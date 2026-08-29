import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask155

def activeValue : BitVec 14 := BitVec.ofNat 14 4098

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1155070, component := 38 },
    { zero := BitVec.ofNat 26 1416702, component := 38 },
    { zero := BitVec.ofNat 26 3251966, component := 38 },
    { zero := BitVec.ofNat 26 3513598, component := 38 },
    { zero := BitVec.ofNat 26 35200958, component := 40 },
    { zero := BitVec.ofNat 26 1675198, component := 34 },
    { zero := BitVec.ofNat 26 35462590, component := 40 },
    { zero := BitVec.ofNat 26 1936830, component := 34 },
    { zero := BitVec.ofNat 26 37297854, component := 22 },
    { zero := BitVec.ofNat 26 3772094, component := 42 },
    { zero := BitVec.ofNat 26 37559486, component := 22 },
    { zero := BitVec.ofNat 26 4033726, component := 33 },
    { zero := BitVec.ofNat 26 34676726, component := 26 },
    { zero := BitVec.ofNat 26 35229686, component := 38 },
    { zero := BitVec.ofNat 26 34938358, component := 26 },
    { zero := BitVec.ofNat 26 35491318, component := 38 },
    { zero := BitVec.ofNat 26 36773622, component := 21 },
    { zero := BitVec.ofNat 26 37326582, component := 38 },
    { zero := BitVec.ofNat 26 37035254, component := 21 },
    { zero := BitVec.ofNat 26 37588214, component := 38 }
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

end Krenn.CollapseSupportCover.Mask155
