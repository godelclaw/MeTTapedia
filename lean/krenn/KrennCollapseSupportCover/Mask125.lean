import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask125

def activeValue : BitVec 14 := BitVec.ofNat 14 3072

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 60375981, component := 9 },
    { zero := BitVec.ofNat 26 60637485, component := 3 },
    { zero := BitVec.ofNat 26 60645645, component := 3 },
    { zero := BitVec.ofNat 26 60376037, component := 3 },
    { zero := BitVec.ofNat 26 60637541, component := 4 },
    { zero := BitVec.ofNat 26 60645701, component := 4 },
    { zero := BitVec.ofNat 26 64570281, component := 39 },
    { zero := BitVec.ofNat 26 64831785, component := 26 },
    { zero := BitVec.ofNat 26 64570337, component := 25 },
    { zero := BitVec.ofNat 26 64831841, component := 23 },
    { zero := BitVec.ofNat 26 60384140, component := 12 },
    { zero := BitVec.ofNat 26 60645772, component := 6 },
    { zero := BitVec.ofNat 26 60384196, component := 6 },
    { zero := BitVec.ofNat 26 60645828, component := 6 },
    { zero := BitVec.ofNat 26 64578472, component := 39 },
    { zero := BitVec.ofNat 26 64840104, component := 25 },
    { zero := BitVec.ofNat 26 64578528, component := 25 },
    { zero := BitVec.ofNat 26 64840160, component := 25 }
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

end Krenn.CollapseSupportCover.Mask125
