import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask001

def activeValue : BitVec 14 := BitVec.ofNat 14 1

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22527306, component := 59 },
    { zero := BitVec.ofNat 26 32881738, component := 36 },
    { zero := BitVec.ofNat 26 24623178, component := 59 },
    { zero := BitVec.ofNat 26 56573194, component := 59 },
    { zero := BitVec.ofNat 26 23047434, component := 36 },
    { zero := BitVec.ofNat 26 66927626, component := 26 },
    { zero := BitVec.ofNat 26 33401866, component := 36 },
    { zero := BitVec.ofNat 26 58669066, component := 59 },
    { zero := BitVec.ofNat 26 25143306, component := 28 },
    { zero := BitVec.ofNat 26 56048962, component := 62 },
    { zero := BitVec.ofNat 26 56601922, component := 37 },
    { zero := BitVec.ofNat 26 66403394, component := 26 },
    { zero := BitVec.ofNat 26 66956354, component := 26 },
    { zero := BitVec.ofNat 26 58144834, component := 54 },
    { zero := BitVec.ofNat 26 58697794, component := 26 },
    { zero := BitVec.ofNat 26 30784840, component := 37 },
    { zero := BitVec.ofNat 26 33012040, component := 62 },
    { zero := BitVec.ofNat 26 64830728, component := 26 },
    { zero := BitVec.ofNat 26 31304968, component := 8 },
    { zero := BitVec.ofNat 26 67057928, component := 26 },
    { zero := BitVec.ofNat 26 33532168, component := 26 },
    { zero := BitVec.ofNat 26 64306496, component := 1 },
    { zero := BitVec.ofNat 26 64859456, component := 37 },
    { zero := BitVec.ofNat 26 66533696, component := 62 },
    { zero := BitVec.ofNat 26 67086656, component := 26 }
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

end Krenn.CollapseSupportCover.Mask001
