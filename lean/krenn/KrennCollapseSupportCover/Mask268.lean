import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask268

def activeValue : BitVec 14 := BitVec.ofNat 14 10240

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17978351, component := 50 },
    { zero := BitVec.ofNat 26 18240367, component := 50 },
    { zero := BitVec.ofNat 26 18502575, component := 50 },
    { zero := BitVec.ofNat 26 18764591, component := 50 },
    { zero := BitVec.ofNat 26 18248527, component := 63 },
    { zero := BitVec.ofNat 26 18772751, component := 63 },
    { zero := BitVec.ofNat 26 22172651, component := 50 },
    { zero := BitVec.ofNat 26 22434667, component := 50 },
    { zero := BitVec.ofNat 26 22696875, component := 50 },
    { zero := BitVec.ofNat 26 22958891, component := 50 },
    { zero := BitVec.ofNat 26 26366957, component := 50 },
    { zero := BitVec.ofNat 26 26628973, component := 50 },
    { zero := BitVec.ofNat 26 26891181, component := 50 },
    { zero := BitVec.ofNat 26 27153197, component := 50 },
    { zero := BitVec.ofNat 26 26637133, component := 63 },
    { zero := BitVec.ofNat 26 27161357, component := 63 },
    { zero := BitVec.ofNat 26 30561257, component := 50 },
    { zero := BitVec.ofNat 26 30823273, component := 50 },
    { zero := BitVec.ofNat 26 31085481, component := 50 },
    { zero := BitVec.ofNat 26 31347497, component := 50 },
    { zero := BitVec.ofNat 26 17986510, component := 63 },
    { zero := BitVec.ofNat 26 18510734, component := 63 },
    { zero := BitVec.ofNat 26 22180842, component := 63 },
    { zero := BitVec.ofNat 26 22705066, component := 63 },
    { zero := BitVec.ofNat 26 26375116, component := 63 },
    { zero := BitVec.ofNat 26 26899340, component := 12 },
    { zero := BitVec.ofNat 26 30569448, component := 63 },
    { zero := BitVec.ofNat 26 31093672, component := 63 }
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

end Krenn.CollapseSupportCover.Mask268
