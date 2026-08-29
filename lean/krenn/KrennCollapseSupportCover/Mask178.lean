import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask178

def activeValue : BitVec 14 := BitVec.ofNat 14 4224

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1285951, component := 51 },
    { zero := BitVec.ofNat 26 34807615, component := 51 },
    { zero := BitVec.ofNat 26 11640383, component := 18 },
    { zero := BitVec.ofNat 26 45162047, component := 2 },
    { zero := BitVec.ofNat 26 3381823, component := 52 },
    { zero := BitVec.ofNat 26 36903487, component := 43 },
    { zero := BitVec.ofNat 26 1294111, component := 64 },
    { zero := BitVec.ofNat 26 34815775, component := 64 },
    { zero := BitVec.ofNat 26 11648543, component := 18 },
    { zero := BitVec.ofNat 26 45170207, component := 2 },
    { zero := BitVec.ofNat 26 3389983, component := 65 },
    { zero := BitVec.ofNat 26 36911647, component := 53 },
    { zero := BitVec.ofNat 26 9543485, component := 11 },
    { zero := BitVec.ofNat 26 43065149, component := 10 },
    { zero := BitVec.ofNat 26 11770685, component := 51 },
    { zero := BitVec.ofNat 26 45292349, component := 51 },
    { zero := BitVec.ofNat 26 9551645, component := 11 },
    { zero := BitVec.ofNat 26 43073309, component := 10 },
    { zero := BitVec.ofNat 26 11778845, component := 64 },
    { zero := BitVec.ofNat 26 45300509, component := 64 }
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

end Krenn.CollapseSupportCover.Mask178
