import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask003

def activeValue : BitVec 14 := BitVec.ofNat 14 4

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 62480037, component := 18 },
    { zero := BitVec.ofNat 26 62508709, component := 18 },
    { zero := BitVec.ofNat 26 62610085, component := 18 },
    { zero := BitVec.ofNat 26 62638757, component := 18 },
    { zero := BitVec.ofNat 26 62741541, component := 3 },
    { zero := BitVec.ofNat 26 62770213, component := 3 },
    { zero := BitVec.ofNat 26 62871589, component := 3 },
    { zero := BitVec.ofNat 26 62900261, component := 3 },
    { zero := BitVec.ofNat 26 62749701, component := 3 },
    { zero := BitVec.ofNat 26 66927621, component := 26 },
    { zero := BitVec.ofNat 26 62778373, component := 3 },
    { zero := BitVec.ofNat 26 66956293, component := 15 },
    { zero := BitVec.ofNat 26 62879749, component := 3 },
    { zero := BitVec.ofNat 26 67057669, component := 26 },
    { zero := BitVec.ofNat 26 62908421, component := 3 },
    { zero := BitVec.ofNat 26 67086341, component := 26 },
    { zero := BitVec.ofNat 26 66657953, component := 42 },
    { zero := BitVec.ofNat 26 66686625, component := 42 },
    { zero := BitVec.ofNat 26 66788001, component := 52 },
    { zero := BitVec.ofNat 26 66816673, component := 42 },
    { zero := BitVec.ofNat 26 66919457, component := 26 },
    { zero := BitVec.ofNat 26 66948129, component := 26 },
    { zero := BitVec.ofNat 26 67049505, component := 26 },
    { zero := BitVec.ofNat 26 67078177, component := 26 },
    { zero := BitVec.ofNat 26 62488196, component := 20 },
    { zero := BitVec.ofNat 26 66666116, component := 20 },
    { zero := BitVec.ofNat 26 62516868, component := 20 },
    { zero := BitVec.ofNat 26 66694788, component := 20 },
    { zero := BitVec.ofNat 26 62618244, component := 20 },
    { zero := BitVec.ofNat 26 66796164, component := 20 },
    { zero := BitVec.ofNat 26 62646916, component := 20 },
    { zero := BitVec.ofNat 26 66824836, component := 20 },
    { zero := BitVec.ofNat 26 62749828, component := 6 },
    { zero := BitVec.ofNat 26 66927748, component := 26 },
    { zero := BitVec.ofNat 26 62778500, component := 6 },
    { zero := BitVec.ofNat 26 66956420, component := 19 },
    { zero := BitVec.ofNat 26 62879876, component := 6 },
    { zero := BitVec.ofNat 26 67057796, component := 26 },
    { zero := BitVec.ofNat 26 62908548, component := 6 },
    { zero := BitVec.ofNat 26 67086468, component := 26 },
    { zero := BitVec.ofNat 26 66666144, component := 42 },
    { zero := BitVec.ofNat 26 66694816, component := 42 },
    { zero := BitVec.ofNat 26 66796192, component := 42 },
    { zero := BitVec.ofNat 26 66824864, component := 42 },
    { zero := BitVec.ofNat 26 66927776, component := 26 },
    { zero := BitVec.ofNat 26 66956448, component := 33 },
    { zero := BitVec.ofNat 26 67057824, component := 26 },
    { zero := BitVec.ofNat 26 67086496, component := 26 }
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

end Krenn.CollapseSupportCover.Mask003
