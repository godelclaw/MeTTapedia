import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask163

def activeValue : BitVec 14 := BitVec.ofNat 14 4112

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1286119, component := 38 },
    { zero := BitVec.ofNat 26 1806311, component := 38 },
    { zero := BitVec.ofNat 26 11640551, component := 38 },
    { zero := BitVec.ofNat 26 12160743, component := 38 },
    { zero := BitVec.ofNat 26 3381991, component := 41 },
    { zero := BitVec.ofNat 26 3902183, component := 41 },
    { zero := BitVec.ofNat 26 1547623, component := 49 },
    { zero := BitVec.ofNat 26 2067815, component := 37 },
    { zero := BitVec.ofNat 26 11902055, component := 15 },
    { zero := BitVec.ofNat 26 12422247, component := 15 },
    { zero := BitVec.ofNat 26 3643495, component := 26 },
    { zero := BitVec.ofNat 26 4163687, component := 26 },
    { zero := BitVec.ofNat 26 1555783, component := 62 },
    { zero := BitVec.ofNat 26 2075975, component := 37 },
    { zero := BitVec.ofNat 26 11910215, component := 15 },
    { zero := BitVec.ofNat 26 12430407, component := 15 },
    { zero := BitVec.ofNat 26 3651655, component := 26 },
    { zero := BitVec.ofNat 26 4171847, component := 26 },
    { zero := BitVec.ofNat 26 9543653, component := 15 },
    { zero := BitVec.ofNat 26 10063845, component := 15 },
    { zero := BitVec.ofNat 26 11770853, component := 18 },
    { zero := BitVec.ofNat 26 12291045, component := 18 },
    { zero := BitVec.ofNat 26 9805157, component := 16 },
    { zero := BitVec.ofNat 26 10325349, component := 16 },
    { zero := BitVec.ofNat 26 12032357, component := 49 },
    { zero := BitVec.ofNat 26 12552549, component := 17 },
    { zero := BitVec.ofNat 26 9813317, component := 16 },
    { zero := BitVec.ofNat 26 10333509, component := 16 },
    { zero := BitVec.ofNat 26 12040517, component := 62 },
    { zero := BitVec.ofNat 26 12560709, component := 17 },
    { zero := BitVec.ofNat 26 1294278, component := 38 },
    { zero := BitVec.ofNat 26 1814470, component := 38 },
    { zero := BitVec.ofNat 26 1555910, component := 38 },
    { zero := BitVec.ofNat 26 2076102, component := 38 },
    { zero := BitVec.ofNat 26 11648710, component := 38 },
    { zero := BitVec.ofNat 26 12168902, component := 20 },
    { zero := BitVec.ofNat 26 3390150, component := 66 },
    { zero := BitVec.ofNat 26 3910342, component := 41 },
    { zero := BitVec.ofNat 26 11910342, component := 38 },
    { zero := BitVec.ofNat 26 12430534, component := 38 },
    { zero := BitVec.ofNat 26 3651782, component := 61 },
    { zero := BitVec.ofNat 26 4171974, component := 26 },
    { zero := BitVec.ofNat 26 9551812, component := 26 },
    { zero := BitVec.ofNat 26 10072004, component := 19 },
    { zero := BitVec.ofNat 26 11779012, component := 65 },
    { zero := BitVec.ofNat 26 12299204, component := 20 },
    { zero := BitVec.ofNat 26 9813444, component := 37 },
    { zero := BitVec.ofNat 26 10333636, component := 19 },
    { zero := BitVec.ofNat 26 12040644, component := 62 },
    { zero := BitVec.ofNat 26 12560836, component := 26 }
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

end Krenn.CollapseSupportCover.Mask163
