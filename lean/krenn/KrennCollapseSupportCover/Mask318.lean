import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask318

def activeValue : BitVec 14 := BitVec.ofNat 14 12304

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1187815, component := 26 },
    { zero := BitVec.ofNat 26 11542247, component := 18 },
    { zero := BitVec.ofNat 26 3283687, component := 41 },
    { zero := BitVec.ofNat 26 1449831, component := 49 },
    { zero := BitVec.ofNat 26 11804263, component := 18 },
    { zero := BitVec.ofNat 26 3545703, component := 52 },
    { zero := BitVec.ofNat 26 1457991, component := 62 },
    { zero := BitVec.ofNat 26 11812423, component := 18 },
    { zero := BitVec.ofNat 26 3553863, component := 65 },
    { zero := BitVec.ofNat 26 9445349, component := 26 },
    { zero := BitVec.ofNat 26 11672549, component := 18 },
    { zero := BitVec.ofNat 26 9707365, component := 17 },
    { zero := BitVec.ofNat 26 11934565, component := 18 },
    { zero := BitVec.ofNat 26 9715525, component := 17 },
    { zero := BitVec.ofNat 26 11942725, component := 18 },
    { zero := BitVec.ofNat 26 1195974, component := 61 },
    { zero := BitVec.ofNat 26 11550406, component := 41 },
    { zero := BitVec.ofNat 26 3291846, component := 66 },
    { zero := BitVec.ofNat 26 9453508, component := 26 },
    { zero := BitVec.ofNat 26 11680708, component := 65 }
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

end Krenn.CollapseSupportCover.Mask318
