import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask067

def activeValue : BitVec 14 := BitVec.ofNat 14 1024

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 62474927, component := 18 },
    { zero := BitVec.ofNat 26 62736431, component := 3 },
    { zero := BitVec.ofNat 26 62744591, component := 3 },
    { zero := BitVec.ofNat 26 66922511, component := 26 },
    { zero := BitVec.ofNat 26 62474983, component := 18 },
    { zero := BitVec.ofNat 26 62736487, component := 3 },
    { zero := BitVec.ofNat 26 62744647, component := 3 },
    { zero := BitVec.ofNat 26 66922567, component := 26 },
    { zero := BitVec.ofNat 26 66652843, component := 30 },
    { zero := BitVec.ofNat 26 66914347, component := 26 },
    { zero := BitVec.ofNat 26 66652899, component := 42 },
    { zero := BitVec.ofNat 26 66914403, component := 26 },
    { zero := BitVec.ofNat 26 62475181, component := 9 },
    { zero := BitVec.ofNat 26 62736685, component := 3 },
    { zero := BitVec.ofNat 26 62744845, component := 3 },
    { zero := BitVec.ofNat 26 66922765, component := 26 },
    { zero := BitVec.ofNat 26 62475237, component := 18 },
    { zero := BitVec.ofNat 26 62736741, component := 4 },
    { zero := BitVec.ofNat 26 62744901, component := 4 },
    { zero := BitVec.ofNat 26 66922821, component := 17 },
    { zero := BitVec.ofNat 26 66653097, component := 42 },
    { zero := BitVec.ofNat 26 66914601, component := 26 },
    { zero := BitVec.ofNat 26 66653153, component := 42 },
    { zero := BitVec.ofNat 26 66914657, component := 26 },
    { zero := BitVec.ofNat 26 62483086, component := 20 },
    { zero := BitVec.ofNat 26 66661006, component := 20 },
    { zero := BitVec.ofNat 26 62744718, component := 6 },
    { zero := BitVec.ofNat 26 66922638, component := 26 },
    { zero := BitVec.ofNat 26 62483142, component := 20 },
    { zero := BitVec.ofNat 26 66661062, component := 20 },
    { zero := BitVec.ofNat 26 62744774, component := 6 },
    { zero := BitVec.ofNat 26 66922694, component := 26 },
    { zero := BitVec.ofNat 26 66661034, component := 30 },
    { zero := BitVec.ofNat 26 66922666, component := 31 },
    { zero := BitVec.ofNat 26 66661090, component := 42 },
    { zero := BitVec.ofNat 26 66922722, component := 26 },
    { zero := BitVec.ofNat 26 62483340, component := 12 },
    { zero := BitVec.ofNat 26 66661260, component := 20 },
    { zero := BitVec.ofNat 26 62744972, component := 6 },
    { zero := BitVec.ofNat 26 66922892, component := 26 },
    { zero := BitVec.ofNat 26 62483396, component := 20 },
    { zero := BitVec.ofNat 26 66661316, component := 20 },
    { zero := BitVec.ofNat 26 62745028, component := 6 },
    { zero := BitVec.ofNat 26 66922948, component := 26 },
    { zero := BitVec.ofNat 26 66661288, component := 42 },
    { zero := BitVec.ofNat 26 66922920, component := 26 },
    { zero := BitVec.ofNat 26 66661344, component := 42 },
    { zero := BitVec.ofNat 26 66922976, component := 26 }
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

end Krenn.CollapseSupportCover.Mask067
