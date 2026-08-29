import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask015

def activeValue : BitVec 14 := BitVec.ofNat 14 128

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18079535, component := 50 },
    { zero := BitVec.ofNat 26 51601199, component := 50 },
    { zero := BitVec.ofNat 26 28433967, component := 18 },
    { zero := BitVec.ofNat 26 61955631, component := 18 },
    { zero := BitVec.ofNat 26 20175407, component := 52 },
    { zero := BitVec.ofNat 26 53697071, component := 52 },
    { zero := BitVec.ofNat 26 18087695, component := 63 },
    { zero := BitVec.ofNat 26 51609359, component := 63 },
    { zero := BitVec.ofNat 26 22265615, component := 59 },
    { zero := BitVec.ofNat 26 55787279, component := 59 },
    { zero := BitVec.ofNat 26 28442127, component := 18 },
    { zero := BitVec.ofNat 26 61963791, component := 18 },
    { zero := BitVec.ofNat 26 32620047, component := 18 },
    { zero := BitVec.ofNat 26 66141711, component := 18 },
    { zero := BitVec.ofNat 26 20183567, component := 65 },
    { zero := BitVec.ofNat 26 53705231, component := 65 },
    { zero := BitVec.ofNat 26 24361487, component := 60 },
    { zero := BitVec.ofNat 26 57883151, component := 60 },
    { zero := BitVec.ofNat 26 22257451, component := 47 },
    { zero := BitVec.ofNat 26 55779115, component := 47 },
    { zero := BitVec.ofNat 26 32611883, component := 36 },
    { zero := BitVec.ofNat 26 66133547, component := 29 },
    { zero := BitVec.ofNat 26 24353323, component := 48 },
    { zero := BitVec.ofNat 26 57874987, component := 48 },
    { zero := BitVec.ofNat 26 26337069, component := 9 },
    { zero := BitVec.ofNat 26 59858733, component := 9 },
    { zero := BitVec.ofNat 26 28564269, component := 50 },
    { zero := BitVec.ofNat 26 62085933, component := 50 },
    { zero := BitVec.ofNat 26 26345229, component := 9 },
    { zero := BitVec.ofNat 26 59866893, component := 9 },
    { zero := BitVec.ofNat 26 30523149, component := 15 },
    { zero := BitVec.ofNat 26 64044813, component := 26 },
    { zero := BitVec.ofNat 26 28572429, component := 63 },
    { zero := BitVec.ofNat 26 62094093, component := 63 },
    { zero := BitVec.ofNat 26 32750349, component := 18 },
    { zero := BitVec.ofNat 26 66272013, component := 18 },
    { zero := BitVec.ofNat 26 30514985, component := 26 },
    { zero := BitVec.ofNat 26 64036649, component := 26 },
    { zero := BitVec.ofNat 26 32742185, component := 52 },
    { zero := BitVec.ofNat 26 66263849, component := 52 }
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

end Krenn.CollapseSupportCover.Mask015
