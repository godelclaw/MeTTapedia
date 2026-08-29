import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask313

def activeValue : BitVec 14 := BitVec.ofNat 14 12288

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1187839, component := 51 },
    { zero := BitVec.ofNat 26 11542271, component := 18 },
    { zero := BitVec.ofNat 26 3283711, component := 41 },
    { zero := BitVec.ofNat 26 1449855, component := 51 },
    { zero := BitVec.ofNat 26 11804287, component := 18 },
    { zero := BitVec.ofNat 26 3545727, component := 52 },
    { zero := BitVec.ofNat 26 1712063, component := 51 },
    { zero := BitVec.ofNat 26 12066495, component := 18 },
    { zero := BitVec.ofNat 26 3807935, component := 52 },
    { zero := BitVec.ofNat 26 1974079, component := 51 },
    { zero := BitVec.ofNat 26 12328511, component := 18 },
    { zero := BitVec.ofNat 26 4069951, component := 52 },
    { zero := BitVec.ofNat 26 1458015, component := 64 },
    { zero := BitVec.ofNat 26 11812447, component := 18 },
    { zero := BitVec.ofNat 26 3553887, component := 65 },
    { zero := BitVec.ofNat 26 1982239, component := 64 },
    { zero := BitVec.ofNat 26 12336671, component := 18 },
    { zero := BitVec.ofNat 26 4078111, component := 65 },
    { zero := BitVec.ofNat 26 9445373, component := 10 },
    { zero := BitVec.ofNat 26 11672573, component := 51 },
    { zero := BitVec.ofNat 26 9707389, component := 10 },
    { zero := BitVec.ofNat 26 11934589, component := 51 },
    { zero := BitVec.ofNat 26 9969597, component := 10 },
    { zero := BitVec.ofNat 26 12196797, component := 51 },
    { zero := BitVec.ofNat 26 10231613, component := 10 },
    { zero := BitVec.ofNat 26 12458813, component := 51 },
    { zero := BitVec.ofNat 26 9715549, component := 10 },
    { zero := BitVec.ofNat 26 11942749, component := 64 },
    { zero := BitVec.ofNat 26 10239773, component := 10 },
    { zero := BitVec.ofNat 26 12466973, component := 64 },
    { zero := BitVec.ofNat 26 1195998, component := 64 },
    { zero := BitVec.ofNat 26 11550430, component := 41 },
    { zero := BitVec.ofNat 26 3291870, component := 66 },
    { zero := BitVec.ofNat 26 1720222, component := 64 },
    { zero := BitVec.ofNat 26 12074654, component := 20 },
    { zero := BitVec.ofNat 26 3816094, component := 65 },
    { zero := BitVec.ofNat 26 9453532, component := 26 },
    { zero := BitVec.ofNat 26 11680732, component := 64 },
    { zero := BitVec.ofNat 26 9977756, component := 13 },
    { zero := BitVec.ofNat 26 12204956, component := 20 }
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

end Krenn.CollapseSupportCover.Mask313
