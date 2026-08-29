import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask002

def activeValue : BitVec 14 := BitVec.ofNat 14 2

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17948654, component := 38 },
    { zero := BitVec.ofNat 26 18210286, component := 38 },
    { zero := BitVec.ofNat 26 20045550, component := 38 },
    { zero := BitVec.ofNat 26 20307182, component := 38 },
    { zero := BitVec.ofNat 26 51994542, component := 39 },
    { zero := BitVec.ofNat 26 18468782, component := 39 },
    { zero := BitVec.ofNat 26 52256174, component := 25 },
    { zero := BitVec.ofNat 26 18730414, component := 33 },
    { zero := BitVec.ofNat 26 54091438, component := 42 },
    { zero := BitVec.ofNat 26 20565678, component := 42 },
    { zero := BitVec.ofNat 26 54353070, component := 25 },
    { zero := BitVec.ofNat 26 20827310, component := 33 },
    { zero := BitVec.ofNat 26 51470310, component := 24 },
    { zero := BitVec.ofNat 26 52023270, component := 38 },
    { zero := BitVec.ofNat 26 51731942, component := 24 },
    { zero := BitVec.ofNat 26 52284902, component := 38 },
    { zero := BitVec.ofNat 26 53567206, component := 24 },
    { zero := BitVec.ofNat 26 54120166, component := 38 },
    { zero := BitVec.ofNat 26 53828838, component := 24 },
    { zero := BitVec.ofNat 26 54381798, component := 38 },
    { zero := BitVec.ofNat 26 22126570, component := 36 },
    { zero := BitVec.ofNat 26 22388202, component := 36 },
    { zero := BitVec.ofNat 26 24223466, component := 36 },
    { zero := BitVec.ofNat 26 24485098, component := 36 },
    { zero := BitVec.ofNat 26 56172458, component := 31 },
    { zero := BitVec.ofNat 26 22646698, component := 32 },
    { zero := BitVec.ofNat 26 56434090, component := 31 },
    { zero := BitVec.ofNat 26 22908330, component := 32 },
    { zero := BitVec.ofNat 26 58269354, component := 30 },
    { zero := BitVec.ofNat 26 24743594, component := 32 },
    { zero := BitVec.ofNat 26 58530986, component := 31 },
    { zero := BitVec.ofNat 26 25005226, component := 32 },
    { zero := BitVec.ofNat 26 55648226, component := 26 },
    { zero := BitVec.ofNat 26 56201186, component := 33 },
    { zero := BitVec.ofNat 26 55909858, component := 26 },
    { zero := BitVec.ofNat 26 56462818, component := 37 },
    { zero := BitVec.ofNat 26 57745122, component := 26 },
    { zero := BitVec.ofNat 26 58298082, component := 42 },
    { zero := BitVec.ofNat 26 58006754, component := 26 },
    { zero := BitVec.ofNat 26 58559714, component := 33 }
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

end Krenn.CollapseSupportCover.Mask002
