import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask035

def activeValue : BitVec 14 := BitVec.ofNat 14 544

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17030383, component := 38 },
    { zero := BitVec.ofNat 26 25287919, component := 38 },
    { zero := BitVec.ofNat 26 51076271, component := 25 },
    { zero := BitVec.ofNat 26 59333807, component := 3 },
    { zero := BitVec.ofNat 26 17550511, component := 33 },
    { zero := BitVec.ofNat 26 25808047, component := 15 },
    { zero := BitVec.ofNat 26 50552039, component := 24 },
    { zero := BitVec.ofNat 26 58809575, component := 24 },
    { zero := BitVec.ofNat 26 51104999, component := 38 },
    { zero := BitVec.ofNat 26 59362535, component := 38 },
    { zero := BitVec.ofNat 26 21208299, component := 47 },
    { zero := BitVec.ofNat 26 29465835, component := 36 },
    { zero := BitVec.ofNat 26 55254187, component := 47 },
    { zero := BitVec.ofNat 26 63511723, component := 31 },
    { zero := BitVec.ofNat 26 21728427, component := 32 },
    { zero := BitVec.ofNat 26 29985963, component := 32 },
    { zero := BitVec.ofNat 26 54729955, component := 26 },
    { zero := BitVec.ofNat 26 62987491, component := 26 },
    { zero := BitVec.ofNat 26 55282915, component := 33 },
    { zero := BitVec.ofNat 26 63540451, component := 33 },
    { zero := BitVec.ofNat 26 17038542, component := 38 },
    { zero := BitVec.ofNat 26 25296078, component := 38 },
    { zero := BitVec.ofNat 26 21216462, component := 38 },
    { zero := BitVec.ofNat 26 29473998, component := 38 },
    { zero := BitVec.ofNat 26 51084430, component := 56 },
    { zero := BitVec.ofNat 26 59341966, component := 6 },
    { zero := BitVec.ofNat 26 55262350, component := 59 },
    { zero := BitVec.ofNat 26 63519886, component := 26 },
    { zero := BitVec.ofNat 26 17558670, component := 26 },
    { zero := BitVec.ofNat 26 25816206, component := 19 },
    { zero := BitVec.ofNat 26 21736590, component := 36 },
    { zero := BitVec.ofNat 26 29994126, component := 19 },
    { zero := BitVec.ofNat 26 50560198, component := 58 },
    { zero := BitVec.ofNat 26 58817734, component := 24 },
    { zero := BitVec.ofNat 26 54738118, component := 61 },
    { zero := BitVec.ofNat 26 62995654, component := 26 },
    { zero := BitVec.ofNat 26 51113158, component := 38 },
    { zero := BitVec.ofNat 26 59370694, component := 38 },
    { zero := BitVec.ofNat 26 55291078, component := 38 },
    { zero := BitVec.ofNat 26 63548614, component := 38 },
    { zero := BitVec.ofNat 26 21216490, component := 59 },
    { zero := BitVec.ofNat 26 29474026, component := 36 },
    { zero := BitVec.ofNat 26 55262378, component := 59 },
    { zero := BitVec.ofNat 26 63519914, component := 31 },
    { zero := BitVec.ofNat 26 21736618, component := 32 },
    { zero := BitVec.ofNat 26 29994154, component := 32 },
    { zero := BitVec.ofNat 26 54738146, component := 26 },
    { zero := BitVec.ofNat 26 62995682, component := 26 },
    { zero := BitVec.ofNat 26 55291106, component := 33 },
    { zero := BitVec.ofNat 26 63548642, component := 33 }
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

end Krenn.CollapseSupportCover.Mask035
