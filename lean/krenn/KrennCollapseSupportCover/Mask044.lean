import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask044

def activeValue : BitVec 14 := BitVec.ofNat 14 640

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17030463, component := 51 },
    { zero := BitVec.ofNat 26 50552127, component := 51 },
    { zero := BitVec.ofNat 26 27384895, component := 15 },
    { zero := BitVec.ofNat 26 60906559, component := 2 },
    { zero := BitVec.ofNat 26 19126335, component := 26 },
    { zero := BitVec.ofNat 26 52647999, component := 43 },
    { zero := BitVec.ofNat 26 17038623, component := 64 },
    { zero := BitVec.ofNat 26 50560287, component := 64 },
    { zero := BitVec.ofNat 26 21216543, component := 64 },
    { zero := BitVec.ofNat 26 54738207, component := 64 },
    { zero := BitVec.ofNat 26 27393055, component := 15 },
    { zero := BitVec.ofNat 26 60914719, component := 2 },
    { zero := BitVec.ofNat 26 31570975, component := 36 },
    { zero := BitVec.ofNat 26 65092639, component := 2 },
    { zero := BitVec.ofNat 26 19134495, component := 26 },
    { zero := BitVec.ofNat 26 52656159, component := 53 },
    { zero := BitVec.ofNat 26 23312415, component := 59 },
    { zero := BitVec.ofNat 26 56834079, component := 59 },
    { zero := BitVec.ofNat 26 21208379, component := 51 },
    { zero := BitVec.ofNat 26 54730043, component := 51 },
    { zero := BitVec.ofNat 26 31562811, component := 36 },
    { zero := BitVec.ofNat 26 65084475, component := 26 },
    { zero := BitVec.ofNat 26 23304251, component := 47 },
    { zero := BitVec.ofNat 26 56825915, component := 43 },
    { zero := BitVec.ofNat 26 25287997, component := 11 },
    { zero := BitVec.ofNat 26 58809661, component := 10 },
    { zero := BitVec.ofNat 26 27515197, component := 51 },
    { zero := BitVec.ofNat 26 61036861, component := 51 },
    { zero := BitVec.ofNat 26 25296157, component := 11 },
    { zero := BitVec.ofNat 26 58817821, component := 10 },
    { zero := BitVec.ofNat 26 29474077, component := 11 },
    { zero := BitVec.ofNat 26 62995741, component := 10 },
    { zero := BitVec.ofNat 26 27523357, component := 64 },
    { zero := BitVec.ofNat 26 61045021, component := 64 },
    { zero := BitVec.ofNat 26 31701277, component := 64 },
    { zero := BitVec.ofNat 26 65222941, component := 64 },
    { zero := BitVec.ofNat 26 29465913, component := 35 },
    { zero := BitVec.ofNat 26 62987577, component := 26 },
    { zero := BitVec.ofNat 26 31693113, component := 51 },
    { zero := BitVec.ofNat 26 65214777, component := 51 }
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

end Krenn.CollapseSupportCover.Mask044
