import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask011

def activeValue : BitVec 14 := BitVec.ofNat 14 64

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18075599, component := 38 },
    { zero := BitVec.ofNat 26 22253519, component := 38 },
    { zero := BitVec.ofNat 26 28430031, component := 38 },
    { zero := BitVec.ofNat 26 32607951, component := 38 },
    { zero := BitVec.ofNat 26 20171471, component := 41 },
    { zero := BitVec.ofNat 26 24349391, component := 41 },
    { zero := BitVec.ofNat 26 18337103, component := 37 },
    { zero := BitVec.ofNat 26 22515023, component := 36 },
    { zero := BitVec.ofNat 26 28691535, component := 15 },
    { zero := BitVec.ofNat 26 32869455, component := 36 },
    { zero := BitVec.ofNat 26 20432975, component := 26 },
    { zero := BitVec.ofNat 26 24610895, component := 26 },
    { zero := BitVec.ofNat 26 51630023, component := 38 },
    { zero := BitVec.ofNat 26 55807943, component := 38 },
    { zero := BitVec.ofNat 26 61984455, component := 38 },
    { zero := BitVec.ofNat 26 66162375, component := 38 },
    { zero := BitVec.ofNat 26 53725895, component := 24 },
    { zero := BitVec.ofNat 26 57903815, component := 41 },
    { zero := BitVec.ofNat 26 51891527, component := 37 },
    { zero := BitVec.ofNat 26 56069447, component := 37 },
    { zero := BitVec.ofNat 26 62245959, component := 3 },
    { zero := BitVec.ofNat 26 66423879, component := 15 },
    { zero := BitVec.ofNat 26 53987399, component := 26 },
    { zero := BitVec.ofNat 26 58165319, component := 26 },
    { zero := BitVec.ofNat 26 26333133, component := 9 },
    { zero := BitVec.ofNat 26 30511053, component := 15 },
    { zero := BitVec.ofNat 26 28560333, component := 9 },
    { zero := BitVec.ofNat 26 32738253, component := 18 },
    { zero := BitVec.ofNat 26 26594637, component := 16 },
    { zero := BitVec.ofNat 26 30772557, component := 16 },
    { zero := BitVec.ofNat 26 28821837, component := 17 },
    { zero := BitVec.ofNat 26 32999757, component := 17 },
    { zero := BitVec.ofNat 26 59887557, component := 3 },
    { zero := BitVec.ofNat 26 64065477, component := 15 },
    { zero := BitVec.ofNat 26 62114757, component := 18 },
    { zero := BitVec.ofNat 26 66292677, component := 18 },
    { zero := BitVec.ofNat 26 60149061, component := 4 },
    { zero := BitVec.ofNat 26 64326981, component := 16 },
    { zero := BitVec.ofNat 26 62376261, component := 4 },
    { zero := BitVec.ofNat 26 66554181, component := 17 }
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

end Krenn.CollapseSupportCover.Mask011
