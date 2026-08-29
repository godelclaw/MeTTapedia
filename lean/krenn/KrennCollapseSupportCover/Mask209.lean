import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask209

def activeValue : BitVec 14 := BitVec.ofNat 14 4736

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 236863, component := 51 },
    { zero := BitVec.ofNat 26 33758527, component := 51 },
    { zero := BitVec.ofNat 26 10591295, component := 15 },
    { zero := BitVec.ofNat 26 44112959, component := 2 },
    { zero := BitVec.ofNat 26 2332735, component := 26 },
    { zero := BitVec.ofNat 26 35854399, component := 43 },
    { zero := BitVec.ofNat 26 245023, component := 64 },
    { zero := BitVec.ofNat 26 33766687, component := 64 },
    { zero := BitVec.ofNat 26 10599455, component := 15 },
    { zero := BitVec.ofNat 26 44121119, component := 2 },
    { zero := BitVec.ofNat 26 2340895, component := 26 },
    { zero := BitVec.ofNat 26 35862559, component := 53 },
    { zero := BitVec.ofNat 26 8494397, component := 11 },
    { zero := BitVec.ofNat 26 42016061, component := 10 },
    { zero := BitVec.ofNat 26 10721597, component := 51 },
    { zero := BitVec.ofNat 26 44243261, component := 51 },
    { zero := BitVec.ofNat 26 8502557, component := 11 },
    { zero := BitVec.ofNat 26 42024221, component := 10 },
    { zero := BitVec.ofNat 26 10729757, component := 64 },
    { zero := BitVec.ofNat 26 44251421, component := 64 }
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

end Krenn.CollapseSupportCover.Mask209
