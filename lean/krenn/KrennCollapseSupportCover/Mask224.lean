import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask224

def activeValue : BitVec 14 := BitVec.ofNat 14 5120

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 45681343, component := 2 },
    { zero := BitVec.ofNat 26 45942847, component := 2 },
    { zero := BitVec.ofNat 26 45951007, component := 2 },
    { zero := BitVec.ofNat 26 45681399, component := 2 },
    { zero := BitVec.ofNat 26 45942903, component := 2 },
    { zero := BitVec.ofNat 26 45951063, component := 2 },
    { zero := BitVec.ofNat 26 45681597, component := 2 },
    { zero := BitVec.ofNat 26 45943101, component := 2 },
    { zero := BitVec.ofNat 26 45951261, component := 2 },
    { zero := BitVec.ofNat 26 45681653, component := 2 },
    { zero := BitVec.ofNat 26 45943157, component := 2 },
    { zero := BitVec.ofNat 26 45951317, component := 2 },
    { zero := BitVec.ofNat 26 45689502, component := 5 },
    { zero := BitVec.ofNat 26 45951134, component := 5 },
    { zero := BitVec.ofNat 26 45689558, component := 5 },
    { zero := BitVec.ofNat 26 45951190, component := 5 },
    { zero := BitVec.ofNat 26 45689756, component := 5 },
    { zero := BitVec.ofNat 26 45951388, component := 5 },
    { zero := BitVec.ofNat 26 45689812, component := 5 },
    { zero := BitVec.ofNat 26 45951444, component := 5 }
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

end Krenn.CollapseSupportCover.Mask224
