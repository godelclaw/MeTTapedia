import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask023

def activeValue : BitVec 14 := BitVec.ofNat 14 192

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18075407, component := 26 },
    { zero := BitVec.ofNat 26 22253327, component := 36 },
    { zero := BitVec.ofNat 26 28429839, component := 18 },
    { zero := BitVec.ofNat 26 32607759, component := 18 },
    { zero := BitVec.ofNat 26 20171279, component := 26 },
    { zero := BitVec.ofNat 26 24349199, component := 29 },
    { zero := BitVec.ofNat 26 26332941, component := 9 },
    { zero := BitVec.ofNat 26 30510861, component := 15 },
    { zero := BitVec.ofNat 26 28560141, component := 9 },
    { zero := BitVec.ofNat 26 32738061, component := 18 }
]

def data : ActiveCover := {
  active := activeValue
  strata := strataData
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 5000000 in
theorem zeroCovered (pattern : Fin 26 → Prop)
    (feasible : Feasible pattern)
    (activePattern : ActiveMatches data.active pattern) :
    ∃ stratum ∈ data.strata, ZeroMatches stratum.zero pattern := by
  exact Semantic.zeroCoveredFromGlobal data (by rfl) pattern feasible activePattern

end Krenn.CollapseSupportCover.Mask023
