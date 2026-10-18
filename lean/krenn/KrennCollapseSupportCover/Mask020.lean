import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask020

def activeValue : BitVec 14 := BitVec.ofNat 14 137

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18087688, component := 63 },
    { zero := BitVec.ofNat 26 51609352, component := 63 },
    { zero := BitVec.ofNat 26 20183816, component := 63 },
    { zero := BitVec.ofNat 26 53705480, component := 63 }
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

end Krenn.CollapseSupportCover.Mask020
