import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask344

def activeValue : BitVec 14 := BitVec.ofNat 14 13392

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 11537095, component := 18 },
    { zero := BitVec.ofNat 26 11799111, component := 18 },
    { zero := BitVec.ofNat 26 11537349, component := 18 },
    { zero := BitVec.ofNat 26 11799365, component := 18 }
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

end Krenn.CollapseSupportCover.Mask344
