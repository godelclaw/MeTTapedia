import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask226

def activeValue : BitVec 14 := BitVec.ofNat 14 5124

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 45681333, component := 2 },
    { zero := BitVec.ofNat 26 45942837, component := 2 },
    { zero := BitVec.ofNat 26 45950997, component := 2 },
    { zero := BitVec.ofNat 26 45689492, component := 5 },
    { zero := BitVec.ofNat 26 45951124, component := 5 }
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

end Krenn.CollapseSupportCover.Mask226
