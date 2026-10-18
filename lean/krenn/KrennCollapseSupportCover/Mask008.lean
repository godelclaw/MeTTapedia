import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask008

def activeValue : BitVec 14 := BitVec.ofNat 14 12

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 54221473, component := 52 },
    { zero := BitVec.ofNat 26 54250145, component := 42 },
    { zero := BitVec.ofNat 26 54482977, component := 45 },
    { zero := BitVec.ofNat 26 54511649, component := 26 },
    { zero := BitVec.ofNat 26 54229664, component := 42 },
    { zero := BitVec.ofNat 26 54258336, component := 42 },
    { zero := BitVec.ofNat 26 54491296, component := 25 },
    { zero := BitVec.ofNat 26 54519968, component := 25 }
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

end Krenn.CollapseSupportCover.Mask008
