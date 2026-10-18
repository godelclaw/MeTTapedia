import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask098

def activeValue : BitVec 14 := BitVec.ofNat 14 2057

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18346312, component := 62 },
    { zero := BitVec.ofNat 26 52392200, component := 56 },
    { zero := BitVec.ofNat 26 18866440, component := 26 },
    { zero := BitVec.ofNat 26 51867968, component := 57 },
    { zero := BitVec.ofNat 26 52420928, component := 23 }
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

end Krenn.CollapseSupportCover.Mask098
