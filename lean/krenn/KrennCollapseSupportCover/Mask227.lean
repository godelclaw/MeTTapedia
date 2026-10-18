import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask227

def activeValue : BitVec 14 := BitVec.ofNat 14 5130

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 37292984, component := 22 },
    { zero := BitVec.ofNat 26 37554616, component := 22 },
    { zero := BitVec.ofNat 26 37293040, component := 22 },
    { zero := BitVec.ofNat 26 37554672, component := 22 }
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

end Krenn.CollapseSupportCover.Mask227
