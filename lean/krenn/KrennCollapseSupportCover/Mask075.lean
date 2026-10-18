import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask075

def activeValue : BitVec 14 := BitVec.ofNat 14 1090

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 53562054, component := 24 },
    { zero := BitVec.ofNat 26 57739974, component := 41 },
    { zero := BitVec.ofNat 26 53823686, component := 24 },
    { zero := BitVec.ofNat 26 58001606, component := 26 }
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

end Krenn.CollapseSupportCover.Mask075
