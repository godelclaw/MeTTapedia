import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask004

def activeValue : BitVec 14 := BitVec.ofNat 14 5

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 66927616, component := 26 },
    { zero := BitVec.ofNat 26 66956288, component := 26 },
    { zero := BitVec.ofNat 26 67057664, component := 26 },
    { zero := BitVec.ofNat 26 67086336, component := 26 }
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

end Krenn.CollapseSupportCover.Mask004
