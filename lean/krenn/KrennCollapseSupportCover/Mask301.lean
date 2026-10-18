import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask301

def activeValue : BitVec 14 := BitVec.ofNat 14 12032

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 29884857, component := 40 },
    { zero := BitVec.ofNat 26 29893020, component := 13 },
    { zero := BitVec.ofNat 26 29893048, component := 40 }
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

end Krenn.CollapseSupportCover.Mask301
