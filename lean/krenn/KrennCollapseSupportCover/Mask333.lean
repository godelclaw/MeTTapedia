import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask333

def activeValue : BitVec 14 := BitVec.ofNat 14 13312

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 12061375, component := 18 },
    { zero := BitVec.ofNat 26 12323391, component := 18 },
    { zero := BitVec.ofNat 26 12331551, component := 18 },
    { zero := BitVec.ofNat 26 12061629, component := 18 },
    { zero := BitVec.ofNat 26 12323645, component := 18 },
    { zero := BitVec.ofNat 26 12331805, component := 18 },
    { zero := BitVec.ofNat 26 12069534, component := 20 },
    { zero := BitVec.ofNat 26 12069788, component := 20 }
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

end Krenn.CollapseSupportCover.Mask333
