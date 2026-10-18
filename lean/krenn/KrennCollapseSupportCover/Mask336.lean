import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask336

def activeValue : BitVec 14 := BitVec.ofNat 14 13328

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 12061415, component := 18 },
    { zero := BitVec.ofNat 26 12323431, component := 18 },
    { zero := BitVec.ofNat 26 12331591, component := 18 },
    { zero := BitVec.ofNat 26 12061669, component := 18 },
    { zero := BitVec.ofNat 26 12323685, component := 18 },
    { zero := BitVec.ofNat 26 12331845, component := 18 },
    { zero := BitVec.ofNat 26 12069574, component := 20 },
    { zero := BitVec.ofNat 26 12069828, component := 20 }
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

end Krenn.CollapseSupportCover.Mask336
