import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask198

def activeValue : BitVec 14 := BitVec.ofNat 14 4620

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 36378801, component := 43 },
    { zero := BitVec.ofNat 26 36407473, component := 22 },
    { zero := BitVec.ofNat 26 36386992, component := 22 },
    { zero := BitVec.ofNat 26 36415664, component := 22 }
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

end Krenn.CollapseSupportCover.Mask198
