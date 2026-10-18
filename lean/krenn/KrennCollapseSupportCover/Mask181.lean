import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask181

def activeValue : BitVec 14 := BitVec.ofNat 14 4233

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1294104, component := 64 },
    { zero := BitVec.ofNat 26 34815768, component := 64 },
    { zero := BitVec.ofNat 26 3390232, component := 64 },
    { zero := BitVec.ofNat 26 36911896, component := 64 }
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

end Krenn.CollapseSupportCover.Mask181
