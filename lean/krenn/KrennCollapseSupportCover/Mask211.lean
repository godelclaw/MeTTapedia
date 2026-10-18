import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask211

def activeValue : BitVec 14 := BitVec.ofNat 14 4744

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 236857, component := 51 },
    { zero := BitVec.ofNat 26 33758521, component := 51 },
    { zero := BitVec.ofNat 26 2332985, component := 51 },
    { zero := BitVec.ofNat 26 35854649, component := 51 }
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

end Krenn.CollapseSupportCover.Mask211
