import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask168

def activeValue : BitVec 14 := BitVec.ofNat 14 4122

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1155040, component := 26 },
    { zero := BitVec.ofNat 26 1675232, component := 33 },
    { zero := BitVec.ofNat 26 1416672, component := 37 },
    { zero := BitVec.ofNat 26 1936864, component := 37 }
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

end Krenn.CollapseSupportCover.Mask168
