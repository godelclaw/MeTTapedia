import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask140

def activeValue : BitVec 14 := BitVec.ofNat 14 3618

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 50938030, component := 25 },
    { zero := BitVec.ofNat 26 50938086, component := 24 },
    { zero := BitVec.ofNat 26 55132330, component := 25 },
    { zero := BitVec.ofNat 26 55132386, component := 25 }
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

end Krenn.CollapseSupportCover.Mask140
