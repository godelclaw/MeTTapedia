import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask043

def activeValue : BitVec 14 := BitVec.ofNat 14 610

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 16895182, component := 38 },
    { zero := BitVec.ofNat 26 21073102, component := 38 },
    { zero := BitVec.ofNat 26 50449606, component := 38 },
    { zero := BitVec.ofNat 26 54627526, component := 38 }
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

end Krenn.CollapseSupportCover.Mask043
