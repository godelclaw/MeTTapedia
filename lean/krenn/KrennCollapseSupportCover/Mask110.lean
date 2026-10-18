import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask110

def activeValue : BitVec 14 := BitVec.ofNat 14 2624

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17023455, component := 26 },
    { zero := BitVec.ofNat 26 50577879, component := 24 },
    { zero := BitVec.ofNat 26 25412061, component := 10 },
    { zero := BitVec.ofNat 26 58966485, component := 3 }
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

end Krenn.CollapseSupportCover.Mask110
