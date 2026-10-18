import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask315

def activeValue : BitVec 14 := BitVec.ofNat 14 12296

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1187833, component := 51 },
    { zero := BitVec.ofNat 26 3283961, component := 51 },
    { zero := BitVec.ofNat 26 1449849, component := 51 },
    { zero := BitVec.ofNat 26 3545977, component := 51 },
    { zero := BitVec.ofNat 26 1712057, component := 51 },
    { zero := BitVec.ofNat 26 3808185, component := 51 },
    { zero := BitVec.ofNat 26 1974073, component := 51 },
    { zero := BitVec.ofNat 26 4070201, component := 51 },
    { zero := BitVec.ofNat 26 1196024, component := 64 },
    { zero := BitVec.ofNat 26 3292152, component := 64 },
    { zero := BitVec.ofNat 26 1720248, component := 64 },
    { zero := BitVec.ofNat 26 3816376, component := 64 }
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

end Krenn.CollapseSupportCover.Mask315
