import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask194

def activeValue : BitVec 14 := BitVec.ofNat 14 4610

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 105982, component := 38 },
    { zero := BitVec.ofNat 26 2202878, component := 38 },
    { zero := BitVec.ofNat 26 34151870, component := 40 },
    { zero := BitVec.ofNat 26 626110, component := 34 },
    { zero := BitVec.ofNat 26 36248766, component := 22 },
    { zero := BitVec.ofNat 26 2723006, component := 33 },
    { zero := BitVec.ofNat 26 33627638, component := 26 },
    { zero := BitVec.ofNat 26 34180598, component := 38 },
    { zero := BitVec.ofNat 26 35724534, component := 21 },
    { zero := BitVec.ofNat 26 36277494, component := 38 }
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

end Krenn.CollapseSupportCover.Mask194
