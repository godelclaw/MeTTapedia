import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask358

def activeValue : BitVec 14 := BitVec.ofNat 14 15112

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 135673, component := 51 },
    { zero := BitVec.ofNat 26 659897, component := 51 },
    { zero := BitVec.ofNat 26 143864, component := 64 },
    { zero := BitVec.ofNat 26 668088, component := 64 }
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

end Krenn.CollapseSupportCover.Mask358
