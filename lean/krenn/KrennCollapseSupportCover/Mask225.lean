import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask225

def activeValue : BitVec 14 := BitVec.ofNat 14 5122

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 37292734, component := 22 },
    { zero := BitVec.ofNat 26 37554366, component := 22 },
    { zero := BitVec.ofNat 26 37292790, component := 21 },
    { zero := BitVec.ofNat 26 37554422, component := 21 }
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

end Krenn.CollapseSupportCover.Mask225
