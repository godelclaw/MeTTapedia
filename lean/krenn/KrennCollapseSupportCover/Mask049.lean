import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask049

def activeValue : BitVec 14 := BitVec.ofNat 14 649

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17038616, component := 64 },
    { zero := BitVec.ofNat 26 50560280, component := 64 },
    { zero := BitVec.ofNat 26 19134744, component := 64 },
    { zero := BitVec.ofNat 26 52656408, component := 64 }
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

end Krenn.CollapseSupportCover.Mask049
