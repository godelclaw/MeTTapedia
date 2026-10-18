import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask025

def activeValue : BitVec 14 := BitVec.ofNat 14 196

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61984261, component := 18 },
    { zero := BitVec.ofNat 26 66162181, component := 18 },
    { zero := BitVec.ofNat 26 62114309, component := 18 },
    { zero := BitVec.ofNat 26 66292229, component := 18 }
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

end Krenn.CollapseSupportCover.Mask025
