import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask013

def activeValue : BitVec 14 := BitVec.ofNat 14 67

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22383946, component := 36 },
    { zero := BitVec.ofNat 26 24480842, component := 36 },
    { zero := BitVec.ofNat 26 55938370, component := 37 },
    { zero := BitVec.ofNat 26 58035266, component := 26 }
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

end Krenn.CollapseSupportCover.Mask013
