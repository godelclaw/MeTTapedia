import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask160

def activeValue : BitVec 14 := BitVec.ofNat 14 4108

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 37427889, component := 43 },
    { zero := BitVec.ofNat 26 37456561, component := 22 },
    { zero := BitVec.ofNat 26 37689393, component := 43 },
    { zero := BitVec.ofNat 26 37718065, component := 26 },
    { zero := BitVec.ofNat 26 37436080, component := 22 },
    { zero := BitVec.ofNat 26 37464752, component := 22 },
    { zero := BitVec.ofNat 26 37697712, component := 22 },
    { zero := BitVec.ofNat 26 37726384, component := 22 }
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

end Krenn.CollapseSupportCover.Mask160
