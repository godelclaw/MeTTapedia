import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask085

def activeValue : BitVec 14 := BitVec.ofNat 14 1540

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61425845, component := 2 },
    { zero := BitVec.ofNat 26 65603761, component := 22 },
    { zero := BitVec.ofNat 26 61434004, component := 5 },
    { zero := BitVec.ofNat 26 65611924, component := 5 },
    { zero := BitVec.ofNat 26 65611952, component := 22 }
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

end Krenn.CollapseSupportCover.Mask085
