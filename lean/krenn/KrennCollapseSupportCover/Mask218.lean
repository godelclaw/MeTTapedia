import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask218

def activeValue : BitVec 14 := BitVec.ofNat 14 4800

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 232735, component := 35 },
    { zero := BitVec.ofNat 26 10587167, component := 15 },
    { zero := BitVec.ofNat 26 2328607, component := 26 },
    { zero := BitVec.ofNat 26 8490269, component := 11 },
    { zero := BitVec.ofNat 26 10717469, component := 10 }
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

end Krenn.CollapseSupportCover.Mask218
