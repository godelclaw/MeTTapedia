import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask169

def activeValue : BitVec 14 := BitVec.ofNat 14 4124

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 3902113, component := 42 },
    { zero := BitVec.ofNat 26 4163617, component := 26 },
    { zero := BitVec.ofNat 26 3910304, component := 42 },
    { zero := BitVec.ofNat 26 4171936, component := 26 }
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

end Krenn.CollapseSupportCover.Mask169
