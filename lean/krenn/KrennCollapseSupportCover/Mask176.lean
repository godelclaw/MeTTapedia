import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask176

def activeValue : BitVec 14 := BitVec.ofNat 14 4178

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1150918, component := 38 },
    { zero := BitVec.ofNat 26 1412550, component := 38 },
    { zero := BitVec.ofNat 26 3247814, component := 38 },
    { zero := BitVec.ofNat 26 3509446, component := 38 }
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

end Krenn.CollapseSupportCover.Mask176
