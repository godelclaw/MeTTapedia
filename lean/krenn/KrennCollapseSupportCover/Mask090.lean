import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask090

def activeValue : BitVec 14 := BitVec.ofNat 14 1728

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 60901407, component := 2 },
    { zero := BitVec.ofNat 26 65079327, component := 2 },
    { zero := BitVec.ofNat 26 60901661, component := 2 },
    { zero := BitVec.ofNat 26 65079581, component := 2 }
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

end Krenn.CollapseSupportCover.Mask090
