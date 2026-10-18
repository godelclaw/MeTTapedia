import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask206

def activeValue : BitVec 14 := BitVec.ofNat 14 4674

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 101854, component := 38 },
    { zero := BitVec.ofNat 26 2198750, component := 38 },
    { zero := BitVec.ofNat 26 33656278, component := 38 },
    { zero := BitVec.ofNat 26 35753174, component := 38 }
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

end Krenn.CollapseSupportCover.Mask206
