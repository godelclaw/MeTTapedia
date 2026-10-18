import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask054

def activeValue : BitVec 14 := BitVec.ofNat 14 676

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 58809381, component := 3 },
    { zero := BitVec.ofNat 26 58817541, component := 3 },
    { zero := BitVec.ofNat 26 62995461, component := 26 },
    { zero := BitVec.ofNat 26 62987297, component := 26 }
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

end Krenn.CollapseSupportCover.Mask054
