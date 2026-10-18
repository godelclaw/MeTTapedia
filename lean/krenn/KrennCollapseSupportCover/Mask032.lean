import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask032

def activeValue : BitVec 14 := BitVec.ofNat 14 522

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 16899576, component := 35 },
    { zero := BitVec.ofNat 26 50945464, component := 40 },
    { zero := BitVec.ofNat 26 17419704, component := 34 },
    { zero := BitVec.ofNat 26 50421232, component := 26 },
    { zero := BitVec.ofNat 26 50974192, component := 25 }
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

end Krenn.CollapseSupportCover.Mask032
