import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask116

def activeValue : BitVec 14 := BitVec.ofNat 14 2720

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17027119, component := 26 },
    { zero := BitVec.ofNat 26 50548783, component := 45 },
    { zero := BitVec.ofNat 26 17035279, component := 26 },
    { zero := BitVec.ofNat 26 50556943, component := 56 },
    { zero := BitVec.ofNat 26 21221419, component := 47 },
    { zero := BitVec.ofNat 26 54743083, component := 47 }
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

end Krenn.CollapseSupportCover.Mask116
