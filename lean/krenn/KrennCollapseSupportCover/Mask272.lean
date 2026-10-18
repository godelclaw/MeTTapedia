import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask272

def activeValue : BitVec 14 := BitVec.ofNat 14 10368

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17978159, component := 50 },
    { zero := BitVec.ofNat 26 17986319, component := 63 },
    { zero := BitVec.ofNat 26 22172459, component := 50 },
    { zero := BitVec.ofNat 26 26366765, component := 50 },
    { zero := BitVec.ofNat 26 26374925, component := 63 },
    { zero := BitVec.ofNat 26 30561065, component := 50 }
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

end Krenn.CollapseSupportCover.Mask272
