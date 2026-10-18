import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask033

def activeValue : BitVec 14 := BitVec.ofNat 14 524

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 53172401, component := 43 },
    { zero := BitVec.ofNat 26 53201073, component := 22 },
    { zero := BitVec.ofNat 26 53180592, component := 22 },
    { zero := BitVec.ofNat 26 53209264, component := 22 }
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

end Krenn.CollapseSupportCover.Mask033
