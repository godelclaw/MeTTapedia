import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask210

def activeValue : BitVec 14 := BitVec.ofNat 14 4740

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 44112949, component := 2 },
    { zero := BitVec.ofNat 26 44242997, component := 2 },
    { zero := BitVec.ofNat 26 44121109, component := 2 },
    { zero := BitVec.ofNat 26 44251157, component := 2 }
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

end Krenn.CollapseSupportCover.Mask210
