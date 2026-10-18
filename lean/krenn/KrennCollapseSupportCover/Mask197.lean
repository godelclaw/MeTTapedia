import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask197

def activeValue : BitVec 14 := BitVec.ofNat 14 4618

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 105976, component := 35 },
    { zero := BitVec.ofNat 26 34151864, component := 40 },
    { zero := BitVec.ofNat 26 626104, component := 34 },
    { zero := BitVec.ofNat 26 33627632, component := 26 },
    { zero := BitVec.ofNat 26 34180592, component := 33 }
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

end Krenn.CollapseSupportCover.Mask197
