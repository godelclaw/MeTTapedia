import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask352

def activeValue : BitVec 14 := BitVec.ofNat 14 14600

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1446265, component := 51 },
    { zero := BitVec.ofNat 26 1970489, component := 51 },
    { zero := BitVec.ofNat 26 1454584, component := 64 },
    { zero := BitVec.ofNat 26 1978808, component := 64 }
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

end Krenn.CollapseSupportCover.Mask352
