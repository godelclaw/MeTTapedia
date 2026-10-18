import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask136

def activeValue : BitVec 14 := BitVec.ofNat 14 3584

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 59326909, component := 10 },
    { zero := BitVec.ofNat 26 59326965, component := 3 },
    { zero := BitVec.ofNat 26 63521209, component := 40 },
    { zero := BitVec.ofNat 26 63521265, component := 25 },
    { zero := BitVec.ofNat 26 59335068, component := 6 },
    { zero := BitVec.ofNat 26 59335124, component := 6 },
    { zero := BitVec.ofNat 26 63529400, component := 40 },
    { zero := BitVec.ofNat 26 63529456, component := 25 }
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

end Krenn.CollapseSupportCover.Mask136
