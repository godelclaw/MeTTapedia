import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask017

def activeValue : BitVec 14 := BitVec.ofNat 14 132

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61955621, component := 18 },
    { zero := BitVec.ofNat 26 62085669, component := 18 },
    { zero := BitVec.ofNat 26 61963781, component := 18 },
    { zero := BitVec.ofNat 26 66141701, component := 18 },
    { zero := BitVec.ofNat 26 62093829, component := 18 },
    { zero := BitVec.ofNat 26 66271749, component := 18 },
    { zero := BitVec.ofNat 26 66133537, component := 26 },
    { zero := BitVec.ofNat 26 66263585, component := 52 }
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

end Krenn.CollapseSupportCover.Mask017
