import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask069

def activeValue : BitVec 14 := BitVec.ofNat 14 1026

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 54086318, component := 42 },
    { zero := BitVec.ofNat 26 54347950, component := 25 },
    { zero := BitVec.ofNat 26 54086374, component := 24 },
    { zero := BitVec.ofNat 26 54348006, component := 24 },
    { zero := BitVec.ofNat 26 58264234, component := 30 },
    { zero := BitVec.ofNat 26 58525866, component := 31 },
    { zero := BitVec.ofNat 26 58264290, component := 42 },
    { zero := BitVec.ofNat 26 58525922, component := 26 }
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

end Krenn.CollapseSupportCover.Mask069
