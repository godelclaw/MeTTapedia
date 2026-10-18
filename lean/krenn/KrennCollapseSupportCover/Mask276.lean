import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask276

def activeValue : BitVec 14 := BitVec.ofNat 14 10496

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22425935, component := 59 },
    { zero := BitVec.ofNat 26 22950159, component := 59 },
    { zero := BitVec.ofNat 26 22417771, component := 47 },
    { zero := BitVec.ofNat 26 22941995, component := 47 },
    { zero := BitVec.ofNat 26 30814541, component := 62 },
    { zero := BitVec.ofNat 26 31338765, component := 26 },
    { zero := BitVec.ofNat 26 30806377, component := 49 },
    { zero := BitVec.ofNat 26 31330601, component := 26 },
    { zero := BitVec.ofNat 26 22426062, component := 59 },
    { zero := BitVec.ofNat 26 22950286, component := 59 },
    { zero := BitVec.ofNat 26 22426090, component := 59 },
    { zero := BitVec.ofNat 26 22950314, component := 59 },
    { zero := BitVec.ofNat 26 30814668, component := 62 },
    { zero := BitVec.ofNat 26 31338892, component := 26 },
    { zero := BitVec.ofNat 26 30814696, component := 62 },
    { zero := BitVec.ofNat 26 31338920, component := 26 }
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

end Krenn.CollapseSupportCover.Mask276
