import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask113

def activeValue : BitVec 14 := BitVec.ofNat 14 2689

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 21229850, component := 64 },
    { zero := BitVec.ofNat 26 54751514, component := 64 },
    { zero := BitVec.ofNat 26 29618456, component := 64 },
    { zero := BitVec.ofNat 26 63140120, component := 64 }
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

end Krenn.CollapseSupportCover.Mask113
