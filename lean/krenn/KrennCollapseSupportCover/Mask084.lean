import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask084

def activeValue : BitVec 14 := BitVec.ofNat 14 1538

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 53037246, component := 22 },
    { zero := BitVec.ofNat 26 53037302, component := 21 },
    { zero := BitVec.ofNat 26 57215162, component := 22 },
    { zero := BitVec.ofNat 26 57215218, component := 22 }
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

end Krenn.CollapseSupportCover.Mask084
