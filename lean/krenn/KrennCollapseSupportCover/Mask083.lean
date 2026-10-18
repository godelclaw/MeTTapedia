import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask083

def activeValue : BitVec 14 := BitVec.ofNat 14 1536

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61425855, component := 2 },
    { zero := BitVec.ofNat 26 61425911, component := 2 },
    { zero := BitVec.ofNat 26 65603771, component := 22 },
    { zero := BitVec.ofNat 26 65603827, component := 22 },
    { zero := BitVec.ofNat 26 61426109, component := 2 },
    { zero := BitVec.ofNat 26 61426165, component := 2 },
    { zero := BitVec.ofNat 26 65604025, component := 22 },
    { zero := BitVec.ofNat 26 65604081, component := 22 },
    { zero := BitVec.ofNat 26 61434014, component := 5 },
    { zero := BitVec.ofNat 26 65611934, component := 5 },
    { zero := BitVec.ofNat 26 61434070, component := 5 },
    { zero := BitVec.ofNat 26 65611990, component := 5 },
    { zero := BitVec.ofNat 26 65611962, component := 22 },
    { zero := BitVec.ofNat 26 65612018, component := 22 },
    { zero := BitVec.ofNat 26 61434268, component := 5 },
    { zero := BitVec.ofNat 26 65612188, component := 5 },
    { zero := BitVec.ofNat 26 61434324, component := 5 },
    { zero := BitVec.ofNat 26 65612244, component := 5 },
    { zero := BitVec.ofNat 26 65612216, component := 22 },
    { zero := BitVec.ofNat 26 65612272, component := 22 }
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

end Krenn.CollapseSupportCover.Mask083
