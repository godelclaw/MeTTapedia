import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask074

def activeValue : BitVec 14 := BitVec.ofNat 14 1088

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61950663, component := 18 },
    { zero := BitVec.ofNat 26 66128583, component := 18 },
    { zero := BitVec.ofNat 26 62212167, component := 3 },
    { zero := BitVec.ofNat 26 66390087, component := 26 },
    { zero := BitVec.ofNat 26 61950917, component := 18 },
    { zero := BitVec.ofNat 26 66128837, component := 18 },
    { zero := BitVec.ofNat 26 62212421, component := 4 },
    { zero := BitVec.ofNat 26 66390341, component := 17 }
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

end Krenn.CollapseSupportCover.Mask074
