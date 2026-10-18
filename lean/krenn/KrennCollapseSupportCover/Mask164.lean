import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask164

def activeValue : BitVec 14 := BitVec.ofNat 14 4114

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1155046, component := 38 },
    { zero := BitVec.ofNat 26 1675238, component := 38 },
    { zero := BitVec.ofNat 26 1416678, component := 38 },
    { zero := BitVec.ofNat 26 1936870, component := 38 },
    { zero := BitVec.ofNat 26 3251942, component := 38 },
    { zero := BitVec.ofNat 26 3772134, component := 38 },
    { zero := BitVec.ofNat 26 3513574, component := 38 },
    { zero := BitVec.ofNat 26 4033766, component := 38 }
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

end Krenn.CollapseSupportCover.Mask164
