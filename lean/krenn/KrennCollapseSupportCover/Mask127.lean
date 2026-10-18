import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask127

def activeValue : BitVec 14 := BitVec.ofNat 14 3074

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 51987374, component := 39 },
    { zero := BitVec.ofNat 26 52249006, component := 25 },
    { zero := BitVec.ofNat 26 51987430, component := 24 },
    { zero := BitVec.ofNat 26 52249062, component := 24 },
    { zero := BitVec.ofNat 26 56181674, component := 39 },
    { zero := BitVec.ofNat 26 56443306, component := 25 },
    { zero := BitVec.ofNat 26 56181730, component := 25 },
    { zero := BitVec.ofNat 26 56443362, component := 25 }
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

end Krenn.CollapseSupportCover.Mask127
