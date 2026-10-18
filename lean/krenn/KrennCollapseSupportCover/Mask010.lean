import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask010

def activeValue : BitVec 14 := BitVec.ofNat 14 14

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 54091424, component := 42 },
    { zero := BitVec.ofNat 26 54120096, component := 42 },
    { zero := BitVec.ofNat 26 54353056, component := 25 },
    { zero := BitVec.ofNat 26 54381728, component := 25 }
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

end Krenn.CollapseSupportCover.Mask010
