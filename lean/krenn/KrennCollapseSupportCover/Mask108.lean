import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask108

def activeValue : BitVec 14 := BitVec.ofNat 14 2596

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 59461797, component := 3 },
    { zero := BitVec.ofNat 26 59490469, component := 3 },
    { zero := BitVec.ofNat 26 63656097, component := 25 },
    { zero := BitVec.ofNat 26 63684769, component := 25 },
    { zero := BitVec.ofNat 26 59469956, component := 6 },
    { zero := BitVec.ofNat 26 59498628, component := 6 },
    { zero := BitVec.ofNat 26 63664288, component := 25 },
    { zero := BitVec.ofNat 26 63692960, component := 25 }
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

end Krenn.CollapseSupportCover.Mask108
