import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask284

def activeValue : BitVec 14 := BitVec.ofNat 14 11264

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 26756013, component := 9 },
    { zero := BitVec.ofNat 26 27018029, component := 9 },
    { zero := BitVec.ofNat 26 27026189, component := 9 },
    { zero := BitVec.ofNat 26 30950313, component := 39 },
    { zero := BitVec.ofNat 26 31212329, component := 26 },
    { zero := BitVec.ofNat 26 26764172, component := 12 },
    { zero := BitVec.ofNat 26 30958504, component := 39 }
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

end Krenn.CollapseSupportCover.Mask284
