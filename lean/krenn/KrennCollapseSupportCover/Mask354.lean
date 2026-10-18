import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask354

def activeValue : BitVec 14 := BitVec.ofNat 14 14608

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1446247, component := 49 },
    { zero := BitVec.ofNat 26 1454407, component := 62 },
    { zero := BitVec.ofNat 26 9834853, component := 49 },
    { zero := BitVec.ofNat 26 9843013, component := 62 },
    { zero := BitVec.ofNat 26 1454534, component := 62 },
    { zero := BitVec.ofNat 26 9843140, component := 62 }
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

end Krenn.CollapseSupportCover.Mask354
