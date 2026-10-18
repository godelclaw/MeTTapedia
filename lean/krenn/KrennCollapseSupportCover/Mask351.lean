import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask351

def activeValue : BitVec 14 := BitVec.ofNat 14 14592

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1446271, component := 51 },
    { zero := BitVec.ofNat 26 1970495, component := 51 },
    { zero := BitVec.ofNat 26 1454431, component := 64 },
    { zero := BitVec.ofNat 26 1978655, component := 64 },
    { zero := BitVec.ofNat 26 9834877, component := 51 },
    { zero := BitVec.ofNat 26 10359101, component := 51 },
    { zero := BitVec.ofNat 26 9843037, component := 64 },
    { zero := BitVec.ofNat 26 10367261, component := 64 },
    { zero := BitVec.ofNat 26 1454558, component := 64 },
    { zero := BitVec.ofNat 26 1978782, component := 64 },
    { zero := BitVec.ofNat 26 9843164, component := 64 },
    { zero := BitVec.ofNat 26 10367388, component := 64 }
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

end Krenn.CollapseSupportCover.Mask351
