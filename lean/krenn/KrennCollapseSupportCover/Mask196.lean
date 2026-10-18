import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask196

def activeValue : BitVec 14 := BitVec.ofNat 14 4616

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 237049, component := 51 },
    { zero := BitVec.ofNat 26 2333177, component := 51 },
    { zero := BitVec.ofNat 26 34282937, component := 51 },
    { zero := BitVec.ofNat 26 757177, component := 34 },
    { zero := BitVec.ofNat 26 36379065, component := 51 },
    { zero := BitVec.ofNat 26 2853305, component := 40 },
    { zero := BitVec.ofNat 26 33758705, component := 26 },
    { zero := BitVec.ofNat 26 34311665, component := 33 },
    { zero := BitVec.ofNat 26 35854833, component := 43 },
    { zero := BitVec.ofNat 26 36407793, component := 22 },
    { zero := BitVec.ofNat 26 245240, component := 64 },
    { zero := BitVec.ofNat 26 2341368, component := 64 },
    { zero := BitVec.ofNat 26 34291128, component := 64 },
    { zero := BitVec.ofNat 26 765368, component := 34 },
    { zero := BitVec.ofNat 26 36387256, component := 64 },
    { zero := BitVec.ofNat 26 2861496, component := 40 },
    { zero := BitVec.ofNat 26 33766896, component := 26 },
    { zero := BitVec.ofNat 26 34319856, component := 33 },
    { zero := BitVec.ofNat 26 35863024, component := 53 },
    { zero := BitVec.ofNat 26 36415984, component := 22 }
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

end Krenn.CollapseSupportCover.Mask196
