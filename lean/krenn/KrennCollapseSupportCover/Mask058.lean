import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask058

def activeValue : BitVec 14 := BitVec.ofNat 14 704

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17026335, component := 35 },
    { zero := BitVec.ofNat 26 21204255, component := 36 },
    { zero := BitVec.ofNat 26 27380767, component := 15 },
    { zero := BitVec.ofNat 26 31558687, component := 36 },
    { zero := BitVec.ofNat 26 19122207, component := 26 },
    { zero := BitVec.ofNat 26 23300127, component := 26 },
    { zero := BitVec.ofNat 26 25283869, component := 11 },
    { zero := BitVec.ofNat 26 29461789, component := 11 },
    { zero := BitVec.ofNat 26 27511069, component := 10 },
    { zero := BitVec.ofNat 26 31688989, component := 10 }
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

end Krenn.CollapseSupportCover.Mask058
