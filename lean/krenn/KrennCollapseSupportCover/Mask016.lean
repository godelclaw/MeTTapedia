import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask016

def activeValue : BitVec 14 := BitVec.ofNat 14 129

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22265610, component := 59 },
    { zero := BitVec.ofNat 26 55787274, component := 59 },
    { zero := BitVec.ofNat 26 32620042, component := 36 },
    { zero := BitVec.ofNat 26 66141706, component := 29 },
    { zero := BitVec.ofNat 26 24361482, component := 60 },
    { zero := BitVec.ofNat 26 57883146, component := 60 },
    { zero := BitVec.ofNat 26 30523144, component := 26 },
    { zero := BitVec.ofNat 26 64044808, component := 26 },
    { zero := BitVec.ofNat 26 32750344, component := 65 },
    { zero := BitVec.ofNat 26 66272008, component := 65 }
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

end Krenn.CollapseSupportCover.Mask016
