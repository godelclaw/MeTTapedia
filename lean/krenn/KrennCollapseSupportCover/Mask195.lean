import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask195

def activeValue : BitVec 14 := BitVec.ofNat 14 4612

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 44637365, component := 2 },
    { zero := BitVec.ofNat 26 44666037, component := 2 },
    { zero := BitVec.ofNat 26 44767413, component := 2 },
    { zero := BitVec.ofNat 26 44796085, component := 2 },
    { zero := BitVec.ofNat 26 44645524, component := 5 },
    { zero := BitVec.ofNat 26 44674196, component := 5 },
    { zero := BitVec.ofNat 26 44775572, component := 5 },
    { zero := BitVec.ofNat 26 44804244, component := 5 }
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

end Krenn.CollapseSupportCover.Mask195
