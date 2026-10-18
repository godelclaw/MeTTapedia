import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask038

def activeValue : BitVec 14 := BitVec.ofNat 14 556

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 51076257, component := 25 },
    { zero := BitVec.ofNat 26 51104929, component := 25 },
    { zero := BitVec.ofNat 26 51084448, component := 25 },
    { zero := BitVec.ofNat 26 51113120, component := 25 }
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

end Krenn.CollapseSupportCover.Mask038
