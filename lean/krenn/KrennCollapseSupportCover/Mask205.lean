import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask205

def activeValue : BitVec 14 := BitVec.ofNat 14 4672

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 232927, component := 38 },
    { zero := BitVec.ofNat 26 10587359, component := 38 },
    { zero := BitVec.ofNat 26 2328799, component := 26 },
    { zero := BitVec.ofNat 26 33787351, component := 38 },
    { zero := BitVec.ofNat 26 44141783, component := 38 },
    { zero := BitVec.ofNat 26 35883223, component := 21 },
    { zero := BitVec.ofNat 26 8490461, component := 11 },
    { zero := BitVec.ofNat 26 10717661, component := 10 },
    { zero := BitVec.ofNat 26 42044885, component := 15 },
    { zero := BitVec.ofNat 26 44272085, component := 2 }
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

end Krenn.CollapseSupportCover.Mask205
