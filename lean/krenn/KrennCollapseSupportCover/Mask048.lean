import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask048

def activeValue : BitVec 14 := BitVec.ofNat 14 648

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17030457, component := 51 },
    { zero := BitVec.ofNat 26 50552121, component := 51 },
    { zero := BitVec.ofNat 26 19126585, component := 51 },
    { zero := BitVec.ofNat 26 52648249, component := 51 }
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

end Krenn.CollapseSupportCover.Mask048
