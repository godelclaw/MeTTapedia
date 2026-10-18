import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask265

def activeValue : BitVec 14 := BitVec.ofNat 14 9408

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 28330511, component := 18 },
    { zero := BitVec.ofNat 26 32508431, component := 18 },
    { zero := BitVec.ofNat 26 28330765, component := 9 },
    { zero := BitVec.ofNat 26 32508685, component := 18 }
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

end Krenn.CollapseSupportCover.Mask265
