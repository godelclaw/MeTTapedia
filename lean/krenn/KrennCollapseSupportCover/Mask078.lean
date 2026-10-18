import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask078

def activeValue : BitVec 14 := BitVec.ofNat 14 1216

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61950479, component := 18 },
    { zero := BitVec.ofNat 26 66128399, component := 18 },
    { zero := BitVec.ofNat 26 61950733, component := 9 },
    { zero := BitVec.ofNat 26 66128653, component := 18 }
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

end Krenn.CollapseSupportCover.Mask078
