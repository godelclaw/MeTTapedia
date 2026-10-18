import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask187

def activeValue : BitVec 14 := BitVec.ofNat 14 4288

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1281823, component := 35 },
    { zero := BitVec.ofNat 26 11636255, component := 18 },
    { zero := BitVec.ofNat 26 3377695, component := 26 },
    { zero := BitVec.ofNat 26 9539357, component := 11 },
    { zero := BitVec.ofNat 26 11766557, component := 18 }
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

end Krenn.CollapseSupportCover.Mask187
