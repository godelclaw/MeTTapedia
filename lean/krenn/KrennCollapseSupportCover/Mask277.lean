import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask277

def activeValue : BitVec 14 := BitVec.ofNat 14 10497

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22425930, component := 59 },
    { zero := BitVec.ofNat 26 22950154, component := 59 },
    { zero := BitVec.ofNat 26 30814536, component := 62 },
    { zero := BitVec.ofNat 26 31338760, component := 26 }
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

end Krenn.CollapseSupportCover.Mask277
