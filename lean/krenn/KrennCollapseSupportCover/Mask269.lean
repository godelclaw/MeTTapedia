import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask269

def activeValue : BitVec 14 := BitVec.ofNat 14 10241

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22442826, component := 63 },
    { zero := BitVec.ofNat 26 22967050, component := 63 },
    { zero := BitVec.ofNat 26 30831432, component := 63 },
    { zero := BitVec.ofNat 26 31355656, component := 63 }
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

end Krenn.CollapseSupportCover.Mask269
