import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask200

def activeValue : BitVec 14 := BitVec.ofNat 14 4656

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 236775, component := 38 },
    { zero := BitVec.ofNat 26 8494311, component := 38 },
    { zero := BitVec.ofNat 26 756967, component := 38 },
    { zero := BitVec.ofNat 26 9014503, component := 38 },
    { zero := BitVec.ofNat 26 244934, component := 38 },
    { zero := BitVec.ofNat 26 8502470, component := 38 },
    { zero := BitVec.ofNat 26 765126, component := 38 },
    { zero := BitVec.ofNat 26 9022662, component := 38 }
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

end Krenn.CollapseSupportCover.Mask200
