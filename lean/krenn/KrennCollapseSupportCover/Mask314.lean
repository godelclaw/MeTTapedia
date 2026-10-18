import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask314

def activeValue : BitVec 14 := BitVec.ofNat 14 12290

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1056766, component := 26 },
    { zero := BitVec.ofNat 26 3153662, component := 41 },
    { zero := BitVec.ofNat 26 1580990, component := 40 },
    { zero := BitVec.ofNat 26 3677886, component := 42 }
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

end Krenn.CollapseSupportCover.Mask314
