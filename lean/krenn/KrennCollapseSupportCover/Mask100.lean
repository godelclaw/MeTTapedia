import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask100

def activeValue : BitVec 14 := BitVec.ofNat 14 2176

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18076463, component := 50 },
    { zero := BitVec.ofNat 26 51598127, component := 50 },
    { zero := BitVec.ofNat 26 18084623, component := 63 },
    { zero := BitVec.ofNat 26 51606287, component := 63 },
    { zero := BitVec.ofNat 26 22270763, component := 50 },
    { zero := BitVec.ofNat 26 55792427, component := 50 },
    { zero := BitVec.ofNat 26 26465069, component := 50 },
    { zero := BitVec.ofNat 26 59986733, component := 50 },
    { zero := BitVec.ofNat 26 26473229, component := 63 },
    { zero := BitVec.ofNat 26 59994893, component := 63 },
    { zero := BitVec.ofNat 26 30659369, component := 50 },
    { zero := BitVec.ofNat 26 64181033, component := 50 }
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

end Krenn.CollapseSupportCover.Mask100
