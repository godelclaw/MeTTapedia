import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask248

def activeValue : BitVec 14 := BitVec.ofNat 14 8193

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22429514, component := 59 },
    { zero := BitVec.ofNat 26 32783946, component := 29 },
    { zero := BitVec.ofNat 26 24525386, component := 60 },
    { zero := BitVec.ofNat 26 22953738, component := 59 },
    { zero := BitVec.ofNat 26 33308170, component := 29 },
    { zero := BitVec.ofNat 26 25049610, component := 60 },
    { zero := BitVec.ofNat 26 30687048, component := 26 },
    { zero := BitVec.ofNat 26 32914248, component := 62 },
    { zero := BitVec.ofNat 26 31211272, component := 26 },
    { zero := BitVec.ofNat 26 33438472, component := 65 }
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

end Krenn.CollapseSupportCover.Mask248
