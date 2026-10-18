import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask052

def activeValue : BitVec 14 := BitVec.ofNat 14 672

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17030191, component := 26 },
    { zero := BitVec.ofNat 26 25287727, component := 15 },
    { zero := BitVec.ofNat 26 50551855, component := 45 },
    { zero := BitVec.ofNat 26 58809391, component := 3 },
    { zero := BitVec.ofNat 26 17038351, component := 26 },
    { zero := BitVec.ofNat 26 25295887, component := 15 },
    { zero := BitVec.ofNat 26 50560015, component := 56 },
    { zero := BitVec.ofNat 26 58817551, component := 3 },
    { zero := BitVec.ofNat 26 21216271, component := 59 },
    { zero := BitVec.ofNat 26 29473807, component := 36 },
    { zero := BitVec.ofNat 26 54737935, component := 59 },
    { zero := BitVec.ofNat 26 62995471, component := 26 },
    { zero := BitVec.ofNat 26 21208107, component := 47 },
    { zero := BitVec.ofNat 26 29465643, component := 36 },
    { zero := BitVec.ofNat 26 54729771, component := 47 },
    { zero := BitVec.ofNat 26 62987307, component := 26 }
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

end Krenn.CollapseSupportCover.Mask052
