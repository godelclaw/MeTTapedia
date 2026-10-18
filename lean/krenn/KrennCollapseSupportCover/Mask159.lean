import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask159

def activeValue : BitVec 14 := BitVec.ofNat 14 4106

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1155064, component := 35 },
    { zero := BitVec.ofNat 26 1416696, component := 37 },
    { zero := BitVec.ofNat 26 35200952, component := 40 },
    { zero := BitVec.ofNat 26 1675192, component := 34 },
    { zero := BitVec.ofNat 26 35462584, component := 40 },
    { zero := BitVec.ofNat 26 1936824, component := 34 },
    { zero := BitVec.ofNat 26 34676720, component := 26 },
    { zero := BitVec.ofNat 26 35229680, component := 33 },
    { zero := BitVec.ofNat 26 34938352, component := 26 },
    { zero := BitVec.ofNat 26 35491312, component := 37 }
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

end Krenn.CollapseSupportCover.Mask159
