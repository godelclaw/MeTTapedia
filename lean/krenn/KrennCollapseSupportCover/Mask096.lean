import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask096

def activeValue : BitVec 14 := BitVec.ofNat 14 2049

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 22540618, component := 59 },
    { zero := BitVec.ofNat 26 56586506, component := 59 },
    { zero := BitVec.ofNat 26 23060746, component := 26 },
    { zero := BitVec.ofNat 26 56062274, component := 57 },
    { zero := BitVec.ofNat 26 56615234, component := 23 },
    { zero := BitVec.ofNat 26 30929224, component := 62 },
    { zero := BitVec.ofNat 26 64975112, component := 56 },
    { zero := BitVec.ofNat 26 31449352, component := 26 },
    { zero := BitVec.ofNat 26 64450880, component := 57 },
    { zero := BitVec.ofNat 26 65003840, component := 23 }
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

end Krenn.CollapseSupportCover.Mask096
