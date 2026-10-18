import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask128

def activeValue : BitVec 14 := BitVec.ofNat 14 3082

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 51987368, component := 39 },
    { zero := BitVec.ofNat 26 52249000, component := 25 },
    { zero := BitVec.ofNat 26 51987424, component := 25 },
    { zero := BitVec.ofNat 26 52249056, component := 25 }
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

end Krenn.CollapseSupportCover.Mask128
