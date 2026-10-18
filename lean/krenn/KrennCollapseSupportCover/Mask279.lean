import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask279

def activeValue : BitVec 14 := BitVec.ofNat 14 11040

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 21106923, component := 47 },
    { zero := BitVec.ofNat 26 21631147, component := 47 },
    { zero := BitVec.ofNat 26 21115086, component := 59 },
    { zero := BitVec.ofNat 26 21639310, component := 59 },
    { zero := BitVec.ofNat 26 21115114, component := 59 },
    { zero := BitVec.ofNat 26 21639338, component := 59 }
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

end Krenn.CollapseSupportCover.Mask279
