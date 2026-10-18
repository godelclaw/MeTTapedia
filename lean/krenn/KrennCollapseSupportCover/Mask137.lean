import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask137

def activeValue : BitVec 14 := BitVec.ofNat 14 3586

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 50938302, component := 40 },
    { zero := BitVec.ofNat 26 50938358, component := 24 },
    { zero := BitVec.ofNat 26 55132602, component := 40 },
    { zero := BitVec.ofNat 26 55132658, component := 25 }
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

end Krenn.CollapseSupportCover.Mask137
