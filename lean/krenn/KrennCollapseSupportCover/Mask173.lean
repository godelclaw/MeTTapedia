import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask173

def activeValue : BitVec 14 := BitVec.ofNat 14 4162

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1150942, component := 38 },
    { zero := BitVec.ofNat 26 1412574, component := 38 },
    { zero := BitVec.ofNat 26 3247838, component := 38 },
    { zero := BitVec.ofNat 26 3509470, component := 38 },
    { zero := BitVec.ofNat 26 34705366, component := 38 },
    { zero := BitVec.ofNat 26 34966998, component := 38 },
    { zero := BitVec.ofNat 26 36802262, component := 38 },
    { zero := BitVec.ofNat 26 37063894, component := 38 }
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

end Krenn.CollapseSupportCover.Mask173
