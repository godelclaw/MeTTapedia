import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask030

def activeValue : BitVec 14 := BitVec.ofNat 14 516

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 61430965, component := 2 },
    { zero := BitVec.ofNat 26 61459637, component := 2 },
    { zero := BitVec.ofNat 26 61561013, component := 2 },
    { zero := BitVec.ofNat 26 61589685, component := 2 },
    { zero := BitVec.ofNat 26 65608881, component := 22 },
    { zero := BitVec.ofNat 26 65637553, component := 22 },
    { zero := BitVec.ofNat 26 65738929, component := 43 },
    { zero := BitVec.ofNat 26 65767601, component := 22 },
    { zero := BitVec.ofNat 26 61439124, component := 5 },
    { zero := BitVec.ofNat 26 65617044, component := 5 },
    { zero := BitVec.ofNat 26 61467796, component := 5 },
    { zero := BitVec.ofNat 26 65645716, component := 5 },
    { zero := BitVec.ofNat 26 61569172, component := 5 },
    { zero := BitVec.ofNat 26 65747092, component := 5 },
    { zero := BitVec.ofNat 26 61597844, component := 5 },
    { zero := BitVec.ofNat 26 65775764, component := 5 },
    { zero := BitVec.ofNat 26 65617072, component := 22 },
    { zero := BitVec.ofNat 26 65645744, component := 22 },
    { zero := BitVec.ofNat 26 65747120, component := 22 },
    { zero := BitVec.ofNat 26 65775792, component := 22 }
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

end Krenn.CollapseSupportCover.Mask030
