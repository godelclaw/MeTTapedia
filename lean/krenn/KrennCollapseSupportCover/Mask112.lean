import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask112

def activeValue : BitVec 14 := BitVec.ofNat 14 2688

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17027391, component := 51 },
    { zero := BitVec.ofNat 26 50549055, component := 51 },
    { zero := BitVec.ofNat 26 17035551, component := 64 },
    { zero := BitVec.ofNat 26 50557215, component := 64 },
    { zero := BitVec.ofNat 26 21221691, component := 51 },
    { zero := BitVec.ofNat 26 54743355, component := 51 },
    { zero := BitVec.ofNat 26 25415997, component := 51 },
    { zero := BitVec.ofNat 26 58937661, component := 51 },
    { zero := BitVec.ofNat 26 25424157, component := 64 },
    { zero := BitVec.ofNat 26 58945821, component := 64 },
    { zero := BitVec.ofNat 26 29610297, component := 51 },
    { zero := BitVec.ofNat 26 63131961, component := 51 }
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

end Krenn.CollapseSupportCover.Mask112
