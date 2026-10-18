import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask106

def activeValue : BitVec 14 := BitVec.ofNat 14 2568

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17027577, component := 51 },
    { zero := BitVec.ofNat 26 51073465, component := 51 },
    { zero := BitVec.ofNat 26 17547705, component := 40 },
    { zero := BitVec.ofNat 26 50549233, component := 45 },
    { zero := BitVec.ofNat 26 51102193, component := 25 },
    { zero := BitVec.ofNat 26 17035768, component := 64 },
    { zero := BitVec.ofNat 26 51081656, component := 64 },
    { zero := BitVec.ofNat 26 17555896, component := 40 },
    { zero := BitVec.ofNat 26 50557424, component := 56 },
    { zero := BitVec.ofNat 26 51110384, component := 25 }
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

end Krenn.CollapseSupportCover.Mask106
