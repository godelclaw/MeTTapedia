import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask250

def activeValue : BitVec 14 := BitVec.ofNat 14 8200

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17981417, component := 50 },
    { zero := BitVec.ofNat 26 20077545, component := 50 },
    { zero := BitVec.ofNat 26 18243433, component := 50 },
    { zero := BitVec.ofNat 26 20339561, component := 50 },
    { zero := BitVec.ofNat 26 18505641, component := 50 },
    { zero := BitVec.ofNat 26 20601769, component := 50 },
    { zero := BitVec.ofNat 26 18767657, component := 50 },
    { zero := BitVec.ofNat 26 20863785, component := 50 },
    { zero := BitVec.ofNat 26 17989608, component := 63 },
    { zero := BitVec.ofNat 26 20085736, component := 63 },
    { zero := BitVec.ofNat 26 18513832, component := 63 },
    { zero := BitVec.ofNat 26 20609960, component := 63 }
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

end Krenn.CollapseSupportCover.Mask250
