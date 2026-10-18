import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask261

def activeValue : BitVec 14 := BitVec.ofNat 14 9280

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 28330703, component := 18 },
    { zero := BitVec.ofNat 26 32508623, component := 18 },
    { zero := BitVec.ofNat 26 28592719, component := 18 },
    { zero := BitVec.ofNat 26 32770639, component := 18 },
    { zero := BitVec.ofNat 26 28330957, component := 9 },
    { zero := BitVec.ofNat 26 32508877, component := 18 },
    { zero := BitVec.ofNat 26 28592973, component := 9 },
    { zero := BitVec.ofNat 26 32770893, component := 18 }
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

end Krenn.CollapseSupportCover.Mask261
