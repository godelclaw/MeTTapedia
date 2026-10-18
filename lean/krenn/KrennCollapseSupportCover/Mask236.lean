import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask236

def activeValue : BitVec 14 := BitVec.ofNat 14 5632

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 44632255, component := 2 },
    { zero := BitVec.ofNat 26 44632311, component := 2 },
    { zero := BitVec.ofNat 26 44632509, component := 2 },
    { zero := BitVec.ofNat 26 44632565, component := 2 },
    { zero := BitVec.ofNat 26 44640414, component := 5 },
    { zero := BitVec.ofNat 26 44640470, component := 5 },
    { zero := BitVec.ofNat 26 44640668, component := 5 },
    { zero := BitVec.ofNat 26 44640724, component := 5 }
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

end Krenn.CollapseSupportCover.Mask236
