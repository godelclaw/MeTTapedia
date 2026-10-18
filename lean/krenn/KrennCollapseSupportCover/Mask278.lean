import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask278

def activeValue : BitVec 14 := BitVec.ofNat 14 11008

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 21107195, component := 51 },
    { zero := BitVec.ofNat 26 21631419, component := 51 },
    { zero := BitVec.ofNat 26 29495801, component := 51 },
    { zero := BitVec.ofNat 26 30020025, component := 51 },
    { zero := BitVec.ofNat 26 21115358, component := 64 },
    { zero := BitVec.ofNat 26 21639582, component := 64 },
    { zero := BitVec.ofNat 26 21115386, component := 64 },
    { zero := BitVec.ofNat 26 21639610, component := 64 },
    { zero := BitVec.ofNat 26 29503964, component := 64 },
    { zero := BitVec.ofNat 26 30028188, component := 64 },
    { zero := BitVec.ofNat 26 29503992, component := 64 },
    { zero := BitVec.ofNat 26 30028216, component := 64 }
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

end Krenn.CollapseSupportCover.Mask278
