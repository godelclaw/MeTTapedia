import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask158

def activeValue : BitVec 14 := BitVec.ofNat 14 4105

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1555800, component := 64 },
    { zero := BitVec.ofNat 26 3651928, component := 64 },
    { zero := BitVec.ofNat 26 35601688, component := 64 },
    { zero := BitVec.ofNat 26 2075928, component := 35 },
    { zero := BitVec.ofNat 26 37697816, component := 64 },
    { zero := BitVec.ofNat 26 4172056, component := 26 },
    { zero := BitVec.ofNat 26 35077456, component := 62 },
    { zero := BitVec.ofNat 26 35630416, component := 37 },
    { zero := BitVec.ofNat 26 37173584, component := 62 },
    { zero := BitVec.ofNat 26 37726544, component := 26 }
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

end Krenn.CollapseSupportCover.Mask158
