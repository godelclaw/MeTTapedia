import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask270

def activeValue : BitVec 14 := BitVec.ofNat 14 10248

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17978345, component := 50 },
    { zero := BitVec.ofNat 26 18240361, component := 50 },
    { zero := BitVec.ofNat 26 18502569, component := 50 },
    { zero := BitVec.ofNat 26 18764585, component := 50 },
    { zero := BitVec.ofNat 26 17986536, component := 63 },
    { zero := BitVec.ofNat 26 18510760, component := 63 }
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

end Krenn.CollapseSupportCover.Mask270
