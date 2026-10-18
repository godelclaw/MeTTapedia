import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask042

def activeValue : BitVec 14 := BitVec.ofNat 14 608

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17026255, component := 38 },
    { zero := BitVec.ofNat 26 25283791, component := 38 },
    { zero := BitVec.ofNat 26 21204175, component := 38 },
    { zero := BitVec.ofNat 26 29461711, component := 38 },
    { zero := BitVec.ofNat 26 50580679, component := 38 },
    { zero := BitVec.ofNat 26 58838215, component := 38 },
    { zero := BitVec.ofNat 26 54758599, component := 38 },
    { zero := BitVec.ofNat 26 63016135, component := 38 }
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

end Krenn.CollapseSupportCover.Mask042
