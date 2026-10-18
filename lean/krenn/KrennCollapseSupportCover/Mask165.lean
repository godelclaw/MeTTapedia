import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask165

def activeValue : BitVec 14 := BitVec.ofNat 14 4116

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 12160677, component := 18 },
    { zero := BitVec.ofNat 26 12290725, component := 18 },
    { zero := BitVec.ofNat 26 12422181, component := 15 },
    { zero := BitVec.ofNat 26 12552229, component := 26 },
    { zero := BitVec.ofNat 26 12430341, component := 15 },
    { zero := BitVec.ofNat 26 12560389, component := 26 },
    { zero := BitVec.ofNat 26 12168836, component := 20 },
    { zero := BitVec.ofNat 26 12298884, component := 20 },
    { zero := BitVec.ofNat 26 12430468, component := 19 },
    { zero := BitVec.ofNat 26 12560516, component := 26 }
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

end Krenn.CollapseSupportCover.Mask165
