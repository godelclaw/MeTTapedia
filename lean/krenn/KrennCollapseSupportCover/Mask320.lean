import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask320

def activeValue : BitVec 14 := BitVec.ofNat 14 12308

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 12066469, component := 18 },
    { zero := BitVec.ofNat 26 12196517, component := 18 },
    { zero := BitVec.ofNat 26 12328485, component := 18 },
    { zero := BitVec.ofNat 26 12458533, component := 18 },
    { zero := BitVec.ofNat 26 12336645, component := 18 },
    { zero := BitVec.ofNat 26 12466693, component := 18 },
    { zero := BitVec.ofNat 26 12074628, component := 20 },
    { zero := BitVec.ofNat 26 12204676, component := 20 }
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

end Krenn.CollapseSupportCover.Mask320
