import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask040

def activeValue : BitVec 14 := BitVec.ofNat 14 576

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17026527, component := 38 },
    { zero := BitVec.ofNat 26 21204447, component := 38 },
    { zero := BitVec.ofNat 26 27380959, component := 38 },
    { zero := BitVec.ofNat 26 31558879, component := 38 },
    { zero := BitVec.ofNat 26 19122399, component := 26 },
    { zero := BitVec.ofNat 26 23300319, component := 26 },
    { zero := BitVec.ofNat 26 50580951, component := 38 },
    { zero := BitVec.ofNat 26 54758871, component := 38 },
    { zero := BitVec.ofNat 26 60935383, component := 38 },
    { zero := BitVec.ofNat 26 65113303, component := 38 },
    { zero := BitVec.ofNat 26 52676823, component := 21 },
    { zero := BitVec.ofNat 26 56854743, component := 21 },
    { zero := BitVec.ofNat 26 25284061, component := 11 },
    { zero := BitVec.ofNat 26 29461981, component := 11 },
    { zero := BitVec.ofNat 26 27511261, component := 10 },
    { zero := BitVec.ofNat 26 31689181, component := 10 },
    { zero := BitVec.ofNat 26 58838485, component := 3 },
    { zero := BitVec.ofNat 26 63016405, component := 15 },
    { zero := BitVec.ofNat 26 61065685, component := 2 },
    { zero := BitVec.ofNat 26 65243605, component := 2 }
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

end Krenn.CollapseSupportCover.Mask040
