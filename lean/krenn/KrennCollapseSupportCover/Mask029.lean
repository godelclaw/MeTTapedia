import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask029

def activeValue : BitVec 14 := BitVec.ofNat 14 514

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 16899582, component := 38 },
    { zero := BitVec.ofNat 26 18996478, component := 38 },
    { zero := BitVec.ofNat 26 50945470, component := 40 },
    { zero := BitVec.ofNat 26 17419710, component := 34 },
    { zero := BitVec.ofNat 26 53042366, component := 22 },
    { zero := BitVec.ofNat 26 19516606, component := 33 },
    { zero := BitVec.ofNat 26 50421238, component := 24 },
    { zero := BitVec.ofNat 26 50974198, component := 38 },
    { zero := BitVec.ofNat 26 52518134, component := 21 },
    { zero := BitVec.ofNat 26 53071094, component := 38 },
    { zero := BitVec.ofNat 26 21077498, component := 36 },
    { zero := BitVec.ofNat 26 23174394, component := 36 },
    { zero := BitVec.ofNat 26 55123386, component := 40 },
    { zero := BitVec.ofNat 26 21597626, component := 32 },
    { zero := BitVec.ofNat 26 57220282, component := 22 },
    { zero := BitVec.ofNat 26 23694522, component := 32 },
    { zero := BitVec.ofNat 26 54599154, component := 26 },
    { zero := BitVec.ofNat 26 55152114, component := 33 },
    { zero := BitVec.ofNat 26 56696050, component := 26 },
    { zero := BitVec.ofNat 26 57249010, component := 22 }
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

end Krenn.CollapseSupportCover.Mask029
