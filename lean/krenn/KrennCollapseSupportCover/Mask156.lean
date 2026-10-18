import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask156

def activeValue : BitVec 14 := BitVec.ofNat 14 4100

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 45686453, component := 2 },
    { zero := BitVec.ofNat 26 45715125, component := 2 },
    { zero := BitVec.ofNat 26 45816501, component := 2 },
    { zero := BitVec.ofNat 26 45845173, component := 2 },
    { zero := BitVec.ofNat 26 45947957, component := 2 },
    { zero := BitVec.ofNat 26 45976629, component := 2 },
    { zero := BitVec.ofNat 26 46078005, component := 2 },
    { zero := BitVec.ofNat 26 46106677, component := 2 },
    { zero := BitVec.ofNat 26 45956117, component := 2 },
    { zero := BitVec.ofNat 26 45984789, component := 2 },
    { zero := BitVec.ofNat 26 46086165, component := 2 },
    { zero := BitVec.ofNat 26 46114837, component := 2 },
    { zero := BitVec.ofNat 26 45694612, component := 5 },
    { zero := BitVec.ofNat 26 45723284, component := 5 },
    { zero := BitVec.ofNat 26 45824660, component := 5 },
    { zero := BitVec.ofNat 26 45853332, component := 5 },
    { zero := BitVec.ofNat 26 45956244, component := 5 },
    { zero := BitVec.ofNat 26 45984916, component := 5 },
    { zero := BitVec.ofNat 26 46086292, component := 5 },
    { zero := BitVec.ofNat 26 46114964, component := 5 }
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

end Krenn.CollapseSupportCover.Mask156
