import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask257

def activeValue : BitVec 14 := BitVec.ofNat 14 9216

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 28854959, component := 18 },
    { zero := BitVec.ofNat 26 29116975, component := 18 },
    { zero := BitVec.ofNat 26 29125135, component := 18 },
    { zero := BitVec.ofNat 26 33303055, component := 18 },
    { zero := BitVec.ofNat 26 33032875, component := 30 },
    { zero := BitVec.ofNat 26 33294891, component := 29 },
    { zero := BitVec.ofNat 26 28855213, component := 9 },
    { zero := BitVec.ofNat 26 29117229, component := 9 },
    { zero := BitVec.ofNat 26 29125389, component := 9 },
    { zero := BitVec.ofNat 26 33303309, component := 18 },
    { zero := BitVec.ofNat 26 33033129, component := 42 },
    { zero := BitVec.ofNat 26 33295145, component := 26 },
    { zero := BitVec.ofNat 26 28863118, component := 20 },
    { zero := BitVec.ofNat 26 33041038, component := 20 },
    { zero := BitVec.ofNat 26 33041066, component := 30 },
    { zero := BitVec.ofNat 26 28863372, component := 12 },
    { zero := BitVec.ofNat 26 33041292, component := 20 },
    { zero := BitVec.ofNat 26 33041320, component := 42 }
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

end Krenn.CollapseSupportCover.Mask257
