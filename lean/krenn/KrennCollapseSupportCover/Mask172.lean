import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask172

def activeValue : BitVec 14 := BitVec.ofNat 14 4160

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1282015, component := 38 },
    { zero := BitVec.ofNat 26 11636447, component := 38 },
    { zero := BitVec.ofNat 26 3377887, component := 41 },
    { zero := BitVec.ofNat 26 1543519, component := 37 },
    { zero := BitVec.ofNat 26 11897951, component := 15 },
    { zero := BitVec.ofNat 26 3639391, component := 26 },
    { zero := BitVec.ofNat 26 34836439, component := 38 },
    { zero := BitVec.ofNat 26 45190871, component := 38 },
    { zero := BitVec.ofNat 26 36932311, component := 21 },
    { zero := BitVec.ofNat 26 35097943, component := 37 },
    { zero := BitVec.ofNat 26 45452375, component := 2 },
    { zero := BitVec.ofNat 26 37193815, component := 26 },
    { zero := BitVec.ofNat 26 9539549, component := 11 },
    { zero := BitVec.ofNat 26 11766749, component := 18 },
    { zero := BitVec.ofNat 26 9801053, component := 16 },
    { zero := BitVec.ofNat 26 12028253, component := 10 },
    { zero := BitVec.ofNat 26 43093973, component := 15 },
    { zero := BitVec.ofNat 26 45321173, component := 2 },
    { zero := BitVec.ofNat 26 43355477, component := 16 },
    { zero := BitVec.ofNat 26 45582677, component := 2 }
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

end Krenn.CollapseSupportCover.Mask172
