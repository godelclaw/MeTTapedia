import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask175

def activeValue : BitVec 14 := BitVec.ofNat 14 4176

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1281991, component := 38 },
    { zero := BitVec.ofNat 26 11636423, component := 38 },
    { zero := BitVec.ofNat 26 3377863, component := 41 },
    { zero := BitVec.ofNat 26 1543495, component := 37 },
    { zero := BitVec.ofNat 26 11897927, component := 15 },
    { zero := BitVec.ofNat 26 3639367, component := 26 },
    { zero := BitVec.ofNat 26 9539525, component := 15 },
    { zero := BitVec.ofNat 26 11766725, component := 18 },
    { zero := BitVec.ofNat 26 9801029, component := 16 },
    { zero := BitVec.ofNat 26 12028229, component := 17 }
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

end Krenn.CollapseSupportCover.Mask175
