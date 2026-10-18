import KrennCollapseSupportCover.Base
import KrennCollapseSupportCoverSemantic

namespace Krenn.CollapseSupportCover.Mask157

def activeValue : BitVec 14 := BitVec.ofNat 14 4104

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 1286137, component := 51 },
    { zero := BitVec.ofNat 26 3382265, component := 51 },
    { zero := BitVec.ofNat 26 1547641, component := 51 },
    { zero := BitVec.ofNat 26 3643769, component := 51 },
    { zero := BitVec.ofNat 26 35332025, component := 51 },
    { zero := BitVec.ofNat 26 1806265, component := 34 },
    { zero := BitVec.ofNat 26 37428153, component := 51 },
    { zero := BitVec.ofNat 26 3902393, component := 40 },
    { zero := BitVec.ofNat 26 35593529, component := 51 },
    { zero := BitVec.ofNat 26 2067769, component := 35 },
    { zero := BitVec.ofNat 26 37689657, component := 51 },
    { zero := BitVec.ofNat 26 4163897, component := 26 },
    { zero := BitVec.ofNat 26 34807793, component := 26 },
    { zero := BitVec.ofNat 26 35360753, component := 33 },
    { zero := BitVec.ofNat 26 36903921, component := 43 },
    { zero := BitVec.ofNat 26 37456881, component := 22 },
    { zero := BitVec.ofNat 26 35069297, component := 49 },
    { zero := BitVec.ofNat 26 35622257, component := 37 },
    { zero := BitVec.ofNat 26 37165425, component := 43 },
    { zero := BitVec.ofNat 26 37718385, component := 26 },
    { zero := BitVec.ofNat 26 1294328, component := 64 },
    { zero := BitVec.ofNat 26 3390456, component := 64 },
    { zero := BitVec.ofNat 26 1555960, component := 64 },
    { zero := BitVec.ofNat 26 3652088, component := 64 },
    { zero := BitVec.ofNat 26 35340216, component := 64 },
    { zero := BitVec.ofNat 26 1814456, component := 34 },
    { zero := BitVec.ofNat 26 37436344, component := 64 },
    { zero := BitVec.ofNat 26 3910584, component := 40 },
    { zero := BitVec.ofNat 26 35601848, component := 64 },
    { zero := BitVec.ofNat 26 2076088, component := 34 },
    { zero := BitVec.ofNat 26 37697976, component := 64 },
    { zero := BitVec.ofNat 26 4172216, component := 40 },
    { zero := BitVec.ofNat 26 34815984, component := 26 },
    { zero := BitVec.ofNat 26 35368944, component := 33 },
    { zero := BitVec.ofNat 26 36912112, component := 53 },
    { zero := BitVec.ofNat 26 37465072, component := 22 },
    { zero := BitVec.ofNat 26 35077616, component := 62 },
    { zero := BitVec.ofNat 26 35630576, component := 37 },
    { zero := BitVec.ofNat 26 37173744, component := 62 },
    { zero := BitVec.ofNat 26 37726704, component := 22 }
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

end Krenn.CollapseSupportCover.Mask157
