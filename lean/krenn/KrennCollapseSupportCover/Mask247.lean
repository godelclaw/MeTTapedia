import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask247

def activeValue : BitVec 14 := BitVec.ofNat 14 8192

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 17981423, component := 50 },
    { zero := BitVec.ofNat 26 28335855, component := 18 },
    { zero := BitVec.ofNat 26 20077295, component := 41 },
    { zero := BitVec.ofNat 26 18243439, component := 50 },
    { zero := BitVec.ofNat 26 28597871, component := 18 },
    { zero := BitVec.ofNat 26 20339311, component := 52 },
    { zero := BitVec.ofNat 26 18505647, component := 50 },
    { zero := BitVec.ofNat 26 28860079, component := 18 },
    { zero := BitVec.ofNat 26 20601519, component := 52 },
    { zero := BitVec.ofNat 26 18767663, component := 50 },
    { zero := BitVec.ofNat 26 29122095, component := 18 },
    { zero := BitVec.ofNat 26 20863535, component := 52 },
    { zero := BitVec.ofNat 26 18251599, component := 63 },
    { zero := BitVec.ofNat 26 22429519, component := 59 },
    { zero := BitVec.ofNat 26 28606031, component := 18 },
    { zero := BitVec.ofNat 26 32783951, component := 18 },
    { zero := BitVec.ofNat 26 20347471, component := 65 },
    { zero := BitVec.ofNat 26 24525391, component := 60 },
    { zero := BitVec.ofNat 26 18775823, component := 63 },
    { zero := BitVec.ofNat 26 22953743, component := 59 },
    { zero := BitVec.ofNat 26 29130255, component := 18 },
    { zero := BitVec.ofNat 26 33308175, component := 18 },
    { zero := BitVec.ofNat 26 20871695, component := 65 },
    { zero := BitVec.ofNat 26 25049615, component := 60 },
    { zero := BitVec.ofNat 26 22159339, component := 47 },
    { zero := BitVec.ofNat 26 32513771, component := 29 },
    { zero := BitVec.ofNat 26 24255211, component := 48 },
    { zero := BitVec.ofNat 26 22421355, component := 47 },
    { zero := BitVec.ofNat 26 32775787, component := 29 },
    { zero := BitVec.ofNat 26 24517227, component := 48 },
    { zero := BitVec.ofNat 26 22683563, component := 47 },
    { zero := BitVec.ofNat 26 33037995, component := 30 },
    { zero := BitVec.ofNat 26 24779435, component := 48 },
    { zero := BitVec.ofNat 26 22945579, component := 47 },
    { zero := BitVec.ofNat 26 33300011, component := 29 },
    { zero := BitVec.ofNat 26 25041451, component := 48 },
    { zero := BitVec.ofNat 26 26238957, component := 9 },
    { zero := BitVec.ofNat 26 28466157, component := 50 },
    { zero := BitVec.ofNat 26 26500973, component := 9 },
    { zero := BitVec.ofNat 26 28728173, component := 50 },
    { zero := BitVec.ofNat 26 26763181, component := 9 },
    { zero := BitVec.ofNat 26 28990381, component := 50 },
    { zero := BitVec.ofNat 26 27025197, component := 9 },
    { zero := BitVec.ofNat 26 29252397, component := 50 },
    { zero := BitVec.ofNat 26 26509133, component := 9 },
    { zero := BitVec.ofNat 26 30687053, component := 17 },
    { zero := BitVec.ofNat 26 28736333, component := 63 },
    { zero := BitVec.ofNat 26 32914253, component := 18 },
    { zero := BitVec.ofNat 26 27033357, component := 9 },
    { zero := BitVec.ofNat 26 31211277, component := 26 },
    { zero := BitVec.ofNat 26 29260557, component := 63 },
    { zero := BitVec.ofNat 26 33438477, component := 18 },
    { zero := BitVec.ofNat 26 30416873, component := 26 },
    { zero := BitVec.ofNat 26 32644073, component := 52 },
    { zero := BitVec.ofNat 26 30678889, component := 26 },
    { zero := BitVec.ofNat 26 32906089, component := 49 },
    { zero := BitVec.ofNat 26 30941097, component := 26 },
    { zero := BitVec.ofNat 26 33168297, component := 52 },
    { zero := BitVec.ofNat 26 31203113, component := 26 },
    { zero := BitVec.ofNat 26 33430313, component := 52 },
    { zero := BitVec.ofNat 26 17989582, component := 63 },
    { zero := BitVec.ofNat 26 22167502, component := 59 },
    { zero := BitVec.ofNat 26 28344014, component := 41 },
    { zero := BitVec.ofNat 26 32521934, component := 41 },
    { zero := BitVec.ofNat 26 20085454, component := 66 },
    { zero := BitVec.ofNat 26 24263374, component := 60 },
    { zero := BitVec.ofNat 26 18513806, component := 63 },
    { zero := BitVec.ofNat 26 22691726, component := 59 },
    { zero := BitVec.ofNat 26 28868238, component := 20 },
    { zero := BitVec.ofNat 26 33046158, component := 20 },
    { zero := BitVec.ofNat 26 20609678, component := 65 },
    { zero := BitVec.ofNat 26 24787598, component := 60 },
    { zero := BitVec.ofNat 26 22167530, component := 59 },
    { zero := BitVec.ofNat 26 32521962, component := 29 },
    { zero := BitVec.ofNat 26 24263402, component := 60 },
    { zero := BitVec.ofNat 26 22691754, component := 59 },
    { zero := BitVec.ofNat 26 33046186, component := 30 },
    { zero := BitVec.ofNat 26 24787626, component := 60 },
    { zero := BitVec.ofNat 26 26247116, component := 26 },
    { zero := BitVec.ofNat 26 30425036, component := 26 },
    { zero := BitVec.ofNat 26 28474316, component := 63 },
    { zero := BitVec.ofNat 26 32652236, component := 65 },
    { zero := BitVec.ofNat 26 26771340, component := 12 },
    { zero := BitVec.ofNat 26 30949260, component := 26 },
    { zero := BitVec.ofNat 26 28998540, component := 12 },
    { zero := BitVec.ofNat 26 33176460, component := 20 },
    { zero := BitVec.ofNat 26 30425064, component := 26 },
    { zero := BitVec.ofNat 26 32652264, component := 65 },
    { zero := BitVec.ofNat 26 30949288, component := 26 },
    { zero := BitVec.ofNat 26 33176488, component := 42 }
]

def data : ActiveCover := {
  active := activeValue
  strata := strataData
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroCovered (pattern : Fin 26 → Prop)
    (feasible : Feasible pattern)
    (activePattern : ActiveMatches data.active pattern) :
    ∃ stratum ∈ data.strata, ZeroMatches stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [Feasible, relationLeftActive,
    relationRightActive] at feasible
  change ActiveMatches activeValue pattern at activePattern
  simp (config := { maxSteps := 1000000 }) only [activeValue, ActiveMatches,
    relationLeftActive] at activePattern
  change ∃ stratum ∈ strataData, ZeroMatches stratum.zero pattern
  simp (config := { maxSteps := 1000000 }) only [strataData, ZeroMatches,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

end Krenn.CollapseSupportCover.Mask247
