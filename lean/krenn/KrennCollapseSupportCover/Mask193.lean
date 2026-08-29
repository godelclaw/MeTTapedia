import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask193

def activeValue : BitVec 14 := BitVec.ofNat 14 4608

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 237055, component := 38 },
    { zero := BitVec.ofNat 26 10591487, component := 38 },
    { zero := BitVec.ofNat 26 2332927, component := 26 },
    { zero := BitVec.ofNat 26 34282943, component := 51 },
    { zero := BitVec.ofNat 26 757183, component := 34 },
    { zero := BitVec.ofNat 26 44637375, component := 2 },
    { zero := BitVec.ofNat 26 11111615, component := 15 },
    { zero := BitVec.ofNat 26 36378815, component := 43 },
    { zero := BitVec.ofNat 26 2853055, component := 26 },
    { zero := BitVec.ofNat 26 33758711, component := 26 },
    { zero := BitVec.ofNat 26 34311671, component := 38 },
    { zero := BitVec.ofNat 26 44113143, component := 2 },
    { zero := BitVec.ofNat 26 44666103, component := 38 },
    { zero := BitVec.ofNat 26 35854583, component := 43 },
    { zero := BitVec.ofNat 26 36407543, component := 21 },
    { zero := BitVec.ofNat 26 8494589, component := 11 },
    { zero := BitVec.ofNat 26 10721789, component := 51 },
    { zero := BitVec.ofNat 26 42540477, component := 10 },
    { zero := BitVec.ofNat 26 9014717, component := 11 },
    { zero := BitVec.ofNat 26 44767677, component := 51 },
    { zero := BitVec.ofNat 26 11241917, component := 10 },
    { zero := BitVec.ofNat 26 42016245, component := 26 },
    { zero := BitVec.ofNat 26 42569205, component := 15 },
    { zero := BitVec.ofNat 26 44243445, component := 2 },
    { zero := BitVec.ofNat 26 44796405, component := 2 },
    { zero := BitVec.ofNat 26 245214, component := 38 },
    { zero := BitVec.ofNat 26 10599646, component := 38 },
    { zero := BitVec.ofNat 26 2341086, component := 61 },
    { zero := BitVec.ofNat 26 34291102, component := 64 },
    { zero := BitVec.ofNat 26 765342, component := 35 },
    { zero := BitVec.ofNat 26 44645534, component := 5 },
    { zero := BitVec.ofNat 26 11119774, component := 19 },
    { zero := BitVec.ofNat 26 36386974, component := 53 },
    { zero := BitVec.ofNat 26 2861214, component := 26 },
    { zero := BitVec.ofNat 26 33766870, component := 61 },
    { zero := BitVec.ofNat 26 34319830, component := 38 },
    { zero := BitVec.ofNat 26 44121302, component := 21 },
    { zero := BitVec.ofNat 26 44674262, component := 5 },
    { zero := BitVec.ofNat 26 35862742, component := 55 },
    { zero := BitVec.ofNat 26 36415702, component := 21 },
    { zero := BitVec.ofNat 26 8502748, component := 35 },
    { zero := BitVec.ofNat 26 10729948, component := 64 },
    { zero := BitVec.ofNat 26 42548636, component := 13 },
    { zero := BitVec.ofNat 26 9022876, component := 14 },
    { zero := BitVec.ofNat 26 44775836, component := 5 },
    { zero := BitVec.ofNat 26 11250076, component := 13 },
    { zero := BitVec.ofNat 26 42024404, component := 26 },
    { zero := BitVec.ofNat 26 42577364, component := 19 },
    { zero := BitVec.ofNat 26 44251604, component := 53 },
    { zero := BitVec.ofNat 26 44804564, component := 5 }
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

end Krenn.CollapseSupportCover.Mask193
