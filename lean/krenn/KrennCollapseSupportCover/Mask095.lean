import KrennCollapseSupportCover.Base

namespace Krenn.CollapseSupportCover.Mask095

def activeValue : BitVec 14 := BitVec.ofNat 14 2048

def strataData : List Stratum := [
    { zero := BitVec.ofNat 26 18076655, component := 50 },
    { zero := BitVec.ofNat 26 18338159, component := 49 },
    { zero := BitVec.ofNat 26 52122543, component := 50 },
    { zero := BitVec.ofNat 26 18596783, component := 39 },
    { zero := BitVec.ofNat 26 52384047, component := 45 },
    { zero := BitVec.ofNat 26 18858287, component := 26 },
    { zero := BitVec.ofNat 26 18346319, component := 62 },
    { zero := BitVec.ofNat 26 52392207, component := 56 },
    { zero := BitVec.ofNat 26 18866447, component := 26 },
    { zero := BitVec.ofNat 26 51598311, component := 24 },
    { zero := BitVec.ofNat 26 52151271, component := 24 },
    { zero := BitVec.ofNat 26 51859815, component := 46 },
    { zero := BitVec.ofNat 26 52412775, component := 23 },
    { zero := BitVec.ofNat 26 51867975, component := 57 },
    { zero := BitVec.ofNat 26 52420935, component := 23 },
    { zero := BitVec.ofNat 26 22270955, component := 50 },
    { zero := BitVec.ofNat 26 22532459, component := 47 },
    { zero := BitVec.ofNat 26 56316843, component := 50 },
    { zero := BitVec.ofNat 26 22791083, component := 39 },
    { zero := BitVec.ofNat 26 56578347, component := 47 },
    { zero := BitVec.ofNat 26 23052587, component := 26 },
    { zero := BitVec.ofNat 26 55792611, component := 45 },
    { zero := BitVec.ofNat 26 56345571, component := 25 },
    { zero := BitVec.ofNat 26 56054115, component := 46 },
    { zero := BitVec.ofNat 26 56607075, component := 23 },
    { zero := BitVec.ofNat 26 26465261, component := 50 },
    { zero := BitVec.ofNat 26 26726765, component := 49 },
    { zero := BitVec.ofNat 26 60511149, component := 50 },
    { zero := BitVec.ofNat 26 26985389, component := 9 },
    { zero := BitVec.ofNat 26 60772653, component := 3 },
    { zero := BitVec.ofNat 26 27246893, component := 26 },
    { zero := BitVec.ofNat 26 26734925, component := 62 },
    { zero := BitVec.ofNat 26 60780813, component := 3 },
    { zero := BitVec.ofNat 26 27255053, component := 26 },
    { zero := BitVec.ofNat 26 59986917, component := 3 },
    { zero := BitVec.ofNat 26 60539877, component := 3 },
    { zero := BitVec.ofNat 26 60248421, component := 4 },
    { zero := BitVec.ofNat 26 60801381, component := 4 },
    { zero := BitVec.ofNat 26 60256581, component := 4 },
    { zero := BitVec.ofNat 26 60809541, component := 4 },
    { zero := BitVec.ofNat 26 30659561, component := 50 },
    { zero := BitVec.ofNat 26 30921065, component := 49 },
    { zero := BitVec.ofNat 26 64705449, component := 50 },
    { zero := BitVec.ofNat 26 31179689, component := 39 },
    { zero := BitVec.ofNat 26 64966953, component := 45 },
    { zero := BitVec.ofNat 26 31441193, component := 26 },
    { zero := BitVec.ofNat 26 64181217, component := 45 },
    { zero := BitVec.ofNat 26 64734177, component := 25 },
    { zero := BitVec.ofNat 26 64442721, component := 46 },
    { zero := BitVec.ofNat 26 64995681, component := 23 },
    { zero := BitVec.ofNat 26 18084814, component := 63 },
    { zero := BitVec.ofNat 26 18346446, component := 62 },
    { zero := BitVec.ofNat 26 52130702, component := 63 },
    { zero := BitVec.ofNat 26 18604942, component := 26 },
    { zero := BitVec.ofNat 26 52392334, component := 56 },
    { zero := BitVec.ofNat 26 18866574, component := 26 },
    { zero := BitVec.ofNat 26 51606470, component := 58 },
    { zero := BitVec.ofNat 26 52159430, component := 24 },
    { zero := BitVec.ofNat 26 51868102, component := 57 },
    { zero := BitVec.ofNat 26 52421062, component := 24 },
    { zero := BitVec.ofNat 26 22279146, component := 63 },
    { zero := BitVec.ofNat 26 22540778, component := 59 },
    { zero := BitVec.ofNat 26 56325034, component := 63 },
    { zero := BitVec.ofNat 26 22799274, component := 39 },
    { zero := BitVec.ofNat 26 56586666, component := 59 },
    { zero := BitVec.ofNat 26 23060906, component := 31 },
    { zero := BitVec.ofNat 26 55800802, component := 56 },
    { zero := BitVec.ofNat 26 56353762, component := 25 },
    { zero := BitVec.ofNat 26 56062434, component := 57 },
    { zero := BitVec.ofNat 26 56615394, component := 25 },
    { zero := BitVec.ofNat 26 26473420, component := 63 },
    { zero := BitVec.ofNat 26 26735052, component := 62 },
    { zero := BitVec.ofNat 26 60519308, component := 12 },
    { zero := BitVec.ofNat 26 26993548, component := 12 },
    { zero := BitVec.ofNat 26 60780940, component := 6 },
    { zero := BitVec.ofNat 26 27255180, component := 26 },
    { zero := BitVec.ofNat 26 59995076, component := 56 },
    { zero := BitVec.ofNat 26 60548036, component := 6 },
    { zero := BitVec.ofNat 26 60256708, component := 57 },
    { zero := BitVec.ofNat 26 60809668, component := 6 },
    { zero := BitVec.ofNat 26 30667752, component := 63 },
    { zero := BitVec.ofNat 26 30929384, component := 62 },
    { zero := BitVec.ofNat 26 64713640, component := 63 },
    { zero := BitVec.ofNat 26 31187880, component := 39 },
    { zero := BitVec.ofNat 26 64975272, component := 25 },
    { zero := BitVec.ofNat 26 31449512, component := 26 },
    { zero := BitVec.ofNat 26 64189408, component := 56 },
    { zero := BitVec.ofNat 26 64742368, component := 25 },
    { zero := BitVec.ofNat 26 64451040, component := 57 },
    { zero := BitVec.ofNat 26 65004000, component := 25 }
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

end Krenn.CollapseSupportCover.Mask095
