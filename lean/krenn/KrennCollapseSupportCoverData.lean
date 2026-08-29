import Mathlib

/-! Concrete Boolean support cover for the reduced C6 collapse binomials. -/

namespace Krenn.CollapseSupportCoverData

structure Stratum where
  zero : BitVec 26
  component : Nat
deriving DecidableEq, Repr

structure ActiveCover where
  active : BitVec 14
  strata : List Stratum
deriving DecidableEq, Repr

def subsetMask (support pattern : BitVec 26) : Bool :=
  (support &&& pattern) == support

def relationSupports : Fin 14 → BitVec 26 × BitVec 26
  | 0 => (BitVec.ofNat 26 129, BitVec.ofNat 26 36)
  | 1 => (BitVec.ofNat 26 8193, BitVec.ofNat 26 8519680)
  | 2 => (BitVec.ofNat 26 258, BitVec.ofNat 26 72)
  | 3 => (BitVec.ofNat 26 8388610, BitVec.ofNat 26 4194308)
  | 4 => (BitVec.ofNat 26 33554440, BitVec.ofNat 26 16777232)
  | 5 => (BitVec.ofNat 26 1048592, BitVec.ofNat 26 2097408)
  | 6 => (BitVec.ofNat 26 8224, BitVec.ofNat 26 528384)
  | 7 => (BitVec.ofNat 26 524352, BitVec.ofNat 26 262272)
  | 8 => (BitVec.ofNat 26 66048, BitVec.ofNat 26 18432)
  | 9 => (BitVec.ofNat 26 262656, BitVec.ofNat 26 1048576)
  | 10 => (BitVec.ofNat 26 132096, BitVec.ofNat 26 36864)
  | 11 => (BitVec.ofNat 26 2098176, BitVec.ofNat 26 2048)
  | 12 => (BitVec.ofNat 26 4210688, BitVec.ofNat 26 16777216)
  | 13 => (BitVec.ofNat 26 33587200, BitVec.ofNat 26 65536)

def relationActive (pattern : BitVec 26) (index : Fin 14) : Bool :=
  subsetMask (relationSupports index).1 pattern

def feasible (pattern : BitVec 26) : Bool :=
  (relationActive pattern 0 == subsetMask (relationSupports 0).2 pattern) &&
    (relationActive pattern 1 == subsetMask (relationSupports 1).2 pattern) &&
    (relationActive pattern 2 == subsetMask (relationSupports 2).2 pattern) &&
    (relationActive pattern 3 == subsetMask (relationSupports 3).2 pattern) &&
    (relationActive pattern 4 == subsetMask (relationSupports 4).2 pattern) &&
    (relationActive pattern 5 == subsetMask (relationSupports 5).2 pattern) &&
    (relationActive pattern 6 == subsetMask (relationSupports 6).2 pattern) &&
    (relationActive pattern 7 == subsetMask (relationSupports 7).2 pattern) &&
    (relationActive pattern 8 == subsetMask (relationSupports 8).2 pattern) &&
    (relationActive pattern 9 == subsetMask (relationSupports 9).2 pattern) &&
    (relationActive pattern 10 == subsetMask (relationSupports 10).2 pattern) &&
    (relationActive pattern 11 == subsetMask (relationSupports 11).2 pattern) &&
    (relationActive pattern 12 == subsetMask (relationSupports 12).2 pattern) &&
    (relationActive pattern 13 == subsetMask (relationSupports 13).2 pattern)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover0 : ActiveCover := {
  active := BitVec.ofNat 14 0
  strata := [
    { zero := BitVec.ofNat 26 18079727, component := 38 },
    { zero := BitVec.ofNat 26 28434159, component := 38 },
    { zero := BitVec.ofNat 26 20175599, component := 41 },
    { zero := BitVec.ofNat 26 18341231, component := 49 },
    { zero := BitVec.ofNat 26 28695663, component := 15 },
    { zero := BitVec.ofNat 26 20437103, component := 26 },
    { zero := BitVec.ofNat 26 52125615, component := 50 },
    { zero := BitVec.ofNat 26 18599855, component := 39 },
    { zero := BitVec.ofNat 26 62480047, component := 18 },
    { zero := BitVec.ofNat 26 28954287, component := 18 },
    { zero := BitVec.ofNat 26 54221487, component := 52 },
    { zero := BitVec.ofNat 26 20695727, component := 42 },
    { zero := BitVec.ofNat 26 52387119, component := 45 },
    { zero := BitVec.ofNat 26 18861359, component := 26 },
    { zero := BitVec.ofNat 26 62741551, component := 3 },
    { zero := BitVec.ofNat 26 29215791, component := 15 },
    { zero := BitVec.ofNat 26 54482991, component := 45 },
    { zero := BitVec.ofNat 26 20957231, component := 26 },
    { zero := BitVec.ofNat 26 18349391, component := 62 },
    { zero := BitVec.ofNat 26 22527311, component := 59 },
    { zero := BitVec.ofNat 26 28703823, component := 15 },
    { zero := BitVec.ofNat 26 32881743, component := 36 },
    { zero := BitVec.ofNat 26 20445263, component := 26 },
    { zero := BitVec.ofNat 26 24623183, component := 59 },
    { zero := BitVec.ofNat 26 52395279, component := 56 },
    { zero := BitVec.ofNat 26 56573199, component := 59 },
    { zero := BitVec.ofNat 26 18869519, component := 26 },
    { zero := BitVec.ofNat 26 23047439, component := 36 },
    { zero := BitVec.ofNat 26 62749711, component := 3 },
    { zero := BitVec.ofNat 26 66927631, component := 26 },
    { zero := BitVec.ofNat 26 29223951, component := 15 },
    { zero := BitVec.ofNat 26 33401871, component := 36 },
    { zero := BitVec.ofNat 26 54491151, component := 56 },
    { zero := BitVec.ofNat 26 58669071, component := 59 },
    { zero := BitVec.ofNat 26 20965391, component := 26 },
    { zero := BitVec.ofNat 26 25143311, component := 28 },
    { zero := BitVec.ofNat 26 51601383, component := 24 },
    { zero := BitVec.ofNat 26 52154343, component := 38 },
    { zero := BitVec.ofNat 26 61955815, component := 18 },
    { zero := BitVec.ofNat 26 62508775, component := 38 },
    { zero := BitVec.ofNat 26 53697255, component := 24 },
    { zero := BitVec.ofNat 26 54250215, component := 24 },
    { zero := BitVec.ofNat 26 51862887, component := 46 },
    { zero := BitVec.ofNat 26 52415847, component := 37 },
    { zero := BitVec.ofNat 26 62217319, component := 3 },
    { zero := BitVec.ofNat 26 62770279, component := 3 },
    { zero := BitVec.ofNat 26 53958759, component := 45 },
    { zero := BitVec.ofNat 26 54511719, component := 26 },
    { zero := BitVec.ofNat 26 51871047, component := 57 },
    { zero := BitVec.ofNat 26 56048967, component := 62 },
    { zero := BitVec.ofNat 26 52424007, component := 37 },
    { zero := BitVec.ofNat 26 56601927, component := 37 },
    { zero := BitVec.ofNat 26 62225479, component := 3 },
    { zero := BitVec.ofNat 26 66403399, component := 26 },
    { zero := BitVec.ofNat 26 62778439, component := 3 },
    { zero := BitVec.ofNat 26 66956359, component := 15 },
    { zero := BitVec.ofNat 26 53966919, component := 56 },
    { zero := BitVec.ofNat 26 58144839, component := 54 },
    { zero := BitVec.ofNat 26 54519879, component := 26 },
    { zero := BitVec.ofNat 26 58697799, component := 26 },
    { zero := BitVec.ofNat 26 22257643, component := 47 },
    { zero := BitVec.ofNat 26 32612075, component := 36 },
    { zero := BitVec.ofNat 26 24353515, component := 48 },
    { zero := BitVec.ofNat 26 22519147, component := 47 },
    { zero := BitVec.ofNat 26 32873579, component := 36 },
    { zero := BitVec.ofNat 26 24615019, component := 47 },
    { zero := BitVec.ofNat 26 56303531, component := 47 },
    { zero := BitVec.ofNat 26 22777771, component := 32 },
    { zero := BitVec.ofNat 26 66657963, component := 30 },
    { zero := BitVec.ofNat 26 33132203, component := 32 },
    { zero := BitVec.ofNat 26 58399403, component := 48 },
    { zero := BitVec.ofNat 26 24873643, component := 30 },
    { zero := BitVec.ofNat 26 56565035, component := 47 },
    { zero := BitVec.ofNat 26 23039275, component := 36 },
    { zero := BitVec.ofNat 26 66919467, component := 26 },
    { zero := BitVec.ofNat 26 33393707, component := 36 },
    { zero := BitVec.ofNat 26 58660907, component := 47 },
    { zero := BitVec.ofNat 26 25135147, component := 27 },
    { zero := BitVec.ofNat 26 55779299, component := 26 },
    { zero := BitVec.ofNat 26 56332259, component := 33 },
    { zero := BitVec.ofNat 26 66133731, component := 26 },
    { zero := BitVec.ofNat 26 66686691, component := 42 },
    { zero := BitVec.ofNat 26 57875171, component := 52 },
    { zero := BitVec.ofNat 26 58428131, component := 42 },
    { zero := BitVec.ofNat 26 56040803, component := 49 },
    { zero := BitVec.ofNat 26 56593763, component := 37 },
    { zero := BitVec.ofNat 26 66395235, component := 26 },
    { zero := BitVec.ofNat 26 66948195, component := 26 },
    { zero := BitVec.ofNat 26 58136675, component := 44 },
    { zero := BitVec.ofNat 26 58689635, component := 26 },
    { zero := BitVec.ofNat 26 26337261, component := 9 },
    { zero := BitVec.ofNat 26 28564461, component := 50 },
    { zero := BitVec.ofNat 26 26598765, component := 16 },
    { zero := BitVec.ofNat 26 28825965, component := 49 },
    { zero := BitVec.ofNat 26 60383149, component := 9 },
    { zero := BitVec.ofNat 26 26857389, component := 9 },
    { zero := BitVec.ofNat 26 62610349, component := 50 },
    { zero := BitVec.ofNat 26 29084589, component := 9 },
    { zero := BitVec.ofNat 26 60644653, component := 3 },
    { zero := BitVec.ofNat 26 27118893, component := 15 },
    { zero := BitVec.ofNat 26 62871853, component := 3 },
    { zero := BitVec.ofNat 26 29346093, component := 26 },
    { zero := BitVec.ofNat 26 26606925, component := 16 },
    { zero := BitVec.ofNat 26 30784845, component := 16 },
    { zero := BitVec.ofNat 26 28834125, component := 62 },
    { zero := BitVec.ofNat 26 33012045, component := 62 },
    { zero := BitVec.ofNat 26 60652813, component := 3 },
    { zero := BitVec.ofNat 26 64830733, component := 26 },
    { zero := BitVec.ofNat 26 27127053, component := 15 },
    { zero := BitVec.ofNat 26 31304973, component := 8 },
    { zero := BitVec.ofNat 26 62880013, component := 3 },
    { zero := BitVec.ofNat 26 67057933, component := 26 },
    { zero := BitVec.ofNat 26 29354253, component := 26 },
    { zero := BitVec.ofNat 26 33532173, component := 26 },
    { zero := BitVec.ofNat 26 59858917, component := 3 },
    { zero := BitVec.ofNat 26 60411877, component := 3 },
    { zero := BitVec.ofNat 26 62086117, component := 18 },
    { zero := BitVec.ofNat 26 62639077, component := 18 },
    { zero := BitVec.ofNat 26 60120421, component := 4 },
    { zero := BitVec.ofNat 26 60673381, component := 4 },
    { zero := BitVec.ofNat 26 62347621, component := 4 },
    { zero := BitVec.ofNat 26 62900581, component := 4 },
    { zero := BitVec.ofNat 26 60128581, component := 4 },
    { zero := BitVec.ofNat 26 64306501, component := 1 },
    { zero := BitVec.ofNat 26 60681541, component := 4 },
    { zero := BitVec.ofNat 26 64859461, component := 16 },
    { zero := BitVec.ofNat 26 62355781, component := 4 },
    { zero := BitVec.ofNat 26 66533701, component := 62 },
    { zero := BitVec.ofNat 26 62908741, component := 4 },
    { zero := BitVec.ofNat 26 67086661, component := 17 },
    { zero := BitVec.ofNat 26 30515177, component := 26 },
    { zero := BitVec.ofNat 26 32742377, component := 52 },
    { zero := BitVec.ofNat 26 30776681, component := 37 },
    { zero := BitVec.ofNat 26 33003881, component := 49 },
    { zero := BitVec.ofNat 26 64561065, component := 26 },
    { zero := BitVec.ofNat 26 31035305, component := 33 },
    { zero := BitVec.ofNat 26 66788265, component := 52 },
    { zero := BitVec.ofNat 26 33262505, component := 42 },
    { zero := BitVec.ofNat 26 64822569, component := 26 },
    { zero := BitVec.ofNat 26 31296809, component := 7 },
    { zero := BitVec.ofNat 26 67049769, component := 26 },
    { zero := BitVec.ofNat 26 33524009, component := 26 },
    { zero := BitVec.ofNat 26 64036833, component := 26 },
    { zero := BitVec.ofNat 26 64589793, component := 33 },
    { zero := BitVec.ofNat 26 66264033, component := 52 },
    { zero := BitVec.ofNat 26 66816993, component := 42 },
    { zero := BitVec.ofNat 26 64298337, component := 0 },
    { zero := BitVec.ofNat 26 64851297, component := 37 },
    { zero := BitVec.ofNat 26 66525537, component := 49 },
    { zero := BitVec.ofNat 26 67078497, component := 26 },
    { zero := BitVec.ofNat 26 18087886, component := 38 },
    { zero := BitVec.ofNat 26 22265806, component := 38 },
    { zero := BitVec.ofNat 26 18349518, component := 38 },
    { zero := BitVec.ofNat 26 22527438, component := 38 },
    { zero := BitVec.ofNat 26 28442318, component := 38 },
    { zero := BitVec.ofNat 26 32620238, component := 38 },
    { zero := BitVec.ofNat 26 20183758, component := 66 },
    { zero := BitVec.ofNat 26 24361678, component := 60 },
    { zero := BitVec.ofNat 26 28703950, component := 38 },
    { zero := BitVec.ofNat 26 32881870, component := 38 },
    { zero := BitVec.ofNat 26 20445390, component := 61 },
    { zero := BitVec.ofNat 26 24623310, component := 59 },
    { zero := BitVec.ofNat 26 52133774, component := 63 },
    { zero := BitVec.ofNat 26 56311694, component := 59 },
    { zero := BitVec.ofNat 26 18608014, component := 26 },
    { zero := BitVec.ofNat 26 22785934, component := 36 },
    { zero := BitVec.ofNat 26 52395406, component := 56 },
    { zero := BitVec.ofNat 26 56573326, component := 59 },
    { zero := BitVec.ofNat 26 18869646, component := 26 },
    { zero := BitVec.ofNat 26 23047566, component := 36 },
    { zero := BitVec.ofNat 26 62488206, component := 20 },
    { zero := BitVec.ofNat 26 66666126, component := 20 },
    { zero := BitVec.ofNat 26 28962446, component := 20 },
    { zero := BitVec.ofNat 26 33140366, component := 20 },
    { zero := BitVec.ofNat 26 54229646, component := 65 },
    { zero := BitVec.ofNat 26 58407566, component := 60 },
    { zero := BitVec.ofNat 26 20703886, component := 26 },
    { zero := BitVec.ofNat 26 24881806, component := 29 },
    { zero := BitVec.ofNat 26 62749838, component := 6 },
    { zero := BitVec.ofNat 26 66927758, component := 26 },
    { zero := BitVec.ofNat 26 29224078, component := 19 },
    { zero := BitVec.ofNat 26 33401998, component := 19 },
    { zero := BitVec.ofNat 26 54491278, component := 56 },
    { zero := BitVec.ofNat 26 58669198, component := 59 },
    { zero := BitVec.ofNat 26 20965518, component := 26 },
    { zero := BitVec.ofNat 26 25143438, component := 28 },
    { zero := BitVec.ofNat 26 51609542, component := 58 },
    { zero := BitVec.ofNat 26 55787462, component := 61 },
    { zero := BitVec.ofNat 26 52162502, component := 38 },
    { zero := BitVec.ofNat 26 56340422, component := 38 },
    { zero := BitVec.ofNat 26 51871174, component := 57 },
    { zero := BitVec.ofNat 26 56049094, component := 62 },
    { zero := BitVec.ofNat 26 52424134, component := 38 },
    { zero := BitVec.ofNat 26 56602054, component := 38 },
    { zero := BitVec.ofNat 26 61963974, component := 24 },
    { zero := BitVec.ofNat 26 66141894, component := 41 },
    { zero := BitVec.ofNat 26 62516934, component := 20 },
    { zero := BitVec.ofNat 26 66694854, component := 20 },
    { zero := BitVec.ofNat 26 53705414, component := 58 },
    { zero := BitVec.ofNat 26 57883334, component := 66 },
    { zero := BitVec.ofNat 26 54258374, component := 24 },
    { zero := BitVec.ofNat 26 58436294, component := 41 },
    { zero := BitVec.ofNat 26 62225606, component := 24 },
    { zero := BitVec.ofNat 26 66403526, component := 26 },
    { zero := BitVec.ofNat 26 62778566, component := 38 },
    { zero := BitVec.ofNat 26 66956486, component := 38 },
    { zero := BitVec.ofNat 26 53967046, component := 58 },
    { zero := BitVec.ofNat 26 58144966, component := 54 },
    { zero := BitVec.ofNat 26 54520006, component := 24 },
    { zero := BitVec.ofNat 26 58697926, component := 26 },
    { zero := BitVec.ofNat 26 22265834, component := 59 },
    { zero := BitVec.ofNat 26 22527466, component := 59 },
    { zero := BitVec.ofNat 26 32620266, component := 36 },
    { zero := BitVec.ofNat 26 24361706, component := 60 },
    { zero := BitVec.ofNat 26 32881898, component := 36 },
    { zero := BitVec.ofNat 26 24623338, component := 59 },
    { zero := BitVec.ofNat 26 56311722, component := 59 },
    { zero := BitVec.ofNat 26 22785962, component := 32 },
    { zero := BitVec.ofNat 26 56573354, component := 59 },
    { zero := BitVec.ofNat 26 23047594, component := 32 },
    { zero := BitVec.ofNat 26 66666154, component := 30 },
    { zero := BitVec.ofNat 26 33140394, component := 32 },
    { zero := BitVec.ofNat 26 58407594, component := 60 },
    { zero := BitVec.ofNat 26 24881834, component := 30 },
    { zero := BitVec.ofNat 26 66927786, component := 31 },
    { zero := BitVec.ofNat 26 33402026, component := 32 },
    { zero := BitVec.ofNat 26 58669226, component := 59 },
    { zero := BitVec.ofNat 26 25143466, component := 28 },
    { zero := BitVec.ofNat 26 55787490, component := 26 },
    { zero := BitVec.ofNat 26 56340450, component := 33 },
    { zero := BitVec.ofNat 26 56049122, component := 62 },
    { zero := BitVec.ofNat 26 56602082, component := 37 },
    { zero := BitVec.ofNat 26 66141922, component := 26 },
    { zero := BitVec.ofNat 26 66694882, component := 42 },
    { zero := BitVec.ofNat 26 57883362, component := 65 },
    { zero := BitVec.ofNat 26 58436322, component := 42 },
    { zero := BitVec.ofNat 26 66403554, component := 26 },
    { zero := BitVec.ofNat 26 66956514, component := 33 },
    { zero := BitVec.ofNat 26 58144994, component := 54 },
    { zero := BitVec.ofNat 26 58697954, component := 26 },
    { zero := BitVec.ofNat 26 26345420, component := 26 },
    { zero := BitVec.ofNat 26 30523340, component := 26 },
    { zero := BitVec.ofNat 26 28572620, component := 63 },
    { zero := BitVec.ofNat 26 32750540, component := 65 },
    { zero := BitVec.ofNat 26 26607052, component := 37 },
    { zero := BitVec.ofNat 26 30784972, component := 37 },
    { zero := BitVec.ofNat 26 28834252, component := 62 },
    { zero := BitVec.ofNat 26 33012172, component := 62 },
    { zero := BitVec.ofNat 26 60391308, component := 12 },
    { zero := BitVec.ofNat 26 64569228, component := 26 },
    { zero := BitVec.ofNat 26 26865548, component := 12 },
    { zero := BitVec.ofNat 26 31043468, component := 19 },
    { zero := BitVec.ofNat 26 62618508, component := 12 },
    { zero := BitVec.ofNat 26 66796428, component := 20 },
    { zero := BitVec.ofNat 26 29092748, component := 12 },
    { zero := BitVec.ofNat 26 33270668, component := 20 },
    { zero := BitVec.ofNat 26 60652940, component := 6 },
    { zero := BitVec.ofNat 26 64830860, component := 26 },
    { zero := BitVec.ofNat 26 27127180, component := 19 },
    { zero := BitVec.ofNat 26 31305100, component := 8 },
    { zero := BitVec.ofNat 26 62880140, component := 6 },
    { zero := BitVec.ofNat 26 67058060, component := 26 },
    { zero := BitVec.ofNat 26 29354380, component := 26 },
    { zero := BitVec.ofNat 26 33532300, component := 26 },
    { zero := BitVec.ofNat 26 59867076, component := 26 },
    { zero := BitVec.ofNat 26 64044996, component := 26 },
    { zero := BitVec.ofNat 26 60420036, component := 6 },
    { zero := BitVec.ofNat 26 64597956, component := 19 },
    { zero := BitVec.ofNat 26 62094276, component := 65 },
    { zero := BitVec.ofNat 26 66272196, component := 65 },
    { zero := BitVec.ofNat 26 62647236, component := 20 },
    { zero := BitVec.ofNat 26 66825156, component := 20 },
    { zero := BitVec.ofNat 26 60128708, component := 23 },
    { zero := BitVec.ofNat 26 64306628, component := 1 },
    { zero := BitVec.ofNat 26 60681668, component := 6 },
    { zero := BitVec.ofNat 26 64859588, component := 19 },
    { zero := BitVec.ofNat 26 62355908, component := 57 },
    { zero := BitVec.ofNat 26 66533828, component := 62 },
    { zero := BitVec.ofNat 26 62908868, component := 6 },
    { zero := BitVec.ofNat 26 67086788, component := 26 },
    { zero := BitVec.ofNat 26 30523368, component := 26 },
    { zero := BitVec.ofNat 26 32750568, component := 65 },
    { zero := BitVec.ofNat 26 30785000, component := 37 },
    { zero := BitVec.ofNat 26 33012200, component := 62 },
    { zero := BitVec.ofNat 26 64569256, component := 26 },
    { zero := BitVec.ofNat 26 31043496, component := 33 },
    { zero := BitVec.ofNat 26 66796456, component := 42 },
    { zero := BitVec.ofNat 26 33270696, component := 42 },
    { zero := BitVec.ofNat 26 64830888, component := 26 },
    { zero := BitVec.ofNat 26 31305128, component := 8 },
    { zero := BitVec.ofNat 26 67058088, component := 26 },
    { zero := BitVec.ofNat 26 33532328, component := 26 },
    { zero := BitVec.ofNat 26 64045024, component := 26 },
    { zero := BitVec.ofNat 26 64597984, component := 33 },
    { zero := BitVec.ofNat 26 66272224, component := 65 },
    { zero := BitVec.ofNat 26 66825184, component := 42 },
    { zero := BitVec.ofNat 26 64306656, component := 1 },
    { zero := BitVec.ofNat 26 64859616, component := 37 },
    { zero := BitVec.ofNat 26 66533856, component := 62 },
    { zero := BitVec.ofNat 26 67086816, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover1 : ActiveCover := {
  active := BitVec.ofNat 14 1
  strata := [
    { zero := BitVec.ofNat 26 22527306, component := 59 },
    { zero := BitVec.ofNat 26 32881738, component := 36 },
    { zero := BitVec.ofNat 26 24623178, component := 59 },
    { zero := BitVec.ofNat 26 56573194, component := 59 },
    { zero := BitVec.ofNat 26 23047434, component := 36 },
    { zero := BitVec.ofNat 26 66927626, component := 26 },
    { zero := BitVec.ofNat 26 33401866, component := 36 },
    { zero := BitVec.ofNat 26 58669066, component := 59 },
    { zero := BitVec.ofNat 26 25143306, component := 28 },
    { zero := BitVec.ofNat 26 56048962, component := 62 },
    { zero := BitVec.ofNat 26 56601922, component := 37 },
    { zero := BitVec.ofNat 26 66403394, component := 26 },
    { zero := BitVec.ofNat 26 66956354, component := 26 },
    { zero := BitVec.ofNat 26 58144834, component := 54 },
    { zero := BitVec.ofNat 26 58697794, component := 26 },
    { zero := BitVec.ofNat 26 30784840, component := 37 },
    { zero := BitVec.ofNat 26 33012040, component := 62 },
    { zero := BitVec.ofNat 26 64830728, component := 26 },
    { zero := BitVec.ofNat 26 31304968, component := 8 },
    { zero := BitVec.ofNat 26 67057928, component := 26 },
    { zero := BitVec.ofNat 26 33532168, component := 26 },
    { zero := BitVec.ofNat 26 64306496, component := 1 },
    { zero := BitVec.ofNat 26 64859456, component := 37 },
    { zero := BitVec.ofNat 26 66533696, component := 62 },
    { zero := BitVec.ofNat 26 67086656, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover2 : ActiveCover := {
  active := BitVec.ofNat 14 2
  strata := [
    { zero := BitVec.ofNat 26 17948654, component := 38 },
    { zero := BitVec.ofNat 26 18210286, component := 38 },
    { zero := BitVec.ofNat 26 20045550, component := 38 },
    { zero := BitVec.ofNat 26 20307182, component := 38 },
    { zero := BitVec.ofNat 26 51994542, component := 39 },
    { zero := BitVec.ofNat 26 18468782, component := 39 },
    { zero := BitVec.ofNat 26 52256174, component := 25 },
    { zero := BitVec.ofNat 26 18730414, component := 33 },
    { zero := BitVec.ofNat 26 54091438, component := 42 },
    { zero := BitVec.ofNat 26 20565678, component := 42 },
    { zero := BitVec.ofNat 26 54353070, component := 25 },
    { zero := BitVec.ofNat 26 20827310, component := 33 },
    { zero := BitVec.ofNat 26 51470310, component := 24 },
    { zero := BitVec.ofNat 26 52023270, component := 38 },
    { zero := BitVec.ofNat 26 51731942, component := 24 },
    { zero := BitVec.ofNat 26 52284902, component := 38 },
    { zero := BitVec.ofNat 26 53567206, component := 24 },
    { zero := BitVec.ofNat 26 54120166, component := 38 },
    { zero := BitVec.ofNat 26 53828838, component := 24 },
    { zero := BitVec.ofNat 26 54381798, component := 38 },
    { zero := BitVec.ofNat 26 22126570, component := 36 },
    { zero := BitVec.ofNat 26 22388202, component := 36 },
    { zero := BitVec.ofNat 26 24223466, component := 36 },
    { zero := BitVec.ofNat 26 24485098, component := 36 },
    { zero := BitVec.ofNat 26 56172458, component := 31 },
    { zero := BitVec.ofNat 26 22646698, component := 32 },
    { zero := BitVec.ofNat 26 56434090, component := 31 },
    { zero := BitVec.ofNat 26 22908330, component := 32 },
    { zero := BitVec.ofNat 26 58269354, component := 30 },
    { zero := BitVec.ofNat 26 24743594, component := 32 },
    { zero := BitVec.ofNat 26 58530986, component := 31 },
    { zero := BitVec.ofNat 26 25005226, component := 32 },
    { zero := BitVec.ofNat 26 55648226, component := 26 },
    { zero := BitVec.ofNat 26 56201186, component := 33 },
    { zero := BitVec.ofNat 26 55909858, component := 26 },
    { zero := BitVec.ofNat 26 56462818, component := 37 },
    { zero := BitVec.ofNat 26 57745122, component := 26 },
    { zero := BitVec.ofNat 26 58298082, component := 42 },
    { zero := BitVec.ofNat 26 58006754, component := 26 },
    { zero := BitVec.ofNat 26 58559714, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover3 : ActiveCover := {
  active := BitVec.ofNat 14 4
  strata := [
    { zero := BitVec.ofNat 26 62480037, component := 18 },
    { zero := BitVec.ofNat 26 62508709, component := 18 },
    { zero := BitVec.ofNat 26 62610085, component := 18 },
    { zero := BitVec.ofNat 26 62638757, component := 18 },
    { zero := BitVec.ofNat 26 62741541, component := 3 },
    { zero := BitVec.ofNat 26 62770213, component := 3 },
    { zero := BitVec.ofNat 26 62871589, component := 3 },
    { zero := BitVec.ofNat 26 62900261, component := 3 },
    { zero := BitVec.ofNat 26 62749701, component := 3 },
    { zero := BitVec.ofNat 26 66927621, component := 26 },
    { zero := BitVec.ofNat 26 62778373, component := 3 },
    { zero := BitVec.ofNat 26 66956293, component := 15 },
    { zero := BitVec.ofNat 26 62879749, component := 3 },
    { zero := BitVec.ofNat 26 67057669, component := 26 },
    { zero := BitVec.ofNat 26 62908421, component := 3 },
    { zero := BitVec.ofNat 26 67086341, component := 26 },
    { zero := BitVec.ofNat 26 66657953, component := 42 },
    { zero := BitVec.ofNat 26 66686625, component := 42 },
    { zero := BitVec.ofNat 26 66788001, component := 52 },
    { zero := BitVec.ofNat 26 66816673, component := 42 },
    { zero := BitVec.ofNat 26 66919457, component := 26 },
    { zero := BitVec.ofNat 26 66948129, component := 26 },
    { zero := BitVec.ofNat 26 67049505, component := 26 },
    { zero := BitVec.ofNat 26 67078177, component := 26 },
    { zero := BitVec.ofNat 26 62488196, component := 20 },
    { zero := BitVec.ofNat 26 66666116, component := 20 },
    { zero := BitVec.ofNat 26 62516868, component := 20 },
    { zero := BitVec.ofNat 26 66694788, component := 20 },
    { zero := BitVec.ofNat 26 62618244, component := 20 },
    { zero := BitVec.ofNat 26 66796164, component := 20 },
    { zero := BitVec.ofNat 26 62646916, component := 20 },
    { zero := BitVec.ofNat 26 66824836, component := 20 },
    { zero := BitVec.ofNat 26 62749828, component := 6 },
    { zero := BitVec.ofNat 26 66927748, component := 26 },
    { zero := BitVec.ofNat 26 62778500, component := 6 },
    { zero := BitVec.ofNat 26 66956420, component := 19 },
    { zero := BitVec.ofNat 26 62879876, component := 6 },
    { zero := BitVec.ofNat 26 67057796, component := 26 },
    { zero := BitVec.ofNat 26 62908548, component := 6 },
    { zero := BitVec.ofNat 26 67086468, component := 26 },
    { zero := BitVec.ofNat 26 66666144, component := 42 },
    { zero := BitVec.ofNat 26 66694816, component := 42 },
    { zero := BitVec.ofNat 26 66796192, component := 42 },
    { zero := BitVec.ofNat 26 66824864, component := 42 },
    { zero := BitVec.ofNat 26 66927776, component := 26 },
    { zero := BitVec.ofNat 26 66956448, component := 33 },
    { zero := BitVec.ofNat 26 67057824, component := 26 },
    { zero := BitVec.ofNat 26 67086496, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover4 : ActiveCover := {
  active := BitVec.ofNat 14 5
  strata := [
    { zero := BitVec.ofNat 26 66927616, component := 26 },
    { zero := BitVec.ofNat 26 66956288, component := 26 },
    { zero := BitVec.ofNat 26 67057664, component := 26 },
    { zero := BitVec.ofNat 26 67086336, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover5 : ActiveCover := {
  active := BitVec.ofNat 14 8
  strata := [
    { zero := BitVec.ofNat 26 18079721, component := 50 },
    { zero := BitVec.ofNat 26 20175849, component := 50 },
    { zero := BitVec.ofNat 26 18341225, component := 49 },
    { zero := BitVec.ofNat 26 20437353, component := 49 },
    { zero := BitVec.ofNat 26 52125609, component := 50 },
    { zero := BitVec.ofNat 26 18599849, component := 39 },
    { zero := BitVec.ofNat 26 54221737, component := 50 },
    { zero := BitVec.ofNat 26 20695977, component := 39 },
    { zero := BitVec.ofNat 26 52387113, component := 45 },
    { zero := BitVec.ofNat 26 18861353, component := 26 },
    { zero := BitVec.ofNat 26 54483241, component := 45 },
    { zero := BitVec.ofNat 26 20957481, component := 26 },
    { zero := BitVec.ofNat 26 51601377, component := 45 },
    { zero := BitVec.ofNat 26 52154337, component := 25 },
    { zero := BitVec.ofNat 26 53697505, component := 52 },
    { zero := BitVec.ofNat 26 54250465, component := 42 },
    { zero := BitVec.ofNat 26 51862881, component := 46 },
    { zero := BitVec.ofNat 26 52415841, component := 37 },
    { zero := BitVec.ofNat 26 53959009, component := 46 },
    { zero := BitVec.ofNat 26 54511969, component := 23 },
    { zero := BitVec.ofNat 26 18087912, component := 63 },
    { zero := BitVec.ofNat 26 20184040, component := 63 },
    { zero := BitVec.ofNat 26 18349544, component := 62 },
    { zero := BitVec.ofNat 26 20445672, component := 62 },
    { zero := BitVec.ofNat 26 52133800, component := 63 },
    { zero := BitVec.ofNat 26 18608040, component := 39 },
    { zero := BitVec.ofNat 26 54229928, component := 63 },
    { zero := BitVec.ofNat 26 20704168, component := 39 },
    { zero := BitVec.ofNat 26 52395432, component := 25 },
    { zero := BitVec.ofNat 26 18869672, component := 33 },
    { zero := BitVec.ofNat 26 54491560, component := 25 },
    { zero := BitVec.ofNat 26 20965800, component := 26 },
    { zero := BitVec.ofNat 26 51609568, component := 56 },
    { zero := BitVec.ofNat 26 52162528, component := 25 },
    { zero := BitVec.ofNat 26 53705696, component := 65 },
    { zero := BitVec.ofNat 26 54258656, component := 42 },
    { zero := BitVec.ofNat 26 51871200, component := 57 },
    { zero := BitVec.ofNat 26 52424160, component := 37 },
    { zero := BitVec.ofNat 26 53967328, component := 57 },
    { zero := BitVec.ofNat 26 54520288, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover6 : ActiveCover := {
  active := BitVec.ofNat 14 9
  strata := [
    { zero := BitVec.ofNat 26 18349384, component := 62 },
    { zero := BitVec.ofNat 26 20445512, component := 62 },
    { zero := BitVec.ofNat 26 52395272, component := 56 },
    { zero := BitVec.ofNat 26 18869512, component := 26 },
    { zero := BitVec.ofNat 26 54491400, component := 56 },
    { zero := BitVec.ofNat 26 20965640, component := 26 },
    { zero := BitVec.ofNat 26 51871040, component := 57 },
    { zero := BitVec.ofNat 26 52424000, component := 37 },
    { zero := BitVec.ofNat 26 53967168, component := 57 },
    { zero := BitVec.ofNat 26 54520128, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover7 : ActiveCover := {
  active := BitVec.ofNat 14 10
  strata := [
    { zero := BitVec.ofNat 26 17948648, component := 26 },
    { zero := BitVec.ofNat 26 18210280, component := 37 },
    { zero := BitVec.ofNat 26 51994536, component := 39 },
    { zero := BitVec.ofNat 26 18468776, component := 39 },
    { zero := BitVec.ofNat 26 52256168, component := 25 },
    { zero := BitVec.ofNat 26 18730408, component := 33 },
    { zero := BitVec.ofNat 26 51470304, component := 26 },
    { zero := BitVec.ofNat 26 52023264, component := 25 },
    { zero := BitVec.ofNat 26 51731936, component := 23 },
    { zero := BitVec.ofNat 26 52284896, component := 37 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover8 : ActiveCover := {
  active := BitVec.ofNat 14 12
  strata := [
    { zero := BitVec.ofNat 26 54221473, component := 52 },
    { zero := BitVec.ofNat 26 54250145, component := 42 },
    { zero := BitVec.ofNat 26 54482977, component := 45 },
    { zero := BitVec.ofNat 26 54511649, component := 26 },
    { zero := BitVec.ofNat 26 54229664, component := 42 },
    { zero := BitVec.ofNat 26 54258336, component := 42 },
    { zero := BitVec.ofNat 26 54491296, component := 25 },
    { zero := BitVec.ofNat 26 54519968, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover9 : ActiveCover := {
  active := BitVec.ofNat 14 13
  strata := [
    { zero := BitVec.ofNat 26 54491136, component := 56 },
    { zero := BitVec.ofNat 26 54519808, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover10 : ActiveCover := {
  active := BitVec.ofNat 14 14
  strata := [
    { zero := BitVec.ofNat 26 54091424, component := 42 },
    { zero := BitVec.ofNat 26 54120096, component := 42 },
    { zero := BitVec.ofNat 26 54353056, component := 25 },
    { zero := BitVec.ofNat 26 54381728, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover11 : ActiveCover := {
  active := BitVec.ofNat 14 64
  strata := [
    { zero := BitVec.ofNat 26 18075599, component := 38 },
    { zero := BitVec.ofNat 26 22253519, component := 38 },
    { zero := BitVec.ofNat 26 28430031, component := 38 },
    { zero := BitVec.ofNat 26 32607951, component := 38 },
    { zero := BitVec.ofNat 26 20171471, component := 41 },
    { zero := BitVec.ofNat 26 24349391, component := 41 },
    { zero := BitVec.ofNat 26 18337103, component := 37 },
    { zero := BitVec.ofNat 26 22515023, component := 36 },
    { zero := BitVec.ofNat 26 28691535, component := 15 },
    { zero := BitVec.ofNat 26 32869455, component := 36 },
    { zero := BitVec.ofNat 26 20432975, component := 26 },
    { zero := BitVec.ofNat 26 24610895, component := 26 },
    { zero := BitVec.ofNat 26 51630023, component := 38 },
    { zero := BitVec.ofNat 26 55807943, component := 38 },
    { zero := BitVec.ofNat 26 61984455, component := 38 },
    { zero := BitVec.ofNat 26 66162375, component := 38 },
    { zero := BitVec.ofNat 26 53725895, component := 24 },
    { zero := BitVec.ofNat 26 57903815, component := 41 },
    { zero := BitVec.ofNat 26 51891527, component := 37 },
    { zero := BitVec.ofNat 26 56069447, component := 37 },
    { zero := BitVec.ofNat 26 62245959, component := 3 },
    { zero := BitVec.ofNat 26 66423879, component := 15 },
    { zero := BitVec.ofNat 26 53987399, component := 26 },
    { zero := BitVec.ofNat 26 58165319, component := 26 },
    { zero := BitVec.ofNat 26 26333133, component := 9 },
    { zero := BitVec.ofNat 26 30511053, component := 15 },
    { zero := BitVec.ofNat 26 28560333, component := 9 },
    { zero := BitVec.ofNat 26 32738253, component := 18 },
    { zero := BitVec.ofNat 26 26594637, component := 16 },
    { zero := BitVec.ofNat 26 30772557, component := 16 },
    { zero := BitVec.ofNat 26 28821837, component := 17 },
    { zero := BitVec.ofNat 26 32999757, component := 17 },
    { zero := BitVec.ofNat 26 59887557, component := 3 },
    { zero := BitVec.ofNat 26 64065477, component := 15 },
    { zero := BitVec.ofNat 26 62114757, component := 18 },
    { zero := BitVec.ofNat 26 66292677, component := 18 },
    { zero := BitVec.ofNat 26 60149061, component := 4 },
    { zero := BitVec.ofNat 26 64326981, component := 16 },
    { zero := BitVec.ofNat 26 62376261, component := 4 },
    { zero := BitVec.ofNat 26 66554181, component := 17 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover12 : ActiveCover := {
  active := BitVec.ofNat 14 66
  strata := [
    { zero := BitVec.ofNat 26 17944526, component := 38 },
    { zero := BitVec.ofNat 26 22122446, component := 38 },
    { zero := BitVec.ofNat 26 18206158, component := 38 },
    { zero := BitVec.ofNat 26 22384078, component := 38 },
    { zero := BitVec.ofNat 26 20041422, component := 38 },
    { zero := BitVec.ofNat 26 24219342, component := 38 },
    { zero := BitVec.ofNat 26 20303054, component := 38 },
    { zero := BitVec.ofNat 26 24480974, component := 38 },
    { zero := BitVec.ofNat 26 51498950, component := 38 },
    { zero := BitVec.ofNat 26 55676870, component := 38 },
    { zero := BitVec.ofNat 26 51760582, component := 38 },
    { zero := BitVec.ofNat 26 55938502, component := 38 },
    { zero := BitVec.ofNat 26 53595846, component := 38 },
    { zero := BitVec.ofNat 26 57773766, component := 38 },
    { zero := BitVec.ofNat 26 53857478, component := 38 },
    { zero := BitVec.ofNat 26 58035398, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover13 : ActiveCover := {
  active := BitVec.ofNat 14 67
  strata := [
    { zero := BitVec.ofNat 26 22383946, component := 36 },
    { zero := BitVec.ofNat 26 24480842, component := 36 },
    { zero := BitVec.ofNat 26 55938370, component := 37 },
    { zero := BitVec.ofNat 26 58035266, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover14 : ActiveCover := {
  active := BitVec.ofNat 14 75
  strata := [
    { zero := BitVec.ofNat 26 18206024, component := 37 },
    { zero := BitVec.ofNat 26 51760448, component := 37 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover15 : ActiveCover := {
  active := BitVec.ofNat 14 128
  strata := [
    { zero := BitVec.ofNat 26 18079535, component := 50 },
    { zero := BitVec.ofNat 26 51601199, component := 50 },
    { zero := BitVec.ofNat 26 28433967, component := 18 },
    { zero := BitVec.ofNat 26 61955631, component := 18 },
    { zero := BitVec.ofNat 26 20175407, component := 52 },
    { zero := BitVec.ofNat 26 53697071, component := 52 },
    { zero := BitVec.ofNat 26 18087695, component := 63 },
    { zero := BitVec.ofNat 26 51609359, component := 63 },
    { zero := BitVec.ofNat 26 22265615, component := 59 },
    { zero := BitVec.ofNat 26 55787279, component := 59 },
    { zero := BitVec.ofNat 26 28442127, component := 18 },
    { zero := BitVec.ofNat 26 61963791, component := 18 },
    { zero := BitVec.ofNat 26 32620047, component := 18 },
    { zero := BitVec.ofNat 26 66141711, component := 18 },
    { zero := BitVec.ofNat 26 20183567, component := 65 },
    { zero := BitVec.ofNat 26 53705231, component := 65 },
    { zero := BitVec.ofNat 26 24361487, component := 60 },
    { zero := BitVec.ofNat 26 57883151, component := 60 },
    { zero := BitVec.ofNat 26 22257451, component := 47 },
    { zero := BitVec.ofNat 26 55779115, component := 47 },
    { zero := BitVec.ofNat 26 32611883, component := 36 },
    { zero := BitVec.ofNat 26 66133547, component := 29 },
    { zero := BitVec.ofNat 26 24353323, component := 48 },
    { zero := BitVec.ofNat 26 57874987, component := 48 },
    { zero := BitVec.ofNat 26 26337069, component := 9 },
    { zero := BitVec.ofNat 26 59858733, component := 9 },
    { zero := BitVec.ofNat 26 28564269, component := 50 },
    { zero := BitVec.ofNat 26 62085933, component := 50 },
    { zero := BitVec.ofNat 26 26345229, component := 9 },
    { zero := BitVec.ofNat 26 59866893, component := 9 },
    { zero := BitVec.ofNat 26 30523149, component := 15 },
    { zero := BitVec.ofNat 26 64044813, component := 26 },
    { zero := BitVec.ofNat 26 28572429, component := 63 },
    { zero := BitVec.ofNat 26 62094093, component := 63 },
    { zero := BitVec.ofNat 26 32750349, component := 18 },
    { zero := BitVec.ofNat 26 66272013, component := 18 },
    { zero := BitVec.ofNat 26 30514985, component := 26 },
    { zero := BitVec.ofNat 26 64036649, component := 26 },
    { zero := BitVec.ofNat 26 32742185, component := 52 },
    { zero := BitVec.ofNat 26 66263849, component := 52 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover16 : ActiveCover := {
  active := BitVec.ofNat 14 129
  strata := [
    { zero := BitVec.ofNat 26 22265610, component := 59 },
    { zero := BitVec.ofNat 26 55787274, component := 59 },
    { zero := BitVec.ofNat 26 32620042, component := 36 },
    { zero := BitVec.ofNat 26 66141706, component := 29 },
    { zero := BitVec.ofNat 26 24361482, component := 60 },
    { zero := BitVec.ofNat 26 57883146, component := 60 },
    { zero := BitVec.ofNat 26 30523144, component := 26 },
    { zero := BitVec.ofNat 26 64044808, component := 26 },
    { zero := BitVec.ofNat 26 32750344, component := 65 },
    { zero := BitVec.ofNat 26 66272008, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover17 : ActiveCover := {
  active := BitVec.ofNat 14 132
  strata := [
    { zero := BitVec.ofNat 26 61955621, component := 18 },
    { zero := BitVec.ofNat 26 62085669, component := 18 },
    { zero := BitVec.ofNat 26 61963781, component := 18 },
    { zero := BitVec.ofNat 26 66141701, component := 18 },
    { zero := BitVec.ofNat 26 62093829, component := 18 },
    { zero := BitVec.ofNat 26 66271749, component := 18 },
    { zero := BitVec.ofNat 26 66133537, component := 26 },
    { zero := BitVec.ofNat 26 66263585, component := 52 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover18 : ActiveCover := {
  active := BitVec.ofNat 14 133
  strata := [
    { zero := BitVec.ofNat 26 66141696, component := 26 },
    { zero := BitVec.ofNat 26 66271744, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover19 : ActiveCover := {
  active := BitVec.ofNat 14 136
  strata := [
    { zero := BitVec.ofNat 26 18079529, component := 50 },
    { zero := BitVec.ofNat 26 51601193, component := 50 },
    { zero := BitVec.ofNat 26 20175657, component := 50 },
    { zero := BitVec.ofNat 26 53697321, component := 50 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover20 : ActiveCover := {
  active := BitVec.ofNat 14 137
  strata := [
    { zero := BitVec.ofNat 26 18087688, component := 63 },
    { zero := BitVec.ofNat 26 51609352, component := 63 },
    { zero := BitVec.ofNat 26 20183816, component := 63 },
    { zero := BitVec.ofNat 26 53705480, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover21 : ActiveCover := {
  active := BitVec.ofNat 14 140
  strata := [
    { zero := BitVec.ofNat 26 53697057, component := 52 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover22 : ActiveCover := {
  active := BitVec.ofNat 14 141
  strata := [
    { zero := BitVec.ofNat 26 53705216, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover23 : ActiveCover := {
  active := BitVec.ofNat 14 192
  strata := [
    { zero := BitVec.ofNat 26 18075407, component := 26 },
    { zero := BitVec.ofNat 26 22253327, component := 36 },
    { zero := BitVec.ofNat 26 28429839, component := 18 },
    { zero := BitVec.ofNat 26 32607759, component := 18 },
    { zero := BitVec.ofNat 26 20171279, component := 26 },
    { zero := BitVec.ofNat 26 24349199, component := 29 },
    { zero := BitVec.ofNat 26 26332941, component := 9 },
    { zero := BitVec.ofNat 26 30510861, component := 15 },
    { zero := BitVec.ofNat 26 28560141, component := 9 },
    { zero := BitVec.ofNat 26 32738061, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover24 : ActiveCover := {
  active := BitVec.ofNat 14 195
  strata := [
    { zero := BitVec.ofNat 26 22122250, component := 36 },
    { zero := BitVec.ofNat 26 24219146, component := 36 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover25 : ActiveCover := {
  active := BitVec.ofNat 14 196
  strata := [
    { zero := BitVec.ofNat 26 61984261, component := 18 },
    { zero := BitVec.ofNat 26 66162181, component := 18 },
    { zero := BitVec.ofNat 26 62114309, component := 18 },
    { zero := BitVec.ofNat 26 66292229, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover26 : ActiveCover := {
  active := BitVec.ofNat 14 203
  strata := [
    { zero := BitVec.ofNat 26 17944328, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover27 : ActiveCover := {
  active := BitVec.ofNat 14 207
  strata := [
    { zero := BitVec.ofNat 26 53595648, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover28 : ActiveCover := {
  active := BitVec.ofNat 14 512
  strata := [
    { zero := BitVec.ofNat 26 17030655, component := 38 },
    { zero := BitVec.ofNat 26 27385087, component := 38 },
    { zero := BitVec.ofNat 26 19126527, component := 26 },
    { zero := BitVec.ofNat 26 51076543, component := 51 },
    { zero := BitVec.ofNat 26 17550783, component := 34 },
    { zero := BitVec.ofNat 26 61430975, component := 2 },
    { zero := BitVec.ofNat 26 27905215, component := 15 },
    { zero := BitVec.ofNat 26 53172415, component := 43 },
    { zero := BitVec.ofNat 26 19646655, component := 26 },
    { zero := BitVec.ofNat 26 50552311, component := 24 },
    { zero := BitVec.ofNat 26 51105271, component := 38 },
    { zero := BitVec.ofNat 26 60906743, component := 2 },
    { zero := BitVec.ofNat 26 61459703, component := 38 },
    { zero := BitVec.ofNat 26 52648183, component := 43 },
    { zero := BitVec.ofNat 26 53201143, component := 21 },
    { zero := BitVec.ofNat 26 21208571, component := 51 },
    { zero := BitVec.ofNat 26 31563003, component := 36 },
    { zero := BitVec.ofNat 26 23304443, component := 47 },
    { zero := BitVec.ofNat 26 55254459, component := 51 },
    { zero := BitVec.ofNat 26 21728699, component := 32 },
    { zero := BitVec.ofNat 26 65608891, component := 22 },
    { zero := BitVec.ofNat 26 32083131, component := 32 },
    { zero := BitVec.ofNat 26 57350331, component := 43 },
    { zero := BitVec.ofNat 26 23824571, component := 31 },
    { zero := BitVec.ofNat 26 54730227, component := 26 },
    { zero := BitVec.ofNat 26 55283187, component := 33 },
    { zero := BitVec.ofNat 26 65084659, component := 26 },
    { zero := BitVec.ofNat 26 65637619, component := 22 },
    { zero := BitVec.ofNat 26 56826099, component := 43 },
    { zero := BitVec.ofNat 26 57379059, component := 22 },
    { zero := BitVec.ofNat 26 25288189, component := 11 },
    { zero := BitVec.ofNat 26 27515389, component := 51 },
    { zero := BitVec.ofNat 26 59334077, component := 10 },
    { zero := BitVec.ofNat 26 25808317, component := 11 },
    { zero := BitVec.ofNat 26 61561277, component := 51 },
    { zero := BitVec.ofNat 26 28035517, component := 10 },
    { zero := BitVec.ofNat 26 58809845, component := 3 },
    { zero := BitVec.ofNat 26 59362805, component := 3 },
    { zero := BitVec.ofNat 26 61037045, component := 2 },
    { zero := BitVec.ofNat 26 61590005, component := 2 },
    { zero := BitVec.ofNat 26 29466105, component := 35 },
    { zero := BitVec.ofNat 26 31693305, component := 51 },
    { zero := BitVec.ofNat 26 63511993, component := 40 },
    { zero := BitVec.ofNat 26 29986233, component := 34 },
    { zero := BitVec.ofNat 26 65739193, component := 51 },
    { zero := BitVec.ofNat 26 32213433, component := 40 },
    { zero := BitVec.ofNat 26 62987761, component := 26 },
    { zero := BitVec.ofNat 26 63540721, component := 33 },
    { zero := BitVec.ofNat 26 65214961, component := 43 },
    { zero := BitVec.ofNat 26 65767921, component := 22 },
    { zero := BitVec.ofNat 26 17038814, component := 38 },
    { zero := BitVec.ofNat 26 21216734, component := 38 },
    { zero := BitVec.ofNat 26 27393246, component := 38 },
    { zero := BitVec.ofNat 26 31571166, component := 38 },
    { zero := BitVec.ofNat 26 19134686, component := 61 },
    { zero := BitVec.ofNat 26 23312606, component := 59 },
    { zero := BitVec.ofNat 26 51084702, component := 64 },
    { zero := BitVec.ofNat 26 55262622, component := 64 },
    { zero := BitVec.ofNat 26 17558942, component := 35 },
    { zero := BitVec.ofNat 26 21736862, component := 36 },
    { zero := BitVec.ofNat 26 61439134, component := 5 },
    { zero := BitVec.ofNat 26 65617054, component := 5 },
    { zero := BitVec.ofNat 26 27913374, component := 19 },
    { zero := BitVec.ofNat 26 32091294, component := 19 },
    { zero := BitVec.ofNat 26 53180574, component := 53 },
    { zero := BitVec.ofNat 26 57358494, component := 59 },
    { zero := BitVec.ofNat 26 19654814, component := 26 },
    { zero := BitVec.ofNat 26 23832734, component := 26 },
    { zero := BitVec.ofNat 26 50560470, component := 58 },
    { zero := BitVec.ofNat 26 54738390, component := 61 },
    { zero := BitVec.ofNat 26 51113430, component := 38 },
    { zero := BitVec.ofNat 26 55291350, component := 38 },
    { zero := BitVec.ofNat 26 60914902, component := 21 },
    { zero := BitVec.ofNat 26 65092822, component := 21 },
    { zero := BitVec.ofNat 26 61467862, component := 5 },
    { zero := BitVec.ofNat 26 65645782, component := 5 },
    { zero := BitVec.ofNat 26 52656342, component := 55 },
    { zero := BitVec.ofNat 26 56834262, component := 55 },
    { zero := BitVec.ofNat 26 53209302, component := 21 },
    { zero := BitVec.ofNat 26 57387222, component := 21 },
    { zero := BitVec.ofNat 26 21216762, component := 64 },
    { zero := BitVec.ofNat 26 31571194, component := 36 },
    { zero := BitVec.ofNat 26 23312634, component := 59 },
    { zero := BitVec.ofNat 26 55262650, component := 64 },
    { zero := BitVec.ofNat 26 21736890, component := 32 },
    { zero := BitVec.ofNat 26 65617082, component := 22 },
    { zero := BitVec.ofNat 26 32091322, component := 32 },
    { zero := BitVec.ofNat 26 57358522, component := 59 },
    { zero := BitVec.ofNat 26 23832762, component := 31 },
    { zero := BitVec.ofNat 26 54738418, component := 26 },
    { zero := BitVec.ofNat 26 55291378, component := 33 },
    { zero := BitVec.ofNat 26 65092850, component := 26 },
    { zero := BitVec.ofNat 26 65645810, component := 22 },
    { zero := BitVec.ofNat 26 56834290, component := 53 },
    { zero := BitVec.ofNat 26 57387250, component := 22 },
    { zero := BitVec.ofNat 26 25296348, component := 35 },
    { zero := BitVec.ofNat 26 29474268, component := 35 },
    { zero := BitVec.ofNat 26 27523548, component := 64 },
    { zero := BitVec.ofNat 26 31701468, component := 64 },
    { zero := BitVec.ofNat 26 59342236, component := 6 },
    { zero := BitVec.ofNat 26 63520156, component := 13 },
    { zero := BitVec.ofNat 26 25816476, component := 14 },
    { zero := BitVec.ofNat 26 29994396, component := 14 },
    { zero := BitVec.ofNat 26 61569436, component := 5 },
    { zero := BitVec.ofNat 26 65747356, component := 5 },
    { zero := BitVec.ofNat 26 28043676, component := 13 },
    { zero := BitVec.ofNat 26 32221596, component := 13 },
    { zero := BitVec.ofNat 26 58818004, component := 26 },
    { zero := BitVec.ofNat 26 62995924, component := 26 },
    { zero := BitVec.ofNat 26 59370964, component := 6 },
    { zero := BitVec.ofNat 26 63548884, component := 19 },
    { zero := BitVec.ofNat 26 61045204, component := 53 },
    { zero := BitVec.ofNat 26 65223124, component := 53 },
    { zero := BitVec.ofNat 26 61598164, component := 5 },
    { zero := BitVec.ofNat 26 65776084, component := 5 },
    { zero := BitVec.ofNat 26 29474296, component := 35 },
    { zero := BitVec.ofNat 26 31701496, component := 64 },
    { zero := BitVec.ofNat 26 63520184, component := 40 },
    { zero := BitVec.ofNat 26 29994424, component := 34 },
    { zero := BitVec.ofNat 26 65747384, component := 64 },
    { zero := BitVec.ofNat 26 32221624, component := 40 },
    { zero := BitVec.ofNat 26 62995952, component := 26 },
    { zero := BitVec.ofNat 26 63548912, component := 33 },
    { zero := BitVec.ofNat 26 65223152, component := 53 },
    { zero := BitVec.ofNat 26 65776112, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover29 : ActiveCover := {
  active := BitVec.ofNat 14 514
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover30 : ActiveCover := {
  active := BitVec.ofNat 14 516
  strata := [
    { zero := BitVec.ofNat 26 61430965, component := 2 },
    { zero := BitVec.ofNat 26 61459637, component := 2 },
    { zero := BitVec.ofNat 26 61561013, component := 2 },
    { zero := BitVec.ofNat 26 61589685, component := 2 },
    { zero := BitVec.ofNat 26 65608881, component := 22 },
    { zero := BitVec.ofNat 26 65637553, component := 22 },
    { zero := BitVec.ofNat 26 65738929, component := 43 },
    { zero := BitVec.ofNat 26 65767601, component := 22 },
    { zero := BitVec.ofNat 26 61439124, component := 5 },
    { zero := BitVec.ofNat 26 65617044, component := 5 },
    { zero := BitVec.ofNat 26 61467796, component := 5 },
    { zero := BitVec.ofNat 26 65645716, component := 5 },
    { zero := BitVec.ofNat 26 61569172, component := 5 },
    { zero := BitVec.ofNat 26 65747092, component := 5 },
    { zero := BitVec.ofNat 26 61597844, component := 5 },
    { zero := BitVec.ofNat 26 65775764, component := 5 },
    { zero := BitVec.ofNat 26 65617072, component := 22 },
    { zero := BitVec.ofNat 26 65645744, component := 22 },
    { zero := BitVec.ofNat 26 65747120, component := 22 },
    { zero := BitVec.ofNat 26 65775792, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover31 : ActiveCover := {
  active := BitVec.ofNat 14 520
  strata := [
    { zero := BitVec.ofNat 26 17030649, component := 51 },
    { zero := BitVec.ofNat 26 19126777, component := 51 },
    { zero := BitVec.ofNat 26 51076537, component := 51 },
    { zero := BitVec.ofNat 26 17550777, component := 34 },
    { zero := BitVec.ofNat 26 53172665, component := 51 },
    { zero := BitVec.ofNat 26 19646905, component := 40 },
    { zero := BitVec.ofNat 26 50552305, component := 45 },
    { zero := BitVec.ofNat 26 51105265, component := 25 },
    { zero := BitVec.ofNat 26 52648433, component := 43 },
    { zero := BitVec.ofNat 26 53201393, component := 22 },
    { zero := BitVec.ofNat 26 17038840, component := 64 },
    { zero := BitVec.ofNat 26 19134968, component := 64 },
    { zero := BitVec.ofNat 26 51084728, component := 64 },
    { zero := BitVec.ofNat 26 17558968, component := 34 },
    { zero := BitVec.ofNat 26 53180856, component := 64 },
    { zero := BitVec.ofNat 26 19655096, component := 40 },
    { zero := BitVec.ofNat 26 50560496, component := 56 },
    { zero := BitVec.ofNat 26 51113456, component := 25 },
    { zero := BitVec.ofNat 26 52656624, component := 53 },
    { zero := BitVec.ofNat 26 53209584, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover32 : ActiveCover := {
  active := BitVec.ofNat 14 522
  strata := [
    { zero := BitVec.ofNat 26 16899576, component := 35 },
    { zero := BitVec.ofNat 26 50945464, component := 40 },
    { zero := BitVec.ofNat 26 17419704, component := 34 },
    { zero := BitVec.ofNat 26 50421232, component := 26 },
    { zero := BitVec.ofNat 26 50974192, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover33 : ActiveCover := {
  active := BitVec.ofNat 14 524
  strata := [
    { zero := BitVec.ofNat 26 53172401, component := 43 },
    { zero := BitVec.ofNat 26 53201073, component := 22 },
    { zero := BitVec.ofNat 26 53180592, component := 22 },
    { zero := BitVec.ofNat 26 53209264, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover34 : ActiveCover := {
  active := BitVec.ofNat 14 526
  strata := [
    { zero := BitVec.ofNat 26 53042352, component := 22 },
    { zero := BitVec.ofNat 26 53071024, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover35 : ActiveCover := {
  active := BitVec.ofNat 14 544
  strata := [
    { zero := BitVec.ofNat 26 17030383, component := 38 },
    { zero := BitVec.ofNat 26 25287919, component := 38 },
    { zero := BitVec.ofNat 26 51076271, component := 25 },
    { zero := BitVec.ofNat 26 59333807, component := 3 },
    { zero := BitVec.ofNat 26 17550511, component := 33 },
    { zero := BitVec.ofNat 26 25808047, component := 15 },
    { zero := BitVec.ofNat 26 50552039, component := 24 },
    { zero := BitVec.ofNat 26 58809575, component := 24 },
    { zero := BitVec.ofNat 26 51104999, component := 38 },
    { zero := BitVec.ofNat 26 59362535, component := 38 },
    { zero := BitVec.ofNat 26 21208299, component := 47 },
    { zero := BitVec.ofNat 26 29465835, component := 36 },
    { zero := BitVec.ofNat 26 55254187, component := 47 },
    { zero := BitVec.ofNat 26 63511723, component := 31 },
    { zero := BitVec.ofNat 26 21728427, component := 32 },
    { zero := BitVec.ofNat 26 29985963, component := 32 },
    { zero := BitVec.ofNat 26 54729955, component := 26 },
    { zero := BitVec.ofNat 26 62987491, component := 26 },
    { zero := BitVec.ofNat 26 55282915, component := 33 },
    { zero := BitVec.ofNat 26 63540451, component := 33 },
    { zero := BitVec.ofNat 26 17038542, component := 38 },
    { zero := BitVec.ofNat 26 25296078, component := 38 },
    { zero := BitVec.ofNat 26 21216462, component := 38 },
    { zero := BitVec.ofNat 26 29473998, component := 38 },
    { zero := BitVec.ofNat 26 51084430, component := 56 },
    { zero := BitVec.ofNat 26 59341966, component := 6 },
    { zero := BitVec.ofNat 26 55262350, component := 59 },
    { zero := BitVec.ofNat 26 63519886, component := 26 },
    { zero := BitVec.ofNat 26 17558670, component := 26 },
    { zero := BitVec.ofNat 26 25816206, component := 19 },
    { zero := BitVec.ofNat 26 21736590, component := 36 },
    { zero := BitVec.ofNat 26 29994126, component := 19 },
    { zero := BitVec.ofNat 26 50560198, component := 58 },
    { zero := BitVec.ofNat 26 58817734, component := 24 },
    { zero := BitVec.ofNat 26 54738118, component := 61 },
    { zero := BitVec.ofNat 26 62995654, component := 26 },
    { zero := BitVec.ofNat 26 51113158, component := 38 },
    { zero := BitVec.ofNat 26 59370694, component := 38 },
    { zero := BitVec.ofNat 26 55291078, component := 38 },
    { zero := BitVec.ofNat 26 63548614, component := 38 },
    { zero := BitVec.ofNat 26 21216490, component := 59 },
    { zero := BitVec.ofNat 26 29474026, component := 36 },
    { zero := BitVec.ofNat 26 55262378, component := 59 },
    { zero := BitVec.ofNat 26 63519914, component := 31 },
    { zero := BitVec.ofNat 26 21736618, component := 32 },
    { zero := BitVec.ofNat 26 29994154, component := 32 },
    { zero := BitVec.ofNat 26 54738146, component := 26 },
    { zero := BitVec.ofNat 26 62995682, component := 26 },
    { zero := BitVec.ofNat 26 55291106, component := 33 },
    { zero := BitVec.ofNat 26 63548642, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover36 : ActiveCover := {
  active := BitVec.ofNat 14 546
  strata := [
    { zero := BitVec.ofNat 26 16899310, component := 38 },
    { zero := BitVec.ofNat 26 50945198, component := 25 },
    { zero := BitVec.ofNat 26 17419438, component := 33 },
    { zero := BitVec.ofNat 26 50420966, component := 24 },
    { zero := BitVec.ofNat 26 50973926, component := 38 },
    { zero := BitVec.ofNat 26 21077226, component := 36 },
    { zero := BitVec.ofNat 26 55123114, component := 31 },
    { zero := BitVec.ofNat 26 21597354, component := 32 },
    { zero := BitVec.ofNat 26 54598882, component := 26 },
    { zero := BitVec.ofNat 26 55151842, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover37 : ActiveCover := {
  active := BitVec.ofNat 14 548
  strata := [
    { zero := BitVec.ofNat 26 59333797, component := 3 },
    { zero := BitVec.ofNat 26 59362469, component := 3 },
    { zero := BitVec.ofNat 26 63511713, component := 26 },
    { zero := BitVec.ofNat 26 63540385, component := 33 },
    { zero := BitVec.ofNat 26 59341956, component := 6 },
    { zero := BitVec.ofNat 26 63519876, component := 26 },
    { zero := BitVec.ofNat 26 59370628, component := 6 },
    { zero := BitVec.ofNat 26 63548548, component := 19 },
    { zero := BitVec.ofNat 26 63519904, component := 26 },
    { zero := BitVec.ofNat 26 63548576, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover38 : ActiveCover := {
  active := BitVec.ofNat 14 556
  strata := [
    { zero := BitVec.ofNat 26 51076257, component := 25 },
    { zero := BitVec.ofNat 26 51104929, component := 25 },
    { zero := BitVec.ofNat 26 51084448, component := 25 },
    { zero := BitVec.ofNat 26 51113120, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover39 : ActiveCover := {
  active := BitVec.ofNat 14 558
  strata := [
    { zero := BitVec.ofNat 26 50945184, component := 25 },
    { zero := BitVec.ofNat 26 50973856, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover40 : ActiveCover := {
  active := BitVec.ofNat 14 576
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover41 : ActiveCover := {
  active := BitVec.ofNat 14 578
  strata := [
    { zero := BitVec.ofNat 26 16895454, component := 38 },
    { zero := BitVec.ofNat 26 21073374, component := 38 },
    { zero := BitVec.ofNat 26 18992350, component := 38 },
    { zero := BitVec.ofNat 26 23170270, component := 38 },
    { zero := BitVec.ofNat 26 50449878, component := 38 },
    { zero := BitVec.ofNat 26 54627798, component := 38 },
    { zero := BitVec.ofNat 26 52546774, component := 38 },
    { zero := BitVec.ofNat 26 56724694, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover42 : ActiveCover := {
  active := BitVec.ofNat 14 608
  strata := [
    { zero := BitVec.ofNat 26 17026255, component := 38 },
    { zero := BitVec.ofNat 26 25283791, component := 38 },
    { zero := BitVec.ofNat 26 21204175, component := 38 },
    { zero := BitVec.ofNat 26 29461711, component := 38 },
    { zero := BitVec.ofNat 26 50580679, component := 38 },
    { zero := BitVec.ofNat 26 58838215, component := 38 },
    { zero := BitVec.ofNat 26 54758599, component := 38 },
    { zero := BitVec.ofNat 26 63016135, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover43 : ActiveCover := {
  active := BitVec.ofNat 14 610
  strata := [
    { zero := BitVec.ofNat 26 16895182, component := 38 },
    { zero := BitVec.ofNat 26 21073102, component := 38 },
    { zero := BitVec.ofNat 26 50449606, component := 38 },
    { zero := BitVec.ofNat 26 54627526, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover44 : ActiveCover := {
  active := BitVec.ofNat 14 640
  strata := [
    { zero := BitVec.ofNat 26 17030463, component := 51 },
    { zero := BitVec.ofNat 26 50552127, component := 51 },
    { zero := BitVec.ofNat 26 27384895, component := 15 },
    { zero := BitVec.ofNat 26 60906559, component := 2 },
    { zero := BitVec.ofNat 26 19126335, component := 26 },
    { zero := BitVec.ofNat 26 52647999, component := 43 },
    { zero := BitVec.ofNat 26 17038623, component := 64 },
    { zero := BitVec.ofNat 26 50560287, component := 64 },
    { zero := BitVec.ofNat 26 21216543, component := 64 },
    { zero := BitVec.ofNat 26 54738207, component := 64 },
    { zero := BitVec.ofNat 26 27393055, component := 15 },
    { zero := BitVec.ofNat 26 60914719, component := 2 },
    { zero := BitVec.ofNat 26 31570975, component := 36 },
    { zero := BitVec.ofNat 26 65092639, component := 2 },
    { zero := BitVec.ofNat 26 19134495, component := 26 },
    { zero := BitVec.ofNat 26 52656159, component := 53 },
    { zero := BitVec.ofNat 26 23312415, component := 59 },
    { zero := BitVec.ofNat 26 56834079, component := 59 },
    { zero := BitVec.ofNat 26 21208379, component := 51 },
    { zero := BitVec.ofNat 26 54730043, component := 51 },
    { zero := BitVec.ofNat 26 31562811, component := 36 },
    { zero := BitVec.ofNat 26 65084475, component := 26 },
    { zero := BitVec.ofNat 26 23304251, component := 47 },
    { zero := BitVec.ofNat 26 56825915, component := 43 },
    { zero := BitVec.ofNat 26 25287997, component := 11 },
    { zero := BitVec.ofNat 26 58809661, component := 10 },
    { zero := BitVec.ofNat 26 27515197, component := 51 },
    { zero := BitVec.ofNat 26 61036861, component := 51 },
    { zero := BitVec.ofNat 26 25296157, component := 11 },
    { zero := BitVec.ofNat 26 58817821, component := 10 },
    { zero := BitVec.ofNat 26 29474077, component := 11 },
    { zero := BitVec.ofNat 26 62995741, component := 10 },
    { zero := BitVec.ofNat 26 27523357, component := 64 },
    { zero := BitVec.ofNat 26 61045021, component := 64 },
    { zero := BitVec.ofNat 26 31701277, component := 64 },
    { zero := BitVec.ofNat 26 65222941, component := 64 },
    { zero := BitVec.ofNat 26 29465913, component := 35 },
    { zero := BitVec.ofNat 26 62987577, component := 26 },
    { zero := BitVec.ofNat 26 31693113, component := 51 },
    { zero := BitVec.ofNat 26 65214777, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover45 : ActiveCover := {
  active := BitVec.ofNat 14 641
  strata := [
    { zero := BitVec.ofNat 26 21216538, component := 64 },
    { zero := BitVec.ofNat 26 54738202, component := 64 },
    { zero := BitVec.ofNat 26 31570970, component := 36 },
    { zero := BitVec.ofNat 26 65092634, component := 26 },
    { zero := BitVec.ofNat 26 23312410, component := 59 },
    { zero := BitVec.ofNat 26 56834074, component := 59 },
    { zero := BitVec.ofNat 26 29474072, component := 35 },
    { zero := BitVec.ofNat 26 62995736, component := 26 },
    { zero := BitVec.ofNat 26 31701272, component := 64 },
    { zero := BitVec.ofNat 26 65222936, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover46 : ActiveCover := {
  active := BitVec.ofNat 14 644
  strata := [
    { zero := BitVec.ofNat 26 60906549, component := 2 },
    { zero := BitVec.ofNat 26 61036597, component := 2 },
    { zero := BitVec.ofNat 26 60914709, component := 2 },
    { zero := BitVec.ofNat 26 65092629, component := 2 },
    { zero := BitVec.ofNat 26 61044757, component := 2 },
    { zero := BitVec.ofNat 26 65222677, component := 2 },
    { zero := BitVec.ofNat 26 65084465, component := 26 },
    { zero := BitVec.ofNat 26 65214513, component := 43 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover47 : ActiveCover := {
  active := BitVec.ofNat 14 645
  strata := [
    { zero := BitVec.ofNat 26 65092624, component := 26 },
    { zero := BitVec.ofNat 26 65222672, component := 53 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover48 : ActiveCover := {
  active := BitVec.ofNat 14 648
  strata := [
    { zero := BitVec.ofNat 26 17030457, component := 51 },
    { zero := BitVec.ofNat 26 50552121, component := 51 },
    { zero := BitVec.ofNat 26 19126585, component := 51 },
    { zero := BitVec.ofNat 26 52648249, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover49 : ActiveCover := {
  active := BitVec.ofNat 14 649
  strata := [
    { zero := BitVec.ofNat 26 17038616, component := 64 },
    { zero := BitVec.ofNat 26 50560280, component := 64 },
    { zero := BitVec.ofNat 26 19134744, component := 64 },
    { zero := BitVec.ofNat 26 52656408, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover50 : ActiveCover := {
  active := BitVec.ofNat 14 652
  strata := [
    { zero := BitVec.ofNat 26 52647985, component := 43 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover51 : ActiveCover := {
  active := BitVec.ofNat 14 653
  strata := [
    { zero := BitVec.ofNat 26 52656144, component := 53 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover52 : ActiveCover := {
  active := BitVec.ofNat 14 672
  strata := [
    { zero := BitVec.ofNat 26 17030191, component := 26 },
    { zero := BitVec.ofNat 26 25287727, component := 15 },
    { zero := BitVec.ofNat 26 50551855, component := 45 },
    { zero := BitVec.ofNat 26 58809391, component := 3 },
    { zero := BitVec.ofNat 26 17038351, component := 26 },
    { zero := BitVec.ofNat 26 25295887, component := 15 },
    { zero := BitVec.ofNat 26 50560015, component := 56 },
    { zero := BitVec.ofNat 26 58817551, component := 3 },
    { zero := BitVec.ofNat 26 21216271, component := 59 },
    { zero := BitVec.ofNat 26 29473807, component := 36 },
    { zero := BitVec.ofNat 26 54737935, component := 59 },
    { zero := BitVec.ofNat 26 62995471, component := 26 },
    { zero := BitVec.ofNat 26 21208107, component := 47 },
    { zero := BitVec.ofNat 26 29465643, component := 36 },
    { zero := BitVec.ofNat 26 54729771, component := 47 },
    { zero := BitVec.ofNat 26 62987307, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover53 : ActiveCover := {
  active := BitVec.ofNat 14 673
  strata := [
    { zero := BitVec.ofNat 26 21216266, component := 59 },
    { zero := BitVec.ofNat 26 29473802, component := 36 },
    { zero := BitVec.ofNat 26 54737930, component := 59 },
    { zero := BitVec.ofNat 26 62995466, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover54 : ActiveCover := {
  active := BitVec.ofNat 14 676
  strata := [
    { zero := BitVec.ofNat 26 58809381, component := 3 },
    { zero := BitVec.ofNat 26 58817541, component := 3 },
    { zero := BitVec.ofNat 26 62995461, component := 26 },
    { zero := BitVec.ofNat 26 62987297, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover55 : ActiveCover := {
  active := BitVec.ofNat 14 677
  strata := [
    { zero := BitVec.ofNat 26 62995456, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover56 : ActiveCover := {
  active := BitVec.ofNat 14 684
  strata := [
    { zero := BitVec.ofNat 26 50551841, component := 45 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover57 : ActiveCover := {
  active := BitVec.ofNat 14 685
  strata := [
    { zero := BitVec.ofNat 26 50560000, component := 56 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover58 : ActiveCover := {
  active := BitVec.ofNat 14 704
  strata := [
    { zero := BitVec.ofNat 26 17026335, component := 35 },
    { zero := BitVec.ofNat 26 21204255, component := 36 },
    { zero := BitVec.ofNat 26 27380767, component := 15 },
    { zero := BitVec.ofNat 26 31558687, component := 36 },
    { zero := BitVec.ofNat 26 19122207, component := 26 },
    { zero := BitVec.ofNat 26 23300127, component := 26 },
    { zero := BitVec.ofNat 26 25283869, component := 11 },
    { zero := BitVec.ofNat 26 29461789, component := 11 },
    { zero := BitVec.ofNat 26 27511069, component := 10 },
    { zero := BitVec.ofNat 26 31688989, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover59 : ActiveCover := {
  active := BitVec.ofNat 14 707
  strata := [
    { zero := BitVec.ofNat 26 21073178, component := 36 },
    { zero := BitVec.ofNat 26 23170074, component := 36 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover60 : ActiveCover := {
  active := BitVec.ofNat 14 708
  strata := [
    { zero := BitVec.ofNat 26 60935189, component := 2 },
    { zero := BitVec.ofNat 26 65113109, component := 2 },
    { zero := BitVec.ofNat 26 61065237, component := 2 },
    { zero := BitVec.ofNat 26 65243157, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover61 : ActiveCover := {
  active := BitVec.ofNat 14 715
  strata := [
    { zero := BitVec.ofNat 26 16895256, component := 35 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover62 : ActiveCover := {
  active := BitVec.ofNat 14 719
  strata := [
    { zero := BitVec.ofNat 26 52546576, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover63 : ActiveCover := {
  active := BitVec.ofNat 14 736
  strata := [
    { zero := BitVec.ofNat 26 17026063, component := 26 },
    { zero := BitVec.ofNat 26 25283599, component := 15 },
    { zero := BitVec.ofNat 26 21203983, component := 36 },
    { zero := BitVec.ofNat 26 29461519, component := 36 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover64 : ActiveCover := {
  active := BitVec.ofNat 14 739
  strata := [
    { zero := BitVec.ofNat 26 21072906, component := 36 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover65 : ActiveCover := {
  active := BitVec.ofNat 14 740
  strata := [
    { zero := BitVec.ofNat 26 58838021, component := 3 },
    { zero := BitVec.ofNat 26 63015941, component := 15 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover66 : ActiveCover := {
  active := BitVec.ofNat 14 751
  strata := [
    { zero := BitVec.ofNat 26 50449408, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover67 : ActiveCover := {
  active := BitVec.ofNat 14 1024
  strata := [
    { zero := BitVec.ofNat 26 62474927, component := 18 },
    { zero := BitVec.ofNat 26 62736431, component := 3 },
    { zero := BitVec.ofNat 26 62744591, component := 3 },
    { zero := BitVec.ofNat 26 66922511, component := 26 },
    { zero := BitVec.ofNat 26 62474983, component := 18 },
    { zero := BitVec.ofNat 26 62736487, component := 3 },
    { zero := BitVec.ofNat 26 62744647, component := 3 },
    { zero := BitVec.ofNat 26 66922567, component := 26 },
    { zero := BitVec.ofNat 26 66652843, component := 30 },
    { zero := BitVec.ofNat 26 66914347, component := 26 },
    { zero := BitVec.ofNat 26 66652899, component := 42 },
    { zero := BitVec.ofNat 26 66914403, component := 26 },
    { zero := BitVec.ofNat 26 62475181, component := 9 },
    { zero := BitVec.ofNat 26 62736685, component := 3 },
    { zero := BitVec.ofNat 26 62744845, component := 3 },
    { zero := BitVec.ofNat 26 66922765, component := 26 },
    { zero := BitVec.ofNat 26 62475237, component := 18 },
    { zero := BitVec.ofNat 26 62736741, component := 4 },
    { zero := BitVec.ofNat 26 62744901, component := 4 },
    { zero := BitVec.ofNat 26 66922821, component := 17 },
    { zero := BitVec.ofNat 26 66653097, component := 42 },
    { zero := BitVec.ofNat 26 66914601, component := 26 },
    { zero := BitVec.ofNat 26 66653153, component := 42 },
    { zero := BitVec.ofNat 26 66914657, component := 26 },
    { zero := BitVec.ofNat 26 62483086, component := 20 },
    { zero := BitVec.ofNat 26 66661006, component := 20 },
    { zero := BitVec.ofNat 26 62744718, component := 6 },
    { zero := BitVec.ofNat 26 66922638, component := 26 },
    { zero := BitVec.ofNat 26 62483142, component := 20 },
    { zero := BitVec.ofNat 26 66661062, component := 20 },
    { zero := BitVec.ofNat 26 62744774, component := 6 },
    { zero := BitVec.ofNat 26 66922694, component := 26 },
    { zero := BitVec.ofNat 26 66661034, component := 30 },
    { zero := BitVec.ofNat 26 66922666, component := 31 },
    { zero := BitVec.ofNat 26 66661090, component := 42 },
    { zero := BitVec.ofNat 26 66922722, component := 26 },
    { zero := BitVec.ofNat 26 62483340, component := 12 },
    { zero := BitVec.ofNat 26 66661260, component := 20 },
    { zero := BitVec.ofNat 26 62744972, component := 6 },
    { zero := BitVec.ofNat 26 66922892, component := 26 },
    { zero := BitVec.ofNat 26 62483396, component := 20 },
    { zero := BitVec.ofNat 26 66661316, component := 20 },
    { zero := BitVec.ofNat 26 62745028, component := 6 },
    { zero := BitVec.ofNat 26 66922948, component := 26 },
    { zero := BitVec.ofNat 26 66661288, component := 42 },
    { zero := BitVec.ofNat 26 66922920, component := 26 },
    { zero := BitVec.ofNat 26 66661344, component := 42 },
    { zero := BitVec.ofNat 26 66922976, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover68 : ActiveCover := {
  active := BitVec.ofNat 14 1025
  strata := [
    { zero := BitVec.ofNat 26 66922506, component := 26 },
    { zero := BitVec.ofNat 26 66922562, component := 26 },
    { zero := BitVec.ofNat 26 66922760, component := 26 },
    { zero := BitVec.ofNat 26 66922816, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover69 : ActiveCover := {
  active := BitVec.ofNat 14 1026
  strata := [
    { zero := BitVec.ofNat 26 54086318, component := 42 },
    { zero := BitVec.ofNat 26 54347950, component := 25 },
    { zero := BitVec.ofNat 26 54086374, component := 24 },
    { zero := BitVec.ofNat 26 54348006, component := 24 },
    { zero := BitVec.ofNat 26 58264234, component := 30 },
    { zero := BitVec.ofNat 26 58525866, component := 31 },
    { zero := BitVec.ofNat 26 58264290, component := 42 },
    { zero := BitVec.ofNat 26 58525922, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover70 : ActiveCover := {
  active := BitVec.ofNat 14 1028
  strata := [
    { zero := BitVec.ofNat 26 62474917, component := 18 },
    { zero := BitVec.ofNat 26 62736421, component := 3 },
    { zero := BitVec.ofNat 26 62744581, component := 3 },
    { zero := BitVec.ofNat 26 66922501, component := 26 },
    { zero := BitVec.ofNat 26 66652833, component := 42 },
    { zero := BitVec.ofNat 26 66914337, component := 26 },
    { zero := BitVec.ofNat 26 62483076, component := 20 },
    { zero := BitVec.ofNat 26 66660996, component := 20 },
    { zero := BitVec.ofNat 26 62744708, component := 6 },
    { zero := BitVec.ofNat 26 66922628, component := 26 },
    { zero := BitVec.ofNat 26 66661024, component := 42 },
    { zero := BitVec.ofNat 26 66922656, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover71 : ActiveCover := {
  active := BitVec.ofNat 14 1029
  strata := [
    { zero := BitVec.ofNat 26 66922496, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover72 : ActiveCover := {
  active := BitVec.ofNat 14 1034
  strata := [
    { zero := BitVec.ofNat 26 54086568, component := 39 },
    { zero := BitVec.ofNat 26 54348200, component := 25 },
    { zero := BitVec.ofNat 26 54086624, component := 42 },
    { zero := BitVec.ofNat 26 54348256, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover73 : ActiveCover := {
  active := BitVec.ofNat 14 1038
  strata := [
    { zero := BitVec.ofNat 26 54086304, component := 42 },
    { zero := BitVec.ofNat 26 54347936, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover74 : ActiveCover := {
  active := BitVec.ofNat 14 1088
  strata := [
    { zero := BitVec.ofNat 26 61950663, component := 18 },
    { zero := BitVec.ofNat 26 66128583, component := 18 },
    { zero := BitVec.ofNat 26 62212167, component := 3 },
    { zero := BitVec.ofNat 26 66390087, component := 26 },
    { zero := BitVec.ofNat 26 61950917, component := 18 },
    { zero := BitVec.ofNat 26 66128837, component := 18 },
    { zero := BitVec.ofNat 26 62212421, component := 4 },
    { zero := BitVec.ofNat 26 66390341, component := 17 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover75 : ActiveCover := {
  active := BitVec.ofNat 14 1090
  strata := [
    { zero := BitVec.ofNat 26 53562054, component := 24 },
    { zero := BitVec.ofNat 26 57739974, component := 41 },
    { zero := BitVec.ofNat 26 53823686, component := 24 },
    { zero := BitVec.ofNat 26 58001606, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover76 : ActiveCover := {
  active := BitVec.ofNat 14 1091
  strata := [
    { zero := BitVec.ofNat 26 58001474, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover77 : ActiveCover := {
  active := BitVec.ofNat 14 1099
  strata := [
    { zero := BitVec.ofNat 26 53823808, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover78 : ActiveCover := {
  active := BitVec.ofNat 14 1216
  strata := [
    { zero := BitVec.ofNat 26 61950479, component := 18 },
    { zero := BitVec.ofNat 26 66128399, component := 18 },
    { zero := BitVec.ofNat 26 61950733, component := 9 },
    { zero := BitVec.ofNat 26 66128653, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover79 : ActiveCover := {
  active := BitVec.ofNat 14 1219
  strata := [
    { zero := BitVec.ofNat 26 57739786, component := 29 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover80 : ActiveCover := {
  active := BitVec.ofNat 14 1220
  strata := [
    { zero := BitVec.ofNat 26 61950469, component := 18 },
    { zero := BitVec.ofNat 26 66128389, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover81 : ActiveCover := {
  active := BitVec.ofNat 14 1227
  strata := [
    { zero := BitVec.ofNat 26 53562120, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover82 : ActiveCover := {
  active := BitVec.ofNat 14 1231
  strata := [
    { zero := BitVec.ofNat 26 53561856, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover83 : ActiveCover := {
  active := BitVec.ofNat 14 1536
  strata := [
    { zero := BitVec.ofNat 26 61425855, component := 2 },
    { zero := BitVec.ofNat 26 61425911, component := 2 },
    { zero := BitVec.ofNat 26 65603771, component := 22 },
    { zero := BitVec.ofNat 26 65603827, component := 22 },
    { zero := BitVec.ofNat 26 61426109, component := 2 },
    { zero := BitVec.ofNat 26 61426165, component := 2 },
    { zero := BitVec.ofNat 26 65604025, component := 22 },
    { zero := BitVec.ofNat 26 65604081, component := 22 },
    { zero := BitVec.ofNat 26 61434014, component := 5 },
    { zero := BitVec.ofNat 26 65611934, component := 5 },
    { zero := BitVec.ofNat 26 61434070, component := 5 },
    { zero := BitVec.ofNat 26 65611990, component := 5 },
    { zero := BitVec.ofNat 26 65611962, component := 22 },
    { zero := BitVec.ofNat 26 65612018, component := 22 },
    { zero := BitVec.ofNat 26 61434268, component := 5 },
    { zero := BitVec.ofNat 26 65612188, component := 5 },
    { zero := BitVec.ofNat 26 61434324, component := 5 },
    { zero := BitVec.ofNat 26 65612244, component := 5 },
    { zero := BitVec.ofNat 26 65612216, component := 22 },
    { zero := BitVec.ofNat 26 65612272, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover84 : ActiveCover := {
  active := BitVec.ofNat 14 1538
  strata := [
    { zero := BitVec.ofNat 26 53037246, component := 22 },
    { zero := BitVec.ofNat 26 53037302, component := 21 },
    { zero := BitVec.ofNat 26 57215162, component := 22 },
    { zero := BitVec.ofNat 26 57215218, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover85 : ActiveCover := {
  active := BitVec.ofNat 14 1540
  strata := [
    { zero := BitVec.ofNat 26 61425845, component := 2 },
    { zero := BitVec.ofNat 26 65603761, component := 22 },
    { zero := BitVec.ofNat 26 61434004, component := 5 },
    { zero := BitVec.ofNat 26 65611924, component := 5 },
    { zero := BitVec.ofNat 26 65611952, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover86 : ActiveCover := {
  active := BitVec.ofNat 14 1546
  strata := [
    { zero := BitVec.ofNat 26 53037496, component := 22 },
    { zero := BitVec.ofNat 26 53037552, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover87 : ActiveCover := {
  active := BitVec.ofNat 14 1550
  strata := [
    { zero := BitVec.ofNat 26 53037232, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover88 : ActiveCover := {
  active := BitVec.ofNat 14 1600
  strata := [
    { zero := BitVec.ofNat 26 60901591, component := 2 },
    { zero := BitVec.ofNat 26 65079511, component := 2 },
    { zero := BitVec.ofNat 26 60901845, component := 2 },
    { zero := BitVec.ofNat 26 65079765, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover89 : ActiveCover := {
  active := BitVec.ofNat 14 1602
  strata := [
    { zero := BitVec.ofNat 26 52512982, component := 21 },
    { zero := BitVec.ofNat 26 56690902, component := 21 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover90 : ActiveCover := {
  active := BitVec.ofNat 14 1728
  strata := [
    { zero := BitVec.ofNat 26 60901407, component := 2 },
    { zero := BitVec.ofNat 26 65079327, component := 2 },
    { zero := BitVec.ofNat 26 60901661, component := 2 },
    { zero := BitVec.ofNat 26 65079581, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover91 : ActiveCover := {
  active := BitVec.ofNat 14 1731
  strata := [
    { zero := BitVec.ofNat 26 56690714, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover92 : ActiveCover := {
  active := BitVec.ofNat 14 1732
  strata := [
    { zero := BitVec.ofNat 26 60901397, component := 2 },
    { zero := BitVec.ofNat 26 65079317, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover93 : ActiveCover := {
  active := BitVec.ofNat 14 1739
  strata := [
    { zero := BitVec.ofNat 26 52513048, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover94 : ActiveCover := {
  active := BitVec.ofNat 14 1743
  strata := [
    { zero := BitVec.ofNat 26 52512784, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover95 : ActiveCover := {
  active := BitVec.ofNat 14 2048
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover96 : ActiveCover := {
  active := BitVec.ofNat 14 2049
  strata := [
    { zero := BitVec.ofNat 26 22540618, component := 59 },
    { zero := BitVec.ofNat 26 56586506, component := 59 },
    { zero := BitVec.ofNat 26 23060746, component := 26 },
    { zero := BitVec.ofNat 26 56062274, component := 57 },
    { zero := BitVec.ofNat 26 56615234, component := 23 },
    { zero := BitVec.ofNat 26 30929224, component := 62 },
    { zero := BitVec.ofNat 26 64975112, component := 56 },
    { zero := BitVec.ofNat 26 31449352, component := 26 },
    { zero := BitVec.ofNat 26 64450880, component := 57 },
    { zero := BitVec.ofNat 26 65003840, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover97 : ActiveCover := {
  active := BitVec.ofNat 14 2056
  strata := [
    { zero := BitVec.ofNat 26 18076649, component := 50 },
    { zero := BitVec.ofNat 26 18338153, component := 49 },
    { zero := BitVec.ofNat 26 52122537, component := 50 },
    { zero := BitVec.ofNat 26 18596777, component := 39 },
    { zero := BitVec.ofNat 26 52384041, component := 45 },
    { zero := BitVec.ofNat 26 18858281, component := 26 },
    { zero := BitVec.ofNat 26 51598305, component := 45 },
    { zero := BitVec.ofNat 26 52151265, component := 25 },
    { zero := BitVec.ofNat 26 51859809, component := 46 },
    { zero := BitVec.ofNat 26 52412769, component := 23 },
    { zero := BitVec.ofNat 26 18084840, component := 63 },
    { zero := BitVec.ofNat 26 18346472, component := 62 },
    { zero := BitVec.ofNat 26 52130728, component := 63 },
    { zero := BitVec.ofNat 26 18604968, component := 39 },
    { zero := BitVec.ofNat 26 52392360, component := 25 },
    { zero := BitVec.ofNat 26 18866600, component := 26 },
    { zero := BitVec.ofNat 26 51606496, component := 56 },
    { zero := BitVec.ofNat 26 52159456, component := 25 },
    { zero := BitVec.ofNat 26 51868128, component := 57 },
    { zero := BitVec.ofNat 26 52421088, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover98 : ActiveCover := {
  active := BitVec.ofNat 14 2057
  strata := [
    { zero := BitVec.ofNat 26 18346312, component := 62 },
    { zero := BitVec.ofNat 26 52392200, component := 56 },
    { zero := BitVec.ofNat 26 18866440, component := 26 },
    { zero := BitVec.ofNat 26 51867968, component := 57 },
    { zero := BitVec.ofNat 26 52420928, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover99 : ActiveCover := {
  active := BitVec.ofNat 14 2112
  strata := [
    { zero := BitVec.ofNat 26 18072527, component := 26 },
    { zero := BitVec.ofNat 26 18334031, component := 26 },
    { zero := BitVec.ofNat 26 51626951, component := 24 },
    { zero := BitVec.ofNat 26 51888455, component := 23 },
    { zero := BitVec.ofNat 26 26461133, component := 9 },
    { zero := BitVec.ofNat 26 26722637, component := 17 },
    { zero := BitVec.ofNat 26 60015557, component := 3 },
    { zero := BitVec.ofNat 26 60277061, component := 4 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover100 : ActiveCover := {
  active := BitVec.ofNat 14 2176
  strata := [
    { zero := BitVec.ofNat 26 18076463, component := 50 },
    { zero := BitVec.ofNat 26 51598127, component := 50 },
    { zero := BitVec.ofNat 26 18084623, component := 63 },
    { zero := BitVec.ofNat 26 51606287, component := 63 },
    { zero := BitVec.ofNat 26 22270763, component := 50 },
    { zero := BitVec.ofNat 26 55792427, component := 50 },
    { zero := BitVec.ofNat 26 26465069, component := 50 },
    { zero := BitVec.ofNat 26 59986733, component := 50 },
    { zero := BitVec.ofNat 26 26473229, component := 63 },
    { zero := BitVec.ofNat 26 59994893, component := 63 },
    { zero := BitVec.ofNat 26 30659369, component := 50 },
    { zero := BitVec.ofNat 26 64181033, component := 50 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover101 : ActiveCover := {
  active := BitVec.ofNat 14 2177
  strata := [
    { zero := BitVec.ofNat 26 22278922, component := 63 },
    { zero := BitVec.ofNat 26 55800586, component := 63 },
    { zero := BitVec.ofNat 26 30667528, component := 63 },
    { zero := BitVec.ofNat 26 64189192, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover102 : ActiveCover := {
  active := BitVec.ofNat 14 2184
  strata := [
    { zero := BitVec.ofNat 26 18076457, component := 50 },
    { zero := BitVec.ofNat 26 51598121, component := 50 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover103 : ActiveCover := {
  active := BitVec.ofNat 14 2185
  strata := [
    { zero := BitVec.ofNat 26 18084616, component := 63 },
    { zero := BitVec.ofNat 26 51606280, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover104 : ActiveCover := {
  active := BitVec.ofNat 14 2240
  strata := [
    { zero := BitVec.ofNat 26 18072335, component := 26 },
    { zero := BitVec.ofNat 26 26460941, component := 9 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover105 : ActiveCover := {
  active := BitVec.ofNat 14 2560
  strata := [
    { zero := BitVec.ofNat 26 17027583, component := 51 },
    { zero := BitVec.ofNat 26 51073471, component := 51 },
    { zero := BitVec.ofNat 26 17547711, component := 40 },
    { zero := BitVec.ofNat 26 50549239, component := 24 },
    { zero := BitVec.ofNat 26 51102199, component := 24 },
    { zero := BitVec.ofNat 26 21221883, component := 51 },
    { zero := BitVec.ofNat 26 55267771, component := 51 },
    { zero := BitVec.ofNat 26 21742011, component := 40 },
    { zero := BitVec.ofNat 26 54743539, component := 45 },
    { zero := BitVec.ofNat 26 55296499, component := 25 },
    { zero := BitVec.ofNat 26 25416189, component := 51 },
    { zero := BitVec.ofNat 26 59462077, component := 51 },
    { zero := BitVec.ofNat 26 25936317, component := 10 },
    { zero := BitVec.ofNat 26 58937845, component := 3 },
    { zero := BitVec.ofNat 26 59490805, component := 3 },
    { zero := BitVec.ofNat 26 29610489, component := 51 },
    { zero := BitVec.ofNat 26 63656377, component := 51 },
    { zero := BitVec.ofNat 26 30130617, component := 40 },
    { zero := BitVec.ofNat 26 63132145, component := 45 },
    { zero := BitVec.ofNat 26 63685105, component := 25 },
    { zero := BitVec.ofNat 26 17035742, component := 64 },
    { zero := BitVec.ofNat 26 51081630, component := 64 },
    { zero := BitVec.ofNat 26 17555870, component := 26 },
    { zero := BitVec.ofNat 26 50557398, component := 58 },
    { zero := BitVec.ofNat 26 51110358, component := 24 },
    { zero := BitVec.ofNat 26 21230074, component := 64 },
    { zero := BitVec.ofNat 26 55275962, component := 64 },
    { zero := BitVec.ofNat 26 21750202, component := 40 },
    { zero := BitVec.ofNat 26 54751730, component := 56 },
    { zero := BitVec.ofNat 26 55304690, component := 25 },
    { zero := BitVec.ofNat 26 25424348, component := 64 },
    { zero := BitVec.ofNat 26 59470236, component := 64 },
    { zero := BitVec.ofNat 26 25944476, component := 13 },
    { zero := BitVec.ofNat 26 58946004, component := 56 },
    { zero := BitVec.ofNat 26 59498964, component := 6 },
    { zero := BitVec.ofNat 26 29618680, component := 64 },
    { zero := BitVec.ofNat 26 63664568, component := 64 },
    { zero := BitVec.ofNat 26 30138808, component := 40 },
    { zero := BitVec.ofNat 26 63140336, component := 56 },
    { zero := BitVec.ofNat 26 63693296, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover106 : ActiveCover := {
  active := BitVec.ofNat 14 2568
  strata := [
    { zero := BitVec.ofNat 26 17027577, component := 51 },
    { zero := BitVec.ofNat 26 51073465, component := 51 },
    { zero := BitVec.ofNat 26 17547705, component := 40 },
    { zero := BitVec.ofNat 26 50549233, component := 45 },
    { zero := BitVec.ofNat 26 51102193, component := 25 },
    { zero := BitVec.ofNat 26 17035768, component := 64 },
    { zero := BitVec.ofNat 26 51081656, component := 64 },
    { zero := BitVec.ofNat 26 17555896, component := 40 },
    { zero := BitVec.ofNat 26 50557424, component := 56 },
    { zero := BitVec.ofNat 26 51110384, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover107 : ActiveCover := {
  active := BitVec.ofNat 14 2592
  strata := [
    { zero := BitVec.ofNat 26 17027311, component := 26 },
    { zero := BitVec.ofNat 26 51073199, component := 25 },
    { zero := BitVec.ofNat 26 17547439, component := 26 },
    { zero := BitVec.ofNat 26 50548967, component := 24 },
    { zero := BitVec.ofNat 26 51101927, component := 24 },
    { zero := BitVec.ofNat 26 21221611, component := 47 },
    { zero := BitVec.ofNat 26 55267499, component := 47 },
    { zero := BitVec.ofNat 26 21741739, component := 31 },
    { zero := BitVec.ofNat 26 54743267, component := 45 },
    { zero := BitVec.ofNat 26 55296227, component := 25 },
    { zero := BitVec.ofNat 26 17035470, component := 61 },
    { zero := BitVec.ofNat 26 51081358, component := 56 },
    { zero := BitVec.ofNat 26 17555598, component := 26 },
    { zero := BitVec.ofNat 26 50557126, component := 58 },
    { zero := BitVec.ofNat 26 51110086, component := 24 },
    { zero := BitVec.ofNat 26 21229802, component := 59 },
    { zero := BitVec.ofNat 26 55275690, component := 59 },
    { zero := BitVec.ofNat 26 21749930, component := 31 },
    { zero := BitVec.ofNat 26 54751458, component := 56 },
    { zero := BitVec.ofNat 26 55304418, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover108 : ActiveCover := {
  active := BitVec.ofNat 14 2596
  strata := [
    { zero := BitVec.ofNat 26 59461797, component := 3 },
    { zero := BitVec.ofNat 26 59490469, component := 3 },
    { zero := BitVec.ofNat 26 63656097, component := 25 },
    { zero := BitVec.ofNat 26 63684769, component := 25 },
    { zero := BitVec.ofNat 26 59469956, component := 6 },
    { zero := BitVec.ofNat 26 59498628, component := 6 },
    { zero := BitVec.ofNat 26 63664288, component := 25 },
    { zero := BitVec.ofNat 26 63692960, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover109 : ActiveCover := {
  active := BitVec.ofNat 14 2604
  strata := [
    { zero := BitVec.ofNat 26 51073185, component := 25 },
    { zero := BitVec.ofNat 26 51101857, component := 25 },
    { zero := BitVec.ofNat 26 51081376, component := 25 },
    { zero := BitVec.ofNat 26 51110048, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover110 : ActiveCover := {
  active := BitVec.ofNat 14 2624
  strata := [
    { zero := BitVec.ofNat 26 17023455, component := 26 },
    { zero := BitVec.ofNat 26 50577879, component := 24 },
    { zero := BitVec.ofNat 26 25412061, component := 10 },
    { zero := BitVec.ofNat 26 58966485, component := 3 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover111 : ActiveCover := {
  active := BitVec.ofNat 14 2656
  strata := [
    { zero := BitVec.ofNat 26 17023183, component := 26 },
    { zero := BitVec.ofNat 26 50577607, component := 24 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover112 : ActiveCover := {
  active := BitVec.ofNat 14 2688
  strata := [
    { zero := BitVec.ofNat 26 17027391, component := 51 },
    { zero := BitVec.ofNat 26 50549055, component := 51 },
    { zero := BitVec.ofNat 26 17035551, component := 64 },
    { zero := BitVec.ofNat 26 50557215, component := 64 },
    { zero := BitVec.ofNat 26 21221691, component := 51 },
    { zero := BitVec.ofNat 26 54743355, component := 51 },
    { zero := BitVec.ofNat 26 25415997, component := 51 },
    { zero := BitVec.ofNat 26 58937661, component := 51 },
    { zero := BitVec.ofNat 26 25424157, component := 64 },
    { zero := BitVec.ofNat 26 58945821, component := 64 },
    { zero := BitVec.ofNat 26 29610297, component := 51 },
    { zero := BitVec.ofNat 26 63131961, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover113 : ActiveCover := {
  active := BitVec.ofNat 14 2689
  strata := [
    { zero := BitVec.ofNat 26 21229850, component := 64 },
    { zero := BitVec.ofNat 26 54751514, component := 64 },
    { zero := BitVec.ofNat 26 29618456, component := 64 },
    { zero := BitVec.ofNat 26 63140120, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover114 : ActiveCover := {
  active := BitVec.ofNat 14 2696
  strata := [
    { zero := BitVec.ofNat 26 17027385, component := 51 },
    { zero := BitVec.ofNat 26 50549049, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover115 : ActiveCover := {
  active := BitVec.ofNat 14 2697
  strata := [
    { zero := BitVec.ofNat 26 17035544, component := 64 },
    { zero := BitVec.ofNat 26 50557208, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover116 : ActiveCover := {
  active := BitVec.ofNat 14 2720
  strata := [
    { zero := BitVec.ofNat 26 17027119, component := 26 },
    { zero := BitVec.ofNat 26 50548783, component := 45 },
    { zero := BitVec.ofNat 26 17035279, component := 26 },
    { zero := BitVec.ofNat 26 50556943, component := 56 },
    { zero := BitVec.ofNat 26 21221419, component := 47 },
    { zero := BitVec.ofNat 26 54743083, component := 47 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover117 : ActiveCover := {
  active := BitVec.ofNat 14 2721
  strata := [
    { zero := BitVec.ofNat 26 21229578, component := 59 },
    { zero := BitVec.ofNat 26 54751242, component := 59 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover118 : ActiveCover := {
  active := BitVec.ofNat 14 2724
  strata := [
    { zero := BitVec.ofNat 26 58937381, component := 3 },
    { zero := BitVec.ofNat 26 58945541, component := 3 },
    { zero := BitVec.ofNat 26 63131681, component := 45 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover119 : ActiveCover := {
  active := BitVec.ofNat 14 2725
  strata := [
    { zero := BitVec.ofNat 26 63139840, component := 56 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover120 : ActiveCover := {
  active := BitVec.ofNat 14 2732
  strata := [
    { zero := BitVec.ofNat 26 50548769, component := 45 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover121 : ActiveCover := {
  active := BitVec.ofNat 14 2733
  strata := [
    { zero := BitVec.ofNat 26 50556928, component := 56 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover122 : ActiveCover := {
  active := BitVec.ofNat 14 2752
  strata := [
    { zero := BitVec.ofNat 26 17023263, component := 26 },
    { zero := BitVec.ofNat 26 25411869, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover123 : ActiveCover := {
  active := BitVec.ofNat 14 2784
  strata := [
    { zero := BitVec.ofNat 26 17022991, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover124 : ActiveCover := {
  active := BitVec.ofNat 14 2788
  strata := [
    { zero := BitVec.ofNat 26 58966021, component := 3 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover125 : ActiveCover := {
  active := BitVec.ofNat 14 3072
  strata := [
    { zero := BitVec.ofNat 26 60375981, component := 9 },
    { zero := BitVec.ofNat 26 60637485, component := 3 },
    { zero := BitVec.ofNat 26 60645645, component := 3 },
    { zero := BitVec.ofNat 26 60376037, component := 3 },
    { zero := BitVec.ofNat 26 60637541, component := 4 },
    { zero := BitVec.ofNat 26 60645701, component := 4 },
    { zero := BitVec.ofNat 26 64570281, component := 39 },
    { zero := BitVec.ofNat 26 64831785, component := 26 },
    { zero := BitVec.ofNat 26 64570337, component := 25 },
    { zero := BitVec.ofNat 26 64831841, component := 23 },
    { zero := BitVec.ofNat 26 60384140, component := 12 },
    { zero := BitVec.ofNat 26 60645772, component := 6 },
    { zero := BitVec.ofNat 26 60384196, component := 6 },
    { zero := BitVec.ofNat 26 60645828, component := 6 },
    { zero := BitVec.ofNat 26 64578472, component := 39 },
    { zero := BitVec.ofNat 26 64840104, component := 25 },
    { zero := BitVec.ofNat 26 64578528, component := 25 },
    { zero := BitVec.ofNat 26 64840160, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover126 : ActiveCover := {
  active := BitVec.ofNat 14 3073
  strata := [
    { zero := BitVec.ofNat 26 64839944, component := 26 },
    { zero := BitVec.ofNat 26 64840000, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover127 : ActiveCover := {
  active := BitVec.ofNat 14 3074
  strata := [
    { zero := BitVec.ofNat 26 51987374, component := 39 },
    { zero := BitVec.ofNat 26 52249006, component := 25 },
    { zero := BitVec.ofNat 26 51987430, component := 24 },
    { zero := BitVec.ofNat 26 52249062, component := 24 },
    { zero := BitVec.ofNat 26 56181674, component := 39 },
    { zero := BitVec.ofNat 26 56443306, component := 25 },
    { zero := BitVec.ofNat 26 56181730, component := 25 },
    { zero := BitVec.ofNat 26 56443362, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover128 : ActiveCover := {
  active := BitVec.ofNat 14 3082
  strata := [
    { zero := BitVec.ofNat 26 51987368, component := 39 },
    { zero := BitVec.ofNat 26 52249000, component := 25 },
    { zero := BitVec.ofNat 26 51987424, component := 25 },
    { zero := BitVec.ofNat 26 52249056, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover129 : ActiveCover := {
  active := BitVec.ofNat 14 3136
  strata := [
    { zero := BitVec.ofNat 26 59851717, component := 3 },
    { zero := BitVec.ofNat 26 60113221, component := 4 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover130 : ActiveCover := {
  active := BitVec.ofNat 14 3138
  strata := [
    { zero := BitVec.ofNat 26 51463110, component := 24 },
    { zero := BitVec.ofNat 26 51724742, component := 24 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover131 : ActiveCover := {
  active := BitVec.ofNat 14 3139
  strata := [
    { zero := BitVec.ofNat 26 55918914, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover132 : ActiveCover := {
  active := BitVec.ofNat 14 3147
  strata := [
    { zero := BitVec.ofNat 26 51724608, component := 23 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover133 : ActiveCover := {
  active := BitVec.ofNat 14 3264
  strata := [
    { zero := BitVec.ofNat 26 59851533, component := 9 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover134 : ActiveCover := {
  active := BitVec.ofNat 14 3267
  strata := [
    { zero := BitVec.ofNat 26 55657226, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover135 : ActiveCover := {
  active := BitVec.ofNat 14 3275
  strata := [
    { zero := BitVec.ofNat 26 51462920, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover136 : ActiveCover := {
  active := BitVec.ofNat 14 3584
  strata := [
    { zero := BitVec.ofNat 26 59326909, component := 10 },
    { zero := BitVec.ofNat 26 59326965, component := 3 },
    { zero := BitVec.ofNat 26 63521209, component := 40 },
    { zero := BitVec.ofNat 26 63521265, component := 25 },
    { zero := BitVec.ofNat 26 59335068, component := 6 },
    { zero := BitVec.ofNat 26 59335124, component := 6 },
    { zero := BitVec.ofNat 26 63529400, component := 40 },
    { zero := BitVec.ofNat 26 63529456, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover137 : ActiveCover := {
  active := BitVec.ofNat 14 3586
  strata := [
    { zero := BitVec.ofNat 26 50938302, component := 40 },
    { zero := BitVec.ofNat 26 50938358, component := 24 },
    { zero := BitVec.ofNat 26 55132602, component := 40 },
    { zero := BitVec.ofNat 26 55132658, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover138 : ActiveCover := {
  active := BitVec.ofNat 14 3594
  strata := [
    { zero := BitVec.ofNat 26 50938296, component := 40 },
    { zero := BitVec.ofNat 26 50938352, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover139 : ActiveCover := {
  active := BitVec.ofNat 14 3616
  strata := [
    { zero := BitVec.ofNat 26 59326639, component := 3 },
    { zero := BitVec.ofNat 26 59326695, component := 24 },
    { zero := BitVec.ofNat 26 63520939, component := 25 },
    { zero := BitVec.ofNat 26 63520995, component := 25 },
    { zero := BitVec.ofNat 26 59334798, component := 6 },
    { zero := BitVec.ofNat 26 59334854, component := 6 },
    { zero := BitVec.ofNat 26 63529130, component := 25 },
    { zero := BitVec.ofNat 26 63529186, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover140 : ActiveCover := {
  active := BitVec.ofNat 14 3618
  strata := [
    { zero := BitVec.ofNat 26 50938030, component := 25 },
    { zero := BitVec.ofNat 26 50938086, component := 24 },
    { zero := BitVec.ofNat 26 55132330, component := 25 },
    { zero := BitVec.ofNat 26 55132386, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover141 : ActiveCover := {
  active := BitVec.ofNat 14 3620
  strata := [
    { zero := BitVec.ofNat 26 59326629, component := 3 },
    { zero := BitVec.ofNat 26 63520929, component := 25 },
    { zero := BitVec.ofNat 26 59334788, component := 6 },
    { zero := BitVec.ofNat 26 63529120, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover142 : ActiveCover := {
  active := BitVec.ofNat 14 3630
  strata := [
    { zero := BitVec.ofNat 26 50938016, component := 25 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover143 : ActiveCover := {
  active := BitVec.ofNat 14 3648
  strata := [
    { zero := BitVec.ofNat 26 58802645, component := 3 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover144 : ActiveCover := {
  active := BitVec.ofNat 14 3650
  strata := [
    { zero := BitVec.ofNat 26 50414038, component := 24 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover145 : ActiveCover := {
  active := BitVec.ofNat 14 3680
  strata := [
    { zero := BitVec.ofNat 26 58802375, component := 24 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover146 : ActiveCover := {
  active := BitVec.ofNat 14 3682
  strata := [
    { zero := BitVec.ofNat 26 50413766, component := 24 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover147 : ActiveCover := {
  active := BitVec.ofNat 14 3776
  strata := [
    { zero := BitVec.ofNat 26 58802461, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover148 : ActiveCover := {
  active := BitVec.ofNat 14 3779
  strata := [
    { zero := BitVec.ofNat 26 54608154, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover149 : ActiveCover := {
  active := BitVec.ofNat 14 3787
  strata := [
    { zero := BitVec.ofNat 26 50413848, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover150 : ActiveCover := {
  active := BitVec.ofNat 14 3808
  strata := [
    { zero := BitVec.ofNat 26 58802191, component := 3 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover151 : ActiveCover := {
  active := BitVec.ofNat 14 3811
  strata := [
    { zero := BitVec.ofNat 26 54607882, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover152 : ActiveCover := {
  active := BitVec.ofNat 14 3812
  strata := [
    { zero := BitVec.ofNat 26 58802181, component := 3 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover153 : ActiveCover := {
  active := BitVec.ofNat 14 3823
  strata := [
    { zero := BitVec.ofNat 26 50413568, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover154 : ActiveCover := {
  active := BitVec.ofNat 14 4096
  strata := [
    { zero := BitVec.ofNat 26 1286143, component := 38 },
    { zero := BitVec.ofNat 26 11640575, component := 38 },
    { zero := BitVec.ofNat 26 3382015, component := 41 },
    { zero := BitVec.ofNat 26 1547647, component := 51 },
    { zero := BitVec.ofNat 26 11902079, component := 15 },
    { zero := BitVec.ofNat 26 3643519, component := 26 },
    { zero := BitVec.ofNat 26 35332031, component := 51 },
    { zero := BitVec.ofNat 26 1806271, component := 34 },
    { zero := BitVec.ofNat 26 45686463, component := 2 },
    { zero := BitVec.ofNat 26 12160703, component := 18 },
    { zero := BitVec.ofNat 26 37427903, component := 43 },
    { zero := BitVec.ofNat 26 3902143, component := 42 },
    { zero := BitVec.ofNat 26 35593535, component := 51 },
    { zero := BitVec.ofNat 26 2067775, component := 35 },
    { zero := BitVec.ofNat 26 45947967, component := 2 },
    { zero := BitVec.ofNat 26 12422207, component := 15 },
    { zero := BitVec.ofNat 26 37689407, component := 43 },
    { zero := BitVec.ofNat 26 4163647, component := 26 },
    { zero := BitVec.ofNat 26 1555807, component := 64 },
    { zero := BitVec.ofNat 26 11910239, component := 15 },
    { zero := BitVec.ofNat 26 3651679, component := 26 },
    { zero := BitVec.ofNat 26 35601695, component := 64 },
    { zero := BitVec.ofNat 26 2075935, component := 35 },
    { zero := BitVec.ofNat 26 45956127, component := 2 },
    { zero := BitVec.ofNat 26 12430367, component := 15 },
    { zero := BitVec.ofNat 26 37697567, component := 53 },
    { zero := BitVec.ofNat 26 4171807, component := 26 },
    { zero := BitVec.ofNat 26 34807799, component := 26 },
    { zero := BitVec.ofNat 26 35360759, component := 38 },
    { zero := BitVec.ofNat 26 45162231, component := 2 },
    { zero := BitVec.ofNat 26 45715191, component := 38 },
    { zero := BitVec.ofNat 26 36903671, component := 43 },
    { zero := BitVec.ofNat 26 37456631, component := 21 },
    { zero := BitVec.ofNat 26 35069303, component := 49 },
    { zero := BitVec.ofNat 26 35622263, component := 37 },
    { zero := BitVec.ofNat 26 45423735, component := 2 },
    { zero := BitVec.ofNat 26 45976695, component := 2 },
    { zero := BitVec.ofNat 26 37165175, component := 43 },
    { zero := BitVec.ofNat 26 37718135, component := 26 },
    { zero := BitVec.ofNat 26 35077463, component := 62 },
    { zero := BitVec.ofNat 26 35630423, component := 37 },
    { zero := BitVec.ofNat 26 45431895, component := 2 },
    { zero := BitVec.ofNat 26 45984855, component := 2 },
    { zero := BitVec.ofNat 26 37173335, component := 53 },
    { zero := BitVec.ofNat 26 37726295, component := 26 },
    { zero := BitVec.ofNat 26 9543677, component := 11 },
    { zero := BitVec.ofNat 26 11770877, component := 51 },
    { zero := BitVec.ofNat 26 9805181, component := 16 },
    { zero := BitVec.ofNat 26 12032381, component := 51 },
    { zero := BitVec.ofNat 26 43589565, component := 10 },
    { zero := BitVec.ofNat 26 10063805, component := 11 },
    { zero := BitVec.ofNat 26 45816765, component := 51 },
    { zero := BitVec.ofNat 26 12291005, component := 18 },
    { zero := BitVec.ofNat 26 43851069, component := 10 },
    { zero := BitVec.ofNat 26 10325309, component := 11 },
    { zero := BitVec.ofNat 26 46078269, component := 51 },
    { zero := BitVec.ofNat 26 12552509, component := 10 },
    { zero := BitVec.ofNat 26 9813341, component := 16 },
    { zero := BitVec.ofNat 26 12040541, component := 64 },
    { zero := BitVec.ofNat 26 43859229, component := 10 },
    { zero := BitVec.ofNat 26 10333469, component := 11 },
    { zero := BitVec.ofNat 26 46086429, component := 64 },
    { zero := BitVec.ofNat 26 12560669, component := 10 },
    { zero := BitVec.ofNat 26 43065333, component := 26 },
    { zero := BitVec.ofNat 26 43618293, component := 15 },
    { zero := BitVec.ofNat 26 45292533, component := 2 },
    { zero := BitVec.ofNat 26 45845493, component := 2 },
    { zero := BitVec.ofNat 26 43326837, component := 17 },
    { zero := BitVec.ofNat 26 43879797, component := 16 },
    { zero := BitVec.ofNat 26 45554037, component := 2 },
    { zero := BitVec.ofNat 26 46106997, component := 2 },
    { zero := BitVec.ofNat 26 43334997, component := 17 },
    { zero := BitVec.ofNat 26 43887957, component := 16 },
    { zero := BitVec.ofNat 26 45562197, component := 2 },
    { zero := BitVec.ofNat 26 46115157, component := 2 },
    { zero := BitVec.ofNat 26 1294302, component := 38 },
    { zero := BitVec.ofNat 26 1555934, component := 38 },
    { zero := BitVec.ofNat 26 11648734, component := 38 },
    { zero := BitVec.ofNat 26 3390174, component := 66 },
    { zero := BitVec.ofNat 26 11910366, component := 38 },
    { zero := BitVec.ofNat 26 3651806, component := 61 },
    { zero := BitVec.ofNat 26 35340190, component := 64 },
    { zero := BitVec.ofNat 26 1814430, component := 35 },
    { zero := BitVec.ofNat 26 35601822, component := 64 },
    { zero := BitVec.ofNat 26 2076062, component := 35 },
    { zero := BitVec.ofNat 26 45694622, component := 5 },
    { zero := BitVec.ofNat 26 12168862, component := 20 },
    { zero := BitVec.ofNat 26 37436062, component := 53 },
    { zero := BitVec.ofNat 26 3910302, component := 26 },
    { zero := BitVec.ofNat 26 45956254, component := 5 },
    { zero := BitVec.ofNat 26 12430494, component := 19 },
    { zero := BitVec.ofNat 26 37697694, component := 53 },
    { zero := BitVec.ofNat 26 4171934, component := 26 },
    { zero := BitVec.ofNat 26 34815958, component := 61 },
    { zero := BitVec.ofNat 26 35368918, component := 38 },
    { zero := BitVec.ofNat 26 35077590, component := 62 },
    { zero := BitVec.ofNat 26 35630550, component := 38 },
    { zero := BitVec.ofNat 26 45170390, component := 21 },
    { zero := BitVec.ofNat 26 45723350, component := 5 },
    { zero := BitVec.ofNat 26 36911830, component := 55 },
    { zero := BitVec.ofNat 26 37464790, component := 21 },
    { zero := BitVec.ofNat 26 45432022, component := 21 },
    { zero := BitVec.ofNat 26 45984982, component := 5 },
    { zero := BitVec.ofNat 26 37173462, component := 55 },
    { zero := BitVec.ofNat 26 37726422, component := 21 },
    { zero := BitVec.ofNat 26 9551836, component := 35 },
    { zero := BitVec.ofNat 26 11779036, component := 64 },
    { zero := BitVec.ofNat 26 9813468, component := 37 },
    { zero := BitVec.ofNat 26 12040668, component := 64 },
    { zero := BitVec.ofNat 26 43597724, component := 13 },
    { zero := BitVec.ofNat 26 10071964, component := 14 },
    { zero := BitVec.ofNat 26 45824924, component := 5 },
    { zero := BitVec.ofNat 26 12299164, component := 20 },
    { zero := BitVec.ofNat 26 43859356, component := 13 },
    { zero := BitVec.ofNat 26 10333596, component := 14 },
    { zero := BitVec.ofNat 26 46086556, component := 5 },
    { zero := BitVec.ofNat 26 12560796, component := 13 },
    { zero := BitVec.ofNat 26 43073492, component := 26 },
    { zero := BitVec.ofNat 26 43626452, component := 19 },
    { zero := BitVec.ofNat 26 45300692, component := 53 },
    { zero := BitVec.ofNat 26 45853652, component := 5 },
    { zero := BitVec.ofNat 26 43335124, component := 26 },
    { zero := BitVec.ofNat 26 43888084, component := 19 },
    { zero := BitVec.ofNat 26 45562324, component := 62 },
    { zero := BitVec.ofNat 26 46115284, component := 5 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover155 : ActiveCover := {
  active := BitVec.ofNat 14 4098
  strata := [
    { zero := BitVec.ofNat 26 1155070, component := 38 },
    { zero := BitVec.ofNat 26 1416702, component := 38 },
    { zero := BitVec.ofNat 26 3251966, component := 38 },
    { zero := BitVec.ofNat 26 3513598, component := 38 },
    { zero := BitVec.ofNat 26 35200958, component := 40 },
    { zero := BitVec.ofNat 26 1675198, component := 34 },
    { zero := BitVec.ofNat 26 35462590, component := 40 },
    { zero := BitVec.ofNat 26 1936830, component := 34 },
    { zero := BitVec.ofNat 26 37297854, component := 22 },
    { zero := BitVec.ofNat 26 3772094, component := 42 },
    { zero := BitVec.ofNat 26 37559486, component := 22 },
    { zero := BitVec.ofNat 26 4033726, component := 33 },
    { zero := BitVec.ofNat 26 34676726, component := 26 },
    { zero := BitVec.ofNat 26 35229686, component := 38 },
    { zero := BitVec.ofNat 26 34938358, component := 26 },
    { zero := BitVec.ofNat 26 35491318, component := 38 },
    { zero := BitVec.ofNat 26 36773622, component := 21 },
    { zero := BitVec.ofNat 26 37326582, component := 38 },
    { zero := BitVec.ofNat 26 37035254, component := 21 },
    { zero := BitVec.ofNat 26 37588214, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover156 : ActiveCover := {
  active := BitVec.ofNat 14 4100
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover157 : ActiveCover := {
  active := BitVec.ofNat 14 4104
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover158 : ActiveCover := {
  active := BitVec.ofNat 14 4105
  strata := [
    { zero := BitVec.ofNat 26 1555800, component := 64 },
    { zero := BitVec.ofNat 26 3651928, component := 64 },
    { zero := BitVec.ofNat 26 35601688, component := 64 },
    { zero := BitVec.ofNat 26 2075928, component := 35 },
    { zero := BitVec.ofNat 26 37697816, component := 64 },
    { zero := BitVec.ofNat 26 4172056, component := 26 },
    { zero := BitVec.ofNat 26 35077456, component := 62 },
    { zero := BitVec.ofNat 26 35630416, component := 37 },
    { zero := BitVec.ofNat 26 37173584, component := 62 },
    { zero := BitVec.ofNat 26 37726544, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover159 : ActiveCover := {
  active := BitVec.ofNat 14 4106
  strata := [
    { zero := BitVec.ofNat 26 1155064, component := 35 },
    { zero := BitVec.ofNat 26 1416696, component := 37 },
    { zero := BitVec.ofNat 26 35200952, component := 40 },
    { zero := BitVec.ofNat 26 1675192, component := 34 },
    { zero := BitVec.ofNat 26 35462584, component := 40 },
    { zero := BitVec.ofNat 26 1936824, component := 34 },
    { zero := BitVec.ofNat 26 34676720, component := 26 },
    { zero := BitVec.ofNat 26 35229680, component := 33 },
    { zero := BitVec.ofNat 26 34938352, component := 26 },
    { zero := BitVec.ofNat 26 35491312, component := 37 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover160 : ActiveCover := {
  active := BitVec.ofNat 14 4108
  strata := [
    { zero := BitVec.ofNat 26 37427889, component := 43 },
    { zero := BitVec.ofNat 26 37456561, component := 22 },
    { zero := BitVec.ofNat 26 37689393, component := 43 },
    { zero := BitVec.ofNat 26 37718065, component := 26 },
    { zero := BitVec.ofNat 26 37436080, component := 22 },
    { zero := BitVec.ofNat 26 37464752, component := 22 },
    { zero := BitVec.ofNat 26 37697712, component := 22 },
    { zero := BitVec.ofNat 26 37726384, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover161 : ActiveCover := {
  active := BitVec.ofNat 14 4109
  strata := [
    { zero := BitVec.ofNat 26 37697552, component := 53 },
    { zero := BitVec.ofNat 26 37726224, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover162 : ActiveCover := {
  active := BitVec.ofNat 14 4110
  strata := [
    { zero := BitVec.ofNat 26 37297840, component := 22 },
    { zero := BitVec.ofNat 26 37326512, component := 22 },
    { zero := BitVec.ofNat 26 37559472, component := 22 },
    { zero := BitVec.ofNat 26 37588144, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover163 : ActiveCover := {
  active := BitVec.ofNat 14 4112
  strata := [
    { zero := BitVec.ofNat 26 1286119, component := 38 },
    { zero := BitVec.ofNat 26 1806311, component := 38 },
    { zero := BitVec.ofNat 26 11640551, component := 38 },
    { zero := BitVec.ofNat 26 12160743, component := 38 },
    { zero := BitVec.ofNat 26 3381991, component := 41 },
    { zero := BitVec.ofNat 26 3902183, component := 41 },
    { zero := BitVec.ofNat 26 1547623, component := 49 },
    { zero := BitVec.ofNat 26 2067815, component := 37 },
    { zero := BitVec.ofNat 26 11902055, component := 15 },
    { zero := BitVec.ofNat 26 12422247, component := 15 },
    { zero := BitVec.ofNat 26 3643495, component := 26 },
    { zero := BitVec.ofNat 26 4163687, component := 26 },
    { zero := BitVec.ofNat 26 1555783, component := 62 },
    { zero := BitVec.ofNat 26 2075975, component := 37 },
    { zero := BitVec.ofNat 26 11910215, component := 15 },
    { zero := BitVec.ofNat 26 12430407, component := 15 },
    { zero := BitVec.ofNat 26 3651655, component := 26 },
    { zero := BitVec.ofNat 26 4171847, component := 26 },
    { zero := BitVec.ofNat 26 9543653, component := 15 },
    { zero := BitVec.ofNat 26 10063845, component := 15 },
    { zero := BitVec.ofNat 26 11770853, component := 18 },
    { zero := BitVec.ofNat 26 12291045, component := 18 },
    { zero := BitVec.ofNat 26 9805157, component := 16 },
    { zero := BitVec.ofNat 26 10325349, component := 16 },
    { zero := BitVec.ofNat 26 12032357, component := 49 },
    { zero := BitVec.ofNat 26 12552549, component := 17 },
    { zero := BitVec.ofNat 26 9813317, component := 16 },
    { zero := BitVec.ofNat 26 10333509, component := 16 },
    { zero := BitVec.ofNat 26 12040517, component := 62 },
    { zero := BitVec.ofNat 26 12560709, component := 17 },
    { zero := BitVec.ofNat 26 1294278, component := 38 },
    { zero := BitVec.ofNat 26 1814470, component := 38 },
    { zero := BitVec.ofNat 26 1555910, component := 38 },
    { zero := BitVec.ofNat 26 2076102, component := 38 },
    { zero := BitVec.ofNat 26 11648710, component := 38 },
    { zero := BitVec.ofNat 26 12168902, component := 20 },
    { zero := BitVec.ofNat 26 3390150, component := 66 },
    { zero := BitVec.ofNat 26 3910342, component := 41 },
    { zero := BitVec.ofNat 26 11910342, component := 38 },
    { zero := BitVec.ofNat 26 12430534, component := 38 },
    { zero := BitVec.ofNat 26 3651782, component := 61 },
    { zero := BitVec.ofNat 26 4171974, component := 26 },
    { zero := BitVec.ofNat 26 9551812, component := 26 },
    { zero := BitVec.ofNat 26 10072004, component := 19 },
    { zero := BitVec.ofNat 26 11779012, component := 65 },
    { zero := BitVec.ofNat 26 12299204, component := 20 },
    { zero := BitVec.ofNat 26 9813444, component := 37 },
    { zero := BitVec.ofNat 26 10333636, component := 19 },
    { zero := BitVec.ofNat 26 12040644, component := 62 },
    { zero := BitVec.ofNat 26 12560836, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover164 : ActiveCover := {
  active := BitVec.ofNat 14 4114
  strata := [
    { zero := BitVec.ofNat 26 1155046, component := 38 },
    { zero := BitVec.ofNat 26 1675238, component := 38 },
    { zero := BitVec.ofNat 26 1416678, component := 38 },
    { zero := BitVec.ofNat 26 1936870, component := 38 },
    { zero := BitVec.ofNat 26 3251942, component := 38 },
    { zero := BitVec.ofNat 26 3772134, component := 38 },
    { zero := BitVec.ofNat 26 3513574, component := 38 },
    { zero := BitVec.ofNat 26 4033766, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover165 : ActiveCover := {
  active := BitVec.ofNat 14 4116
  strata := [
    { zero := BitVec.ofNat 26 12160677, component := 18 },
    { zero := BitVec.ofNat 26 12290725, component := 18 },
    { zero := BitVec.ofNat 26 12422181, component := 15 },
    { zero := BitVec.ofNat 26 12552229, component := 26 },
    { zero := BitVec.ofNat 26 12430341, component := 15 },
    { zero := BitVec.ofNat 26 12560389, component := 26 },
    { zero := BitVec.ofNat 26 12168836, component := 20 },
    { zero := BitVec.ofNat 26 12298884, component := 20 },
    { zero := BitVec.ofNat 26 12430468, component := 19 },
    { zero := BitVec.ofNat 26 12560516, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover166 : ActiveCover := {
  active := BitVec.ofNat 14 4120
  strata := [
    { zero := BitVec.ofNat 26 1286113, component := 26 },
    { zero := BitVec.ofNat 26 1806305, component := 33 },
    { zero := BitVec.ofNat 26 3382241, component := 52 },
    { zero := BitVec.ofNat 26 3902433, component := 42 },
    { zero := BitVec.ofNat 26 1547617, component := 49 },
    { zero := BitVec.ofNat 26 2067809, component := 37 },
    { zero := BitVec.ofNat 26 3643745, component := 49 },
    { zero := BitVec.ofNat 26 4163937, component := 26 },
    { zero := BitVec.ofNat 26 1294304, component := 26 },
    { zero := BitVec.ofNat 26 1814496, component := 33 },
    { zero := BitVec.ofNat 26 3390432, component := 65 },
    { zero := BitVec.ofNat 26 3910624, component := 42 },
    { zero := BitVec.ofNat 26 1555936, component := 62 },
    { zero := BitVec.ofNat 26 2076128, component := 37 },
    { zero := BitVec.ofNat 26 3652064, component := 62 },
    { zero := BitVec.ofNat 26 4172256, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover167 : ActiveCover := {
  active := BitVec.ofNat 14 4121
  strata := [
    { zero := BitVec.ofNat 26 1555776, component := 62 },
    { zero := BitVec.ofNat 26 2075968, component := 37 },
    { zero := BitVec.ofNat 26 3651904, component := 62 },
    { zero := BitVec.ofNat 26 4172096, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover168 : ActiveCover := {
  active := BitVec.ofNat 14 4122
  strata := [
    { zero := BitVec.ofNat 26 1155040, component := 26 },
    { zero := BitVec.ofNat 26 1675232, component := 33 },
    { zero := BitVec.ofNat 26 1416672, component := 37 },
    { zero := BitVec.ofNat 26 1936864, component := 37 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover169 : ActiveCover := {
  active := BitVec.ofNat 14 4124
  strata := [
    { zero := BitVec.ofNat 26 3902113, component := 42 },
    { zero := BitVec.ofNat 26 4163617, component := 26 },
    { zero := BitVec.ofNat 26 3910304, component := 42 },
    { zero := BitVec.ofNat 26 4171936, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover170 : ActiveCover := {
  active := BitVec.ofNat 14 4125
  strata := [
    { zero := BitVec.ofNat 26 4171776, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover171 : ActiveCover := {
  active := BitVec.ofNat 14 4126
  strata := [
    { zero := BitVec.ofNat 26 3772064, component := 42 },
    { zero := BitVec.ofNat 26 4033696, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover172 : ActiveCover := {
  active := BitVec.ofNat 14 4160
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover173 : ActiveCover := {
  active := BitVec.ofNat 14 4162
  strata := [
    { zero := BitVec.ofNat 26 1150942, component := 38 },
    { zero := BitVec.ofNat 26 1412574, component := 38 },
    { zero := BitVec.ofNat 26 3247838, component := 38 },
    { zero := BitVec.ofNat 26 3509470, component := 38 },
    { zero := BitVec.ofNat 26 34705366, component := 38 },
    { zero := BitVec.ofNat 26 34966998, component := 38 },
    { zero := BitVec.ofNat 26 36802262, component := 38 },
    { zero := BitVec.ofNat 26 37063894, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover174 : ActiveCover := {
  active := BitVec.ofNat 14 4171
  strata := [
    { zero := BitVec.ofNat 26 1412440, component := 37 },
    { zero := BitVec.ofNat 26 34966864, component := 37 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover175 : ActiveCover := {
  active := BitVec.ofNat 14 4176
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover176 : ActiveCover := {
  active := BitVec.ofNat 14 4178
  strata := [
    { zero := BitVec.ofNat 26 1150918, component := 38 },
    { zero := BitVec.ofNat 26 1412550, component := 38 },
    { zero := BitVec.ofNat 26 3247814, component := 38 },
    { zero := BitVec.ofNat 26 3509446, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover177 : ActiveCover := {
  active := BitVec.ofNat 14 4187
  strata := [
    { zero := BitVec.ofNat 26 1412416, component := 37 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover178 : ActiveCover := {
  active := BitVec.ofNat 14 4224
  strata := [
    { zero := BitVec.ofNat 26 1285951, component := 51 },
    { zero := BitVec.ofNat 26 34807615, component := 51 },
    { zero := BitVec.ofNat 26 11640383, component := 18 },
    { zero := BitVec.ofNat 26 45162047, component := 2 },
    { zero := BitVec.ofNat 26 3381823, component := 52 },
    { zero := BitVec.ofNat 26 36903487, component := 43 },
    { zero := BitVec.ofNat 26 1294111, component := 64 },
    { zero := BitVec.ofNat 26 34815775, component := 64 },
    { zero := BitVec.ofNat 26 11648543, component := 18 },
    { zero := BitVec.ofNat 26 45170207, component := 2 },
    { zero := BitVec.ofNat 26 3389983, component := 65 },
    { zero := BitVec.ofNat 26 36911647, component := 53 },
    { zero := BitVec.ofNat 26 9543485, component := 11 },
    { zero := BitVec.ofNat 26 43065149, component := 10 },
    { zero := BitVec.ofNat 26 11770685, component := 51 },
    { zero := BitVec.ofNat 26 45292349, component := 51 },
    { zero := BitVec.ofNat 26 9551645, component := 11 },
    { zero := BitVec.ofNat 26 43073309, component := 10 },
    { zero := BitVec.ofNat 26 11778845, component := 64 },
    { zero := BitVec.ofNat 26 45300509, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover179 : ActiveCover := {
  active := BitVec.ofNat 14 4228
  strata := [
    { zero := BitVec.ofNat 26 45162037, component := 2 },
    { zero := BitVec.ofNat 26 45292085, component := 2 },
    { zero := BitVec.ofNat 26 45170197, component := 2 },
    { zero := BitVec.ofNat 26 45300245, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover180 : ActiveCover := {
  active := BitVec.ofNat 14 4232
  strata := [
    { zero := BitVec.ofNat 26 1285945, component := 51 },
    { zero := BitVec.ofNat 26 34807609, component := 51 },
    { zero := BitVec.ofNat 26 3382073, component := 51 },
    { zero := BitVec.ofNat 26 36903737, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover181 : ActiveCover := {
  active := BitVec.ofNat 14 4233
  strata := [
    { zero := BitVec.ofNat 26 1294104, component := 64 },
    { zero := BitVec.ofNat 26 34815768, component := 64 },
    { zero := BitVec.ofNat 26 3390232, component := 64 },
    { zero := BitVec.ofNat 26 36911896, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover182 : ActiveCover := {
  active := BitVec.ofNat 14 4236
  strata := [
    { zero := BitVec.ofNat 26 36903473, component := 43 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover183 : ActiveCover := {
  active := BitVec.ofNat 14 4237
  strata := [
    { zero := BitVec.ofNat 26 36911632, component := 53 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover184 : ActiveCover := {
  active := BitVec.ofNat 14 4244
  strata := [
    { zero := BitVec.ofNat 26 11640357, component := 18 },
    { zero := BitVec.ofNat 26 11770405, component := 18 },
    { zero := BitVec.ofNat 26 11648517, component := 18 },
    { zero := BitVec.ofNat 26 11778565, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover185 : ActiveCover := {
  active := BitVec.ofNat 14 4252
  strata := [
    { zero := BitVec.ofNat 26 3381793, component := 52 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover186 : ActiveCover := {
  active := BitVec.ofNat 14 4253
  strata := [
    { zero := BitVec.ofNat 26 3389952, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover187 : ActiveCover := {
  active := BitVec.ofNat 14 4288
  strata := [
    { zero := BitVec.ofNat 26 1281823, component := 35 },
    { zero := BitVec.ofNat 26 11636255, component := 18 },
    { zero := BitVec.ofNat 26 3377695, component := 26 },
    { zero := BitVec.ofNat 26 9539357, component := 11 },
    { zero := BitVec.ofNat 26 11766557, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover188 : ActiveCover := {
  active := BitVec.ofNat 14 4292
  strata := [
    { zero := BitVec.ofNat 26 45190677, component := 2 },
    { zero := BitVec.ofNat 26 45320725, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover189 : ActiveCover := {
  active := BitVec.ofNat 14 4299
  strata := [
    { zero := BitVec.ofNat 26 1150744, component := 35 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover190 : ActiveCover := {
  active := BitVec.ofNat 14 4303
  strata := [
    { zero := BitVec.ofNat 26 36802064, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover191 : ActiveCover := {
  active := BitVec.ofNat 14 4308
  strata := [
    { zero := BitVec.ofNat 26 11636229, component := 18 },
    { zero := BitVec.ofNat 26 11766277, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover192 : ActiveCover := {
  active := BitVec.ofNat 14 4319
  strata := [
    { zero := BitVec.ofNat 26 3247616, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover193 : ActiveCover := {
  active := BitVec.ofNat 14 4608
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover194 : ActiveCover := {
  active := BitVec.ofNat 14 4610
  strata := [
    { zero := BitVec.ofNat 26 105982, component := 38 },
    { zero := BitVec.ofNat 26 2202878, component := 38 },
    { zero := BitVec.ofNat 26 34151870, component := 40 },
    { zero := BitVec.ofNat 26 626110, component := 34 },
    { zero := BitVec.ofNat 26 36248766, component := 22 },
    { zero := BitVec.ofNat 26 2723006, component := 33 },
    { zero := BitVec.ofNat 26 33627638, component := 26 },
    { zero := BitVec.ofNat 26 34180598, component := 38 },
    { zero := BitVec.ofNat 26 35724534, component := 21 },
    { zero := BitVec.ofNat 26 36277494, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover195 : ActiveCover := {
  active := BitVec.ofNat 14 4612
  strata := [
    { zero := BitVec.ofNat 26 44637365, component := 2 },
    { zero := BitVec.ofNat 26 44666037, component := 2 },
    { zero := BitVec.ofNat 26 44767413, component := 2 },
    { zero := BitVec.ofNat 26 44796085, component := 2 },
    { zero := BitVec.ofNat 26 44645524, component := 5 },
    { zero := BitVec.ofNat 26 44674196, component := 5 },
    { zero := BitVec.ofNat 26 44775572, component := 5 },
    { zero := BitVec.ofNat 26 44804244, component := 5 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover196 : ActiveCover := {
  active := BitVec.ofNat 14 4616
  strata := [
    { zero := BitVec.ofNat 26 237049, component := 51 },
    { zero := BitVec.ofNat 26 2333177, component := 51 },
    { zero := BitVec.ofNat 26 34282937, component := 51 },
    { zero := BitVec.ofNat 26 757177, component := 34 },
    { zero := BitVec.ofNat 26 36379065, component := 51 },
    { zero := BitVec.ofNat 26 2853305, component := 40 },
    { zero := BitVec.ofNat 26 33758705, component := 26 },
    { zero := BitVec.ofNat 26 34311665, component := 33 },
    { zero := BitVec.ofNat 26 35854833, component := 43 },
    { zero := BitVec.ofNat 26 36407793, component := 22 },
    { zero := BitVec.ofNat 26 245240, component := 64 },
    { zero := BitVec.ofNat 26 2341368, component := 64 },
    { zero := BitVec.ofNat 26 34291128, component := 64 },
    { zero := BitVec.ofNat 26 765368, component := 34 },
    { zero := BitVec.ofNat 26 36387256, component := 64 },
    { zero := BitVec.ofNat 26 2861496, component := 40 },
    { zero := BitVec.ofNat 26 33766896, component := 26 },
    { zero := BitVec.ofNat 26 34319856, component := 33 },
    { zero := BitVec.ofNat 26 35863024, component := 53 },
    { zero := BitVec.ofNat 26 36415984, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover197 : ActiveCover := {
  active := BitVec.ofNat 14 4618
  strata := [
    { zero := BitVec.ofNat 26 105976, component := 35 },
    { zero := BitVec.ofNat 26 34151864, component := 40 },
    { zero := BitVec.ofNat 26 626104, component := 34 },
    { zero := BitVec.ofNat 26 33627632, component := 26 },
    { zero := BitVec.ofNat 26 34180592, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover198 : ActiveCover := {
  active := BitVec.ofNat 14 4620
  strata := [
    { zero := BitVec.ofNat 26 36378801, component := 43 },
    { zero := BitVec.ofNat 26 36407473, component := 22 },
    { zero := BitVec.ofNat 26 36386992, component := 22 },
    { zero := BitVec.ofNat 26 36415664, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover199 : ActiveCover := {
  active := BitVec.ofNat 14 4622
  strata := [
    { zero := BitVec.ofNat 26 36248752, component := 22 },
    { zero := BitVec.ofNat 26 36277424, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover200 : ActiveCover := {
  active := BitVec.ofNat 14 4656
  strata := [
    { zero := BitVec.ofNat 26 236775, component := 38 },
    { zero := BitVec.ofNat 26 8494311, component := 38 },
    { zero := BitVec.ofNat 26 756967, component := 38 },
    { zero := BitVec.ofNat 26 9014503, component := 38 },
    { zero := BitVec.ofNat 26 244934, component := 38 },
    { zero := BitVec.ofNat 26 8502470, component := 38 },
    { zero := BitVec.ofNat 26 765126, component := 38 },
    { zero := BitVec.ofNat 26 9022662, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover201 : ActiveCover := {
  active := BitVec.ofNat 14 4658
  strata := [
    { zero := BitVec.ofNat 26 105702, component := 38 },
    { zero := BitVec.ofNat 26 625894, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover202 : ActiveCover := {
  active := BitVec.ofNat 14 4660
  strata := [
    { zero := BitVec.ofNat 26 9014437, component := 15 },
    { zero := BitVec.ofNat 26 9022596, component := 19 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover203 : ActiveCover := {
  active := BitVec.ofNat 14 4668
  strata := [
    { zero := BitVec.ofNat 26 756897, component := 33 },
    { zero := BitVec.ofNat 26 765088, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover204 : ActiveCover := {
  active := BitVec.ofNat 14 4670
  strata := [
    { zero := BitVec.ofNat 26 625824, component := 33 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover205 : ActiveCover := {
  active := BitVec.ofNat 14 4672
  strata := [
    { zero := BitVec.ofNat 26 232927, component := 38 },
    { zero := BitVec.ofNat 26 10587359, component := 38 },
    { zero := BitVec.ofNat 26 2328799, component := 26 },
    { zero := BitVec.ofNat 26 33787351, component := 38 },
    { zero := BitVec.ofNat 26 44141783, component := 38 },
    { zero := BitVec.ofNat 26 35883223, component := 21 },
    { zero := BitVec.ofNat 26 8490461, component := 11 },
    { zero := BitVec.ofNat 26 10717661, component := 10 },
    { zero := BitVec.ofNat 26 42044885, component := 15 },
    { zero := BitVec.ofNat 26 44272085, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover206 : ActiveCover := {
  active := BitVec.ofNat 14 4674
  strata := [
    { zero := BitVec.ofNat 26 101854, component := 38 },
    { zero := BitVec.ofNat 26 2198750, component := 38 },
    { zero := BitVec.ofNat 26 33656278, component := 38 },
    { zero := BitVec.ofNat 26 35753174, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover207 : ActiveCover := {
  active := BitVec.ofNat 14 4720
  strata := [
    { zero := BitVec.ofNat 26 232647, component := 38 },
    { zero := BitVec.ofNat 26 8490183, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover208 : ActiveCover := {
  active := BitVec.ofNat 14 4722
  strata := [
    { zero := BitVec.ofNat 26 101574, component := 38 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover209 : ActiveCover := {
  active := BitVec.ofNat 14 4736
  strata := [
    { zero := BitVec.ofNat 26 236863, component := 51 },
    { zero := BitVec.ofNat 26 33758527, component := 51 },
    { zero := BitVec.ofNat 26 10591295, component := 15 },
    { zero := BitVec.ofNat 26 44112959, component := 2 },
    { zero := BitVec.ofNat 26 2332735, component := 26 },
    { zero := BitVec.ofNat 26 35854399, component := 43 },
    { zero := BitVec.ofNat 26 245023, component := 64 },
    { zero := BitVec.ofNat 26 33766687, component := 64 },
    { zero := BitVec.ofNat 26 10599455, component := 15 },
    { zero := BitVec.ofNat 26 44121119, component := 2 },
    { zero := BitVec.ofNat 26 2340895, component := 26 },
    { zero := BitVec.ofNat 26 35862559, component := 53 },
    { zero := BitVec.ofNat 26 8494397, component := 11 },
    { zero := BitVec.ofNat 26 42016061, component := 10 },
    { zero := BitVec.ofNat 26 10721597, component := 51 },
    { zero := BitVec.ofNat 26 44243261, component := 51 },
    { zero := BitVec.ofNat 26 8502557, component := 11 },
    { zero := BitVec.ofNat 26 42024221, component := 10 },
    { zero := BitVec.ofNat 26 10729757, component := 64 },
    { zero := BitVec.ofNat 26 44251421, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover210 : ActiveCover := {
  active := BitVec.ofNat 14 4740
  strata := [
    { zero := BitVec.ofNat 26 44112949, component := 2 },
    { zero := BitVec.ofNat 26 44242997, component := 2 },
    { zero := BitVec.ofNat 26 44121109, component := 2 },
    { zero := BitVec.ofNat 26 44251157, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover211 : ActiveCover := {
  active := BitVec.ofNat 14 4744
  strata := [
    { zero := BitVec.ofNat 26 236857, component := 51 },
    { zero := BitVec.ofNat 26 33758521, component := 51 },
    { zero := BitVec.ofNat 26 2332985, component := 51 },
    { zero := BitVec.ofNat 26 35854649, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover212 : ActiveCover := {
  active := BitVec.ofNat 14 4745
  strata := [
    { zero := BitVec.ofNat 26 245016, component := 64 },
    { zero := BitVec.ofNat 26 33766680, component := 64 },
    { zero := BitVec.ofNat 26 2341144, component := 64 },
    { zero := BitVec.ofNat 26 35862808, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover213 : ActiveCover := {
  active := BitVec.ofNat 14 4748
  strata := [
    { zero := BitVec.ofNat 26 35854385, component := 43 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover214 : ActiveCover := {
  active := BitVec.ofNat 14 4749
  strata := [
    { zero := BitVec.ofNat 26 35862544, component := 53 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover215 : ActiveCover := {
  active := BitVec.ofNat 14 4788
  strata := [
    { zero := BitVec.ofNat 26 8494117, component := 15 },
    { zero := BitVec.ofNat 26 8502277, component := 15 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover216 : ActiveCover := {
  active := BitVec.ofNat 14 4796
  strata := [
    { zero := BitVec.ofNat 26 236577, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover217 : ActiveCover := {
  active := BitVec.ofNat 14 4797
  strata := [
    { zero := BitVec.ofNat 26 244736, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover218 : ActiveCover := {
  active := BitVec.ofNat 14 4800
  strata := [
    { zero := BitVec.ofNat 26 232735, component := 35 },
    { zero := BitVec.ofNat 26 10587167, component := 15 },
    { zero := BitVec.ofNat 26 2328607, component := 26 },
    { zero := BitVec.ofNat 26 8490269, component := 11 },
    { zero := BitVec.ofNat 26 10717469, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover219 : ActiveCover := {
  active := BitVec.ofNat 14 4804
  strata := [
    { zero := BitVec.ofNat 26 44141589, component := 2 },
    { zero := BitVec.ofNat 26 44271637, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover220 : ActiveCover := {
  active := BitVec.ofNat 14 4811
  strata := [
    { zero := BitVec.ofNat 26 101656, component := 35 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover221 : ActiveCover := {
  active := BitVec.ofNat 14 4815
  strata := [
    { zero := BitVec.ofNat 26 35752976, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover222 : ActiveCover := {
  active := BitVec.ofNat 14 4852
  strata := [
    { zero := BitVec.ofNat 26 8489989, component := 15 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover223 : ActiveCover := {
  active := BitVec.ofNat 14 4863
  strata := [
    { zero := BitVec.ofNat 26 101376, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover224 : ActiveCover := {
  active := BitVec.ofNat 14 5120
  strata := [
    { zero := BitVec.ofNat 26 45681343, component := 2 },
    { zero := BitVec.ofNat 26 45942847, component := 2 },
    { zero := BitVec.ofNat 26 45951007, component := 2 },
    { zero := BitVec.ofNat 26 45681399, component := 2 },
    { zero := BitVec.ofNat 26 45942903, component := 2 },
    { zero := BitVec.ofNat 26 45951063, component := 2 },
    { zero := BitVec.ofNat 26 45681597, component := 2 },
    { zero := BitVec.ofNat 26 45943101, component := 2 },
    { zero := BitVec.ofNat 26 45951261, component := 2 },
    { zero := BitVec.ofNat 26 45681653, component := 2 },
    { zero := BitVec.ofNat 26 45943157, component := 2 },
    { zero := BitVec.ofNat 26 45951317, component := 2 },
    { zero := BitVec.ofNat 26 45689502, component := 5 },
    { zero := BitVec.ofNat 26 45951134, component := 5 },
    { zero := BitVec.ofNat 26 45689558, component := 5 },
    { zero := BitVec.ofNat 26 45951190, component := 5 },
    { zero := BitVec.ofNat 26 45689756, component := 5 },
    { zero := BitVec.ofNat 26 45951388, component := 5 },
    { zero := BitVec.ofNat 26 45689812, component := 5 },
    { zero := BitVec.ofNat 26 45951444, component := 5 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover225 : ActiveCover := {
  active := BitVec.ofNat 14 5122
  strata := [
    { zero := BitVec.ofNat 26 37292734, component := 22 },
    { zero := BitVec.ofNat 26 37554366, component := 22 },
    { zero := BitVec.ofNat 26 37292790, component := 21 },
    { zero := BitVec.ofNat 26 37554422, component := 21 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover226 : ActiveCover := {
  active := BitVec.ofNat 14 5124
  strata := [
    { zero := BitVec.ofNat 26 45681333, component := 2 },
    { zero := BitVec.ofNat 26 45942837, component := 2 },
    { zero := BitVec.ofNat 26 45950997, component := 2 },
    { zero := BitVec.ofNat 26 45689492, component := 5 },
    { zero := BitVec.ofNat 26 45951124, component := 5 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover227 : ActiveCover := {
  active := BitVec.ofNat 14 5130
  strata := [
    { zero := BitVec.ofNat 26 37292984, component := 22 },
    { zero := BitVec.ofNat 26 37554616, component := 22 },
    { zero := BitVec.ofNat 26 37293040, component := 22 },
    { zero := BitVec.ofNat 26 37554672, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover228 : ActiveCover := {
  active := BitVec.ofNat 14 5134
  strata := [
    { zero := BitVec.ofNat 26 37292720, component := 22 },
    { zero := BitVec.ofNat 26 37554352, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover229 : ActiveCover := {
  active := BitVec.ofNat 14 5184
  strata := [
    { zero := BitVec.ofNat 26 45157079, component := 2 },
    { zero := BitVec.ofNat 26 45418583, component := 2 },
    { zero := BitVec.ofNat 26 45157333, component := 2 },
    { zero := BitVec.ofNat 26 45418837, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover230 : ActiveCover := {
  active := BitVec.ofNat 14 5186
  strata := [
    { zero := BitVec.ofNat 26 36768470, component := 21 },
    { zero := BitVec.ofNat 26 37030102, component := 21 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover231 : ActiveCover := {
  active := BitVec.ofNat 14 5195
  strata := [
    { zero := BitVec.ofNat 26 37030224, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover232 : ActiveCover := {
  active := BitVec.ofNat 14 5312
  strata := [
    { zero := BitVec.ofNat 26 45156895, component := 2 },
    { zero := BitVec.ofNat 26 45157149, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover233 : ActiveCover := {
  active := BitVec.ofNat 14 5316
  strata := [
    { zero := BitVec.ofNat 26 45156885, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover234 : ActiveCover := {
  active := BitVec.ofNat 14 5323
  strata := [
    { zero := BitVec.ofNat 26 36768536, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover235 : ActiveCover := {
  active := BitVec.ofNat 14 5327
  strata := [
    { zero := BitVec.ofNat 26 36768272, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover236 : ActiveCover := {
  active := BitVec.ofNat 14 5632
  strata := [
    { zero := BitVec.ofNat 26 44632255, component := 2 },
    { zero := BitVec.ofNat 26 44632311, component := 2 },
    { zero := BitVec.ofNat 26 44632509, component := 2 },
    { zero := BitVec.ofNat 26 44632565, component := 2 },
    { zero := BitVec.ofNat 26 44640414, component := 5 },
    { zero := BitVec.ofNat 26 44640470, component := 5 },
    { zero := BitVec.ofNat 26 44640668, component := 5 },
    { zero := BitVec.ofNat 26 44640724, component := 5 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover237 : ActiveCover := {
  active := BitVec.ofNat 14 5634
  strata := [
    { zero := BitVec.ofNat 26 36243646, component := 22 },
    { zero := BitVec.ofNat 26 36243702, component := 21 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover238 : ActiveCover := {
  active := BitVec.ofNat 14 5636
  strata := [
    { zero := BitVec.ofNat 26 44632245, component := 2 },
    { zero := BitVec.ofNat 26 44640404, component := 5 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover239 : ActiveCover := {
  active := BitVec.ofNat 14 5642
  strata := [
    { zero := BitVec.ofNat 26 36243896, component := 22 },
    { zero := BitVec.ofNat 26 36243952, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover240 : ActiveCover := {
  active := BitVec.ofNat 14 5646
  strata := [
    { zero := BitVec.ofNat 26 36243632, component := 22 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover241 : ActiveCover := {
  active := BitVec.ofNat 14 5696
  strata := [
    { zero := BitVec.ofNat 26 44107991, component := 2 },
    { zero := BitVec.ofNat 26 44108245, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover242 : ActiveCover := {
  active := BitVec.ofNat 14 5698
  strata := [
    { zero := BitVec.ofNat 26 35719382, component := 21 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover243 : ActiveCover := {
  active := BitVec.ofNat 14 5824
  strata := [
    { zero := BitVec.ofNat 26 44107807, component := 2 },
    { zero := BitVec.ofNat 26 44108061, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover244 : ActiveCover := {
  active := BitVec.ofNat 14 5828
  strata := [
    { zero := BitVec.ofNat 26 44107797, component := 2 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover245 : ActiveCover := {
  active := BitVec.ofNat 14 5835
  strata := [
    { zero := BitVec.ofNat 26 35719448, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover246 : ActiveCover := {
  active := BitVec.ofNat 14 5839
  strata := [
    { zero := BitVec.ofNat 26 35719184, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover247 : ActiveCover := {
  active := BitVec.ofNat 14 8192
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover248 : ActiveCover := {
  active := BitVec.ofNat 14 8193
  strata := [
    { zero := BitVec.ofNat 26 22429514, component := 59 },
    { zero := BitVec.ofNat 26 32783946, component := 29 },
    { zero := BitVec.ofNat 26 24525386, component := 60 },
    { zero := BitVec.ofNat 26 22953738, component := 59 },
    { zero := BitVec.ofNat 26 33308170, component := 29 },
    { zero := BitVec.ofNat 26 25049610, component := 60 },
    { zero := BitVec.ofNat 26 30687048, component := 26 },
    { zero := BitVec.ofNat 26 32914248, component := 62 },
    { zero := BitVec.ofNat 26 31211272, component := 26 },
    { zero := BitVec.ofNat 26 33438472, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover249 : ActiveCover := {
  active := BitVec.ofNat 14 8194
  strata := [
    { zero := BitVec.ofNat 26 17850350, component := 26 },
    { zero := BitVec.ofNat 26 19947246, component := 41 },
    { zero := BitVec.ofNat 26 18374574, component := 39 },
    { zero := BitVec.ofNat 26 20471470, component := 42 },
    { zero := BitVec.ofNat 26 22028266, component := 26 },
    { zero := BitVec.ofNat 26 24125162, component := 29 },
    { zero := BitVec.ofNat 26 22552490, component := 31 },
    { zero := BitVec.ofNat 26 24649386, component := 30 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover250 : ActiveCover := {
  active := BitVec.ofNat 14 8200
  strata := [
    { zero := BitVec.ofNat 26 17981417, component := 50 },
    { zero := BitVec.ofNat 26 20077545, component := 50 },
    { zero := BitVec.ofNat 26 18243433, component := 50 },
    { zero := BitVec.ofNat 26 20339561, component := 50 },
    { zero := BitVec.ofNat 26 18505641, component := 50 },
    { zero := BitVec.ofNat 26 20601769, component := 50 },
    { zero := BitVec.ofNat 26 18767657, component := 50 },
    { zero := BitVec.ofNat 26 20863785, component := 50 },
    { zero := BitVec.ofNat 26 17989608, component := 63 },
    { zero := BitVec.ofNat 26 20085736, component := 63 },
    { zero := BitVec.ofNat 26 18513832, component := 63 },
    { zero := BitVec.ofNat 26 20609960, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover251 : ActiveCover := {
  active := BitVec.ofNat 14 8201
  strata := [
    { zero := BitVec.ofNat 26 18251592, component := 63 },
    { zero := BitVec.ofNat 26 20347720, component := 63 },
    { zero := BitVec.ofNat 26 18775816, component := 63 },
    { zero := BitVec.ofNat 26 20871944, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover252 : ActiveCover := {
  active := BitVec.ofNat 14 8202
  strata := [
    { zero := BitVec.ofNat 26 17850344, component := 26 },
    { zero := BitVec.ofNat 26 18374568, component := 39 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover253 : ActiveCover := {
  active := BitVec.ofNat 14 8320
  strata := [
    { zero := BitVec.ofNat 26 17981231, component := 50 },
    { zero := BitVec.ofNat 26 28335663, component := 18 },
    { zero := BitVec.ofNat 26 20077103, component := 52 },
    { zero := BitVec.ofNat 26 17989391, component := 63 },
    { zero := BitVec.ofNat 26 22167311, component := 59 },
    { zero := BitVec.ofNat 26 28343823, component := 18 },
    { zero := BitVec.ofNat 26 32521743, component := 18 },
    { zero := BitVec.ofNat 26 20085263, component := 65 },
    { zero := BitVec.ofNat 26 24263183, component := 60 },
    { zero := BitVec.ofNat 26 22159147, component := 47 },
    { zero := BitVec.ofNat 26 32513579, component := 29 },
    { zero := BitVec.ofNat 26 24255019, component := 48 },
    { zero := BitVec.ofNat 26 26238765, component := 9 },
    { zero := BitVec.ofNat 26 28465965, component := 50 },
    { zero := BitVec.ofNat 26 26246925, component := 9 },
    { zero := BitVec.ofNat 26 30424845, component := 26 },
    { zero := BitVec.ofNat 26 28474125, component := 63 },
    { zero := BitVec.ofNat 26 32652045, component := 18 },
    { zero := BitVec.ofNat 26 30416681, component := 26 },
    { zero := BitVec.ofNat 26 32643881, component := 52 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover254 : ActiveCover := {
  active := BitVec.ofNat 14 8321
  strata := [
    { zero := BitVec.ofNat 26 22167306, component := 59 },
    { zero := BitVec.ofNat 26 32521738, component := 29 },
    { zero := BitVec.ofNat 26 24263178, component := 60 },
    { zero := BitVec.ofNat 26 30424840, component := 26 },
    { zero := BitVec.ofNat 26 32652040, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover255 : ActiveCover := {
  active := BitVec.ofNat 14 8328
  strata := [
    { zero := BitVec.ofNat 26 17981225, component := 50 },
    { zero := BitVec.ofNat 26 20077353, component := 50 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover256 : ActiveCover := {
  active := BitVec.ofNat 14 8329
  strata := [
    { zero := BitVec.ofNat 26 17989384, component := 63 },
    { zero := BitVec.ofNat 26 20085512, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover257 : ActiveCover := {
  active := BitVec.ofNat 14 9216
  strata := [
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
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover258 : ActiveCover := {
  active := BitVec.ofNat 14 9217
  strata := [
    { zero := BitVec.ofNat 26 33303050, component := 29 },
    { zero := BitVec.ofNat 26 33303304, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover259 : ActiveCover := {
  active := BitVec.ofNat 14 9218
  strata := [
    { zero := BitVec.ofNat 26 20466350, component := 42 },
    { zero := BitVec.ofNat 26 24644266, component := 30 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover260 : ActiveCover := {
  active := BitVec.ofNat 14 9226
  strata := [
    { zero := BitVec.ofNat 26 20466600, component := 39 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover261 : ActiveCover := {
  active := BitVec.ofNat 14 9280
  strata := [
    { zero := BitVec.ofNat 26 28330703, component := 18 },
    { zero := BitVec.ofNat 26 32508623, component := 18 },
    { zero := BitVec.ofNat 26 28592719, component := 18 },
    { zero := BitVec.ofNat 26 32770639, component := 18 },
    { zero := BitVec.ofNat 26 28330957, component := 9 },
    { zero := BitVec.ofNat 26 32508877, component := 18 },
    { zero := BitVec.ofNat 26 28592973, component := 9 },
    { zero := BitVec.ofNat 26 32770893, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover262 : ActiveCover := {
  active := BitVec.ofNat 14 9282
  strata := [
    { zero := BitVec.ofNat 26 19942094, component := 41 },
    { zero := BitVec.ofNat 26 24120014, component := 41 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover263 : ActiveCover := {
  active := BitVec.ofNat 14 9283
  strata := [
    { zero := BitVec.ofNat 26 24382026, component := 29 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover264 : ActiveCover := {
  active := BitVec.ofNat 14 9291
  strata := [
    { zero := BitVec.ofNat 26 20204360, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover265 : ActiveCover := {
  active := BitVec.ofNat 14 9408
  strata := [
    { zero := BitVec.ofNat 26 28330511, component := 18 },
    { zero := BitVec.ofNat 26 32508431, component := 18 },
    { zero := BitVec.ofNat 26 28330765, component := 9 },
    { zero := BitVec.ofNat 26 32508685, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover266 : ActiveCover := {
  active := BitVec.ofNat 14 9411
  strata := [
    { zero := BitVec.ofNat 26 24119818, component := 29 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover267 : ActiveCover := {
  active := BitVec.ofNat 14 9419
  strata := [
    { zero := BitVec.ofNat 26 19942152, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover268 : ActiveCover := {
  active := BitVec.ofNat 14 10240
  strata := [
    { zero := BitVec.ofNat 26 17978351, component := 50 },
    { zero := BitVec.ofNat 26 18240367, component := 50 },
    { zero := BitVec.ofNat 26 18502575, component := 50 },
    { zero := BitVec.ofNat 26 18764591, component := 50 },
    { zero := BitVec.ofNat 26 18248527, component := 63 },
    { zero := BitVec.ofNat 26 18772751, component := 63 },
    { zero := BitVec.ofNat 26 22172651, component := 50 },
    { zero := BitVec.ofNat 26 22434667, component := 50 },
    { zero := BitVec.ofNat 26 22696875, component := 50 },
    { zero := BitVec.ofNat 26 22958891, component := 50 },
    { zero := BitVec.ofNat 26 26366957, component := 50 },
    { zero := BitVec.ofNat 26 26628973, component := 50 },
    { zero := BitVec.ofNat 26 26891181, component := 50 },
    { zero := BitVec.ofNat 26 27153197, component := 50 },
    { zero := BitVec.ofNat 26 26637133, component := 63 },
    { zero := BitVec.ofNat 26 27161357, component := 63 },
    { zero := BitVec.ofNat 26 30561257, component := 50 },
    { zero := BitVec.ofNat 26 30823273, component := 50 },
    { zero := BitVec.ofNat 26 31085481, component := 50 },
    { zero := BitVec.ofNat 26 31347497, component := 50 },
    { zero := BitVec.ofNat 26 17986510, component := 63 },
    { zero := BitVec.ofNat 26 18510734, component := 63 },
    { zero := BitVec.ofNat 26 22180842, component := 63 },
    { zero := BitVec.ofNat 26 22705066, component := 63 },
    { zero := BitVec.ofNat 26 26375116, component := 63 },
    { zero := BitVec.ofNat 26 26899340, component := 12 },
    { zero := BitVec.ofNat 26 30569448, component := 63 },
    { zero := BitVec.ofNat 26 31093672, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover269 : ActiveCover := {
  active := BitVec.ofNat 14 10241
  strata := [
    { zero := BitVec.ofNat 26 22442826, component := 63 },
    { zero := BitVec.ofNat 26 22967050, component := 63 },
    { zero := BitVec.ofNat 26 30831432, component := 63 },
    { zero := BitVec.ofNat 26 31355656, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover270 : ActiveCover := {
  active := BitVec.ofNat 14 10248
  strata := [
    { zero := BitVec.ofNat 26 17978345, component := 50 },
    { zero := BitVec.ofNat 26 18240361, component := 50 },
    { zero := BitVec.ofNat 26 18502569, component := 50 },
    { zero := BitVec.ofNat 26 18764585, component := 50 },
    { zero := BitVec.ofNat 26 17986536, component := 63 },
    { zero := BitVec.ofNat 26 18510760, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover271 : ActiveCover := {
  active := BitVec.ofNat 14 10249
  strata := [
    { zero := BitVec.ofNat 26 18248520, component := 63 },
    { zero := BitVec.ofNat 26 18772744, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover272 : ActiveCover := {
  active := BitVec.ofNat 14 10368
  strata := [
    { zero := BitVec.ofNat 26 17978159, component := 50 },
    { zero := BitVec.ofNat 26 17986319, component := 63 },
    { zero := BitVec.ofNat 26 22172459, component := 50 },
    { zero := BitVec.ofNat 26 26366765, component := 50 },
    { zero := BitVec.ofNat 26 26374925, component := 63 },
    { zero := BitVec.ofNat 26 30561065, component := 50 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover273 : ActiveCover := {
  active := BitVec.ofNat 14 10369
  strata := [
    { zero := BitVec.ofNat 26 22180618, component := 63 },
    { zero := BitVec.ofNat 26 30569224, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover274 : ActiveCover := {
  active := BitVec.ofNat 14 10376
  strata := [
    { zero := BitVec.ofNat 26 17978153, component := 50 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover275 : ActiveCover := {
  active := BitVec.ofNat 14 10377
  strata := [
    { zero := BitVec.ofNat 26 17986312, component := 63 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover276 : ActiveCover := {
  active := BitVec.ofNat 14 10496
  strata := [
    { zero := BitVec.ofNat 26 22425935, component := 59 },
    { zero := BitVec.ofNat 26 22950159, component := 59 },
    { zero := BitVec.ofNat 26 22417771, component := 47 },
    { zero := BitVec.ofNat 26 22941995, component := 47 },
    { zero := BitVec.ofNat 26 30814541, component := 62 },
    { zero := BitVec.ofNat 26 31338765, component := 26 },
    { zero := BitVec.ofNat 26 30806377, component := 49 },
    { zero := BitVec.ofNat 26 31330601, component := 26 },
    { zero := BitVec.ofNat 26 22426062, component := 59 },
    { zero := BitVec.ofNat 26 22950286, component := 59 },
    { zero := BitVec.ofNat 26 22426090, component := 59 },
    { zero := BitVec.ofNat 26 22950314, component := 59 },
    { zero := BitVec.ofNat 26 30814668, component := 62 },
    { zero := BitVec.ofNat 26 31338892, component := 26 },
    { zero := BitVec.ofNat 26 30814696, component := 62 },
    { zero := BitVec.ofNat 26 31338920, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover277 : ActiveCover := {
  active := BitVec.ofNat 14 10497
  strata := [
    { zero := BitVec.ofNat 26 22425930, component := 59 },
    { zero := BitVec.ofNat 26 22950154, component := 59 },
    { zero := BitVec.ofNat 26 30814536, component := 62 },
    { zero := BitVec.ofNat 26 31338760, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover278 : ActiveCover := {
  active := BitVec.ofNat 14 11008
  strata := [
    { zero := BitVec.ofNat 26 21107195, component := 51 },
    { zero := BitVec.ofNat 26 21631419, component := 51 },
    { zero := BitVec.ofNat 26 29495801, component := 51 },
    { zero := BitVec.ofNat 26 30020025, component := 51 },
    { zero := BitVec.ofNat 26 21115358, component := 64 },
    { zero := BitVec.ofNat 26 21639582, component := 64 },
    { zero := BitVec.ofNat 26 21115386, component := 64 },
    { zero := BitVec.ofNat 26 21639610, component := 64 },
    { zero := BitVec.ofNat 26 29503964, component := 64 },
    { zero := BitVec.ofNat 26 30028188, component := 64 },
    { zero := BitVec.ofNat 26 29503992, component := 64 },
    { zero := BitVec.ofNat 26 30028216, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover279 : ActiveCover := {
  active := BitVec.ofNat 14 11040
  strata := [
    { zero := BitVec.ofNat 26 21106923, component := 47 },
    { zero := BitVec.ofNat 26 21631147, component := 47 },
    { zero := BitVec.ofNat 26 21115086, component := 59 },
    { zero := BitVec.ofNat 26 21639310, component := 59 },
    { zero := BitVec.ofNat 26 21115114, component := 59 },
    { zero := BitVec.ofNat 26 21639338, component := 59 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover280 : ActiveCover := {
  active := BitVec.ofNat 14 11136
  strata := [
    { zero := BitVec.ofNat 26 21115167, component := 64 },
    { zero := BitVec.ofNat 26 21107003, component := 51 },
    { zero := BitVec.ofNat 26 29503773, component := 64 },
    { zero := BitVec.ofNat 26 29495609, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover281 : ActiveCover := {
  active := BitVec.ofNat 14 11137
  strata := [
    { zero := BitVec.ofNat 26 21115162, component := 64 },
    { zero := BitVec.ofNat 26 29503768, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover282 : ActiveCover := {
  active := BitVec.ofNat 14 11168
  strata := [
    { zero := BitVec.ofNat 26 21114895, component := 59 },
    { zero := BitVec.ofNat 26 21106731, component := 47 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover283 : ActiveCover := {
  active := BitVec.ofNat 14 11169
  strata := [
    { zero := BitVec.ofNat 26 21114890, component := 59 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover284 : ActiveCover := {
  active := BitVec.ofNat 14 11264
  strata := [
    { zero := BitVec.ofNat 26 26756013, component := 9 },
    { zero := BitVec.ofNat 26 27018029, component := 9 },
    { zero := BitVec.ofNat 26 27026189, component := 9 },
    { zero := BitVec.ofNat 26 30950313, component := 39 },
    { zero := BitVec.ofNat 26 31212329, component := 26 },
    { zero := BitVec.ofNat 26 26764172, component := 12 },
    { zero := BitVec.ofNat 26 30958504, component := 39 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover285 : ActiveCover := {
  active := BitVec.ofNat 14 11265
  strata := [
    { zero := BitVec.ofNat 26 31220488, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover286 : ActiveCover := {
  active := BitVec.ofNat 14 11266
  strata := [
    { zero := BitVec.ofNat 26 18367406, component := 39 },
    { zero := BitVec.ofNat 26 22561706, component := 39 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover287 : ActiveCover := {
  active := BitVec.ofNat 14 11274
  strata := [
    { zero := BitVec.ofNat 26 18367400, component := 39 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover288 : ActiveCover := {
  active := BitVec.ofNat 14 11328
  strata := [
    { zero := BitVec.ofNat 26 26231757, component := 9 },
    { zero := BitVec.ofNat 26 26493773, component := 9 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover289 : ActiveCover := {
  active := BitVec.ofNat 14 11330
  strata := [
    { zero := BitVec.ofNat 26 17843150, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover290 : ActiveCover := {
  active := BitVec.ofNat 14 11331
  strata := [
    { zero := BitVec.ofNat 26 22299466, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover291 : ActiveCover := {
  active := BitVec.ofNat 14 11339
  strata := [
    { zero := BitVec.ofNat 26 18105160, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover292 : ActiveCover := {
  active := BitVec.ofNat 14 11456
  strata := [
    { zero := BitVec.ofNat 26 26231565, component := 9 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover293 : ActiveCover := {
  active := BitVec.ofNat 14 11459
  strata := [
    { zero := BitVec.ofNat 26 22037258, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover294 : ActiveCover := {
  active := BitVec.ofNat 14 11467
  strata := [
    { zero := BitVec.ofNat 26 17842952, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover295 : ActiveCover := {
  active := BitVec.ofNat 14 11520
  strata := [
    { zero := BitVec.ofNat 26 31203597, component := 26 },
    { zero := BitVec.ofNat 26 31195433, component := 26 },
    { zero := BitVec.ofNat 26 31203724, component := 26 },
    { zero := BitVec.ofNat 26 31203752, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover296 : ActiveCover := {
  active := BitVec.ofNat 14 11521
  strata := [
    { zero := BitVec.ofNat 26 31203592, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover297 : ActiveCover := {
  active := BitVec.ofNat 14 11522
  strata := [
    { zero := BitVec.ofNat 26 22806954, component := 31 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover298 : ActiveCover := {
  active := BitVec.ofNat 14 11584
  strata := [
    { zero := BitVec.ofNat 26 30671181, component := 17 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover299 : ActiveCover := {
  active := BitVec.ofNat 14 11586
  strata := [
    { zero := BitVec.ofNat 26 22282702, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover300 : ActiveCover := {
  active := BitVec.ofNat 14 11587
  strata := [
    { zero := BitVec.ofNat 26 22282570, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover301 : ActiveCover := {
  active := BitVec.ofNat 14 12032
  strata := [
    { zero := BitVec.ofNat 26 29884857, component := 40 },
    { zero := BitVec.ofNat 26 29893020, component := 13 },
    { zero := BitVec.ofNat 26 29893048, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover302 : ActiveCover := {
  active := BitVec.ofNat 14 12034
  strata := [
    { zero := BitVec.ofNat 26 21496250, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover303 : ActiveCover := {
  active := BitVec.ofNat 14 12064
  strata := [
    { zero := BitVec.ofNat 26 29884587, component := 31 },
    { zero := BitVec.ofNat 26 29892750, component := 26 },
    { zero := BitVec.ofNat 26 29892778, component := 31 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover304 : ActiveCover := {
  active := BitVec.ofNat 14 12066
  strata := [
    { zero := BitVec.ofNat 26 21495978, component := 31 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover305 : ActiveCover := {
  active := BitVec.ofNat 14 12096
  strata := [
    { zero := BitVec.ofNat 26 29360605, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover306 : ActiveCover := {
  active := BitVec.ofNat 14 12098
  strata := [
    { zero := BitVec.ofNat 26 20971998, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover307 : ActiveCover := {
  active := BitVec.ofNat 14 12128
  strata := [
    { zero := BitVec.ofNat 26 29360335, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover308 : ActiveCover := {
  active := BitVec.ofNat 14 12130
  strata := [
    { zero := BitVec.ofNat 26 20971726, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover309 : ActiveCover := {
  active := BitVec.ofNat 14 12224
  strata := [
    { zero := BitVec.ofNat 26 29360413, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover310 : ActiveCover := {
  active := BitVec.ofNat 14 12227
  strata := [
    { zero := BitVec.ofNat 26 20971802, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover311 : ActiveCover := {
  active := BitVec.ofNat 14 12256
  strata := [
    { zero := BitVec.ofNat 26 29360143, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover312 : ActiveCover := {
  active := BitVec.ofNat 14 12259
  strata := [
    { zero := BitVec.ofNat 26 20971530, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover313 : ActiveCover := {
  active := BitVec.ofNat 14 12288
  strata := [
    { zero := BitVec.ofNat 26 1187839, component := 51 },
    { zero := BitVec.ofNat 26 11542271, component := 18 },
    { zero := BitVec.ofNat 26 3283711, component := 41 },
    { zero := BitVec.ofNat 26 1449855, component := 51 },
    { zero := BitVec.ofNat 26 11804287, component := 18 },
    { zero := BitVec.ofNat 26 3545727, component := 52 },
    { zero := BitVec.ofNat 26 1712063, component := 51 },
    { zero := BitVec.ofNat 26 12066495, component := 18 },
    { zero := BitVec.ofNat 26 3807935, component := 52 },
    { zero := BitVec.ofNat 26 1974079, component := 51 },
    { zero := BitVec.ofNat 26 12328511, component := 18 },
    { zero := BitVec.ofNat 26 4069951, component := 52 },
    { zero := BitVec.ofNat 26 1458015, component := 64 },
    { zero := BitVec.ofNat 26 11812447, component := 18 },
    { zero := BitVec.ofNat 26 3553887, component := 65 },
    { zero := BitVec.ofNat 26 1982239, component := 64 },
    { zero := BitVec.ofNat 26 12336671, component := 18 },
    { zero := BitVec.ofNat 26 4078111, component := 65 },
    { zero := BitVec.ofNat 26 9445373, component := 10 },
    { zero := BitVec.ofNat 26 11672573, component := 51 },
    { zero := BitVec.ofNat 26 9707389, component := 10 },
    { zero := BitVec.ofNat 26 11934589, component := 51 },
    { zero := BitVec.ofNat 26 9969597, component := 10 },
    { zero := BitVec.ofNat 26 12196797, component := 51 },
    { zero := BitVec.ofNat 26 10231613, component := 10 },
    { zero := BitVec.ofNat 26 12458813, component := 51 },
    { zero := BitVec.ofNat 26 9715549, component := 10 },
    { zero := BitVec.ofNat 26 11942749, component := 64 },
    { zero := BitVec.ofNat 26 10239773, component := 10 },
    { zero := BitVec.ofNat 26 12466973, component := 64 },
    { zero := BitVec.ofNat 26 1195998, component := 64 },
    { zero := BitVec.ofNat 26 11550430, component := 41 },
    { zero := BitVec.ofNat 26 3291870, component := 66 },
    { zero := BitVec.ofNat 26 1720222, component := 64 },
    { zero := BitVec.ofNat 26 12074654, component := 20 },
    { zero := BitVec.ofNat 26 3816094, component := 65 },
    { zero := BitVec.ofNat 26 9453532, component := 26 },
    { zero := BitVec.ofNat 26 11680732, component := 64 },
    { zero := BitVec.ofNat 26 9977756, component := 13 },
    { zero := BitVec.ofNat 26 12204956, component := 20 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover314 : ActiveCover := {
  active := BitVec.ofNat 14 12290
  strata := [
    { zero := BitVec.ofNat 26 1056766, component := 26 },
    { zero := BitVec.ofNat 26 3153662, component := 41 },
    { zero := BitVec.ofNat 26 1580990, component := 40 },
    { zero := BitVec.ofNat 26 3677886, component := 42 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover315 : ActiveCover := {
  active := BitVec.ofNat 14 12296
  strata := [
    { zero := BitVec.ofNat 26 1187833, component := 51 },
    { zero := BitVec.ofNat 26 3283961, component := 51 },
    { zero := BitVec.ofNat 26 1449849, component := 51 },
    { zero := BitVec.ofNat 26 3545977, component := 51 },
    { zero := BitVec.ofNat 26 1712057, component := 51 },
    { zero := BitVec.ofNat 26 3808185, component := 51 },
    { zero := BitVec.ofNat 26 1974073, component := 51 },
    { zero := BitVec.ofNat 26 4070201, component := 51 },
    { zero := BitVec.ofNat 26 1196024, component := 64 },
    { zero := BitVec.ofNat 26 3292152, component := 64 },
    { zero := BitVec.ofNat 26 1720248, component := 64 },
    { zero := BitVec.ofNat 26 3816376, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover316 : ActiveCover := {
  active := BitVec.ofNat 14 12297
  strata := [
    { zero := BitVec.ofNat 26 1458008, component := 64 },
    { zero := BitVec.ofNat 26 3554136, component := 64 },
    { zero := BitVec.ofNat 26 1982232, component := 64 },
    { zero := BitVec.ofNat 26 4078360, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover317 : ActiveCover := {
  active := BitVec.ofNat 14 12298
  strata := [
    { zero := BitVec.ofNat 26 1056760, component := 26 },
    { zero := BitVec.ofNat 26 1580984, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover318 : ActiveCover := {
  active := BitVec.ofNat 14 12304
  strata := [
    { zero := BitVec.ofNat 26 1187815, component := 26 },
    { zero := BitVec.ofNat 26 11542247, component := 18 },
    { zero := BitVec.ofNat 26 3283687, component := 41 },
    { zero := BitVec.ofNat 26 1449831, component := 49 },
    { zero := BitVec.ofNat 26 11804263, component := 18 },
    { zero := BitVec.ofNat 26 3545703, component := 52 },
    { zero := BitVec.ofNat 26 1457991, component := 62 },
    { zero := BitVec.ofNat 26 11812423, component := 18 },
    { zero := BitVec.ofNat 26 3553863, component := 65 },
    { zero := BitVec.ofNat 26 9445349, component := 26 },
    { zero := BitVec.ofNat 26 11672549, component := 18 },
    { zero := BitVec.ofNat 26 9707365, component := 17 },
    { zero := BitVec.ofNat 26 11934565, component := 18 },
    { zero := BitVec.ofNat 26 9715525, component := 17 },
    { zero := BitVec.ofNat 26 11942725, component := 18 },
    { zero := BitVec.ofNat 26 1195974, component := 61 },
    { zero := BitVec.ofNat 26 11550406, component := 41 },
    { zero := BitVec.ofNat 26 3291846, component := 66 },
    { zero := BitVec.ofNat 26 9453508, component := 26 },
    { zero := BitVec.ofNat 26 11680708, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover319 : ActiveCover := {
  active := BitVec.ofNat 14 12306
  strata := [
    { zero := BitVec.ofNat 26 1056742, component := 26 },
    { zero := BitVec.ofNat 26 3153638, component := 41 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover320 : ActiveCover := {
  active := BitVec.ofNat 14 12308
  strata := [
    { zero := BitVec.ofNat 26 12066469, component := 18 },
    { zero := BitVec.ofNat 26 12196517, component := 18 },
    { zero := BitVec.ofNat 26 12328485, component := 18 },
    { zero := BitVec.ofNat 26 12458533, component := 18 },
    { zero := BitVec.ofNat 26 12336645, component := 18 },
    { zero := BitVec.ofNat 26 12466693, component := 18 },
    { zero := BitVec.ofNat 26 12074628, component := 20 },
    { zero := BitVec.ofNat 26 12204676, component := 20 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover321 : ActiveCover := {
  active := BitVec.ofNat 14 12312
  strata := [
    { zero := BitVec.ofNat 26 1187809, component := 26 },
    { zero := BitVec.ofNat 26 3283937, component := 52 },
    { zero := BitVec.ofNat 26 1449825, component := 49 },
    { zero := BitVec.ofNat 26 3545953, component := 49 },
    { zero := BitVec.ofNat 26 1196000, component := 26 },
    { zero := BitVec.ofNat 26 3292128, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover322 : ActiveCover := {
  active := BitVec.ofNat 14 12313
  strata := [
    { zero := BitVec.ofNat 26 1457984, component := 62 },
    { zero := BitVec.ofNat 26 3554112, component := 62 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover323 : ActiveCover := {
  active := BitVec.ofNat 14 12314
  strata := [
    { zero := BitVec.ofNat 26 1056736, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover324 : ActiveCover := {
  active := BitVec.ofNat 14 12316
  strata := [
    { zero := BitVec.ofNat 26 3807905, component := 52 },
    { zero := BitVec.ofNat 26 4069921, component := 52 },
    { zero := BitVec.ofNat 26 3816096, component := 42 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover325 : ActiveCover := {
  active := BitVec.ofNat 14 12317
  strata := [
    { zero := BitVec.ofNat 26 4078080, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover326 : ActiveCover := {
  active := BitVec.ofNat 14 12318
  strata := [
    { zero := BitVec.ofNat 26 3677856, component := 42 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover327 : ActiveCover := {
  active := BitVec.ofNat 14 12416
  strata := [
    { zero := BitVec.ofNat 26 1187647, component := 51 },
    { zero := BitVec.ofNat 26 11542079, component := 18 },
    { zero := BitVec.ofNat 26 3283519, component := 52 },
    { zero := BitVec.ofNat 26 1195807, component := 64 },
    { zero := BitVec.ofNat 26 11550239, component := 18 },
    { zero := BitVec.ofNat 26 3291679, component := 65 },
    { zero := BitVec.ofNat 26 9445181, component := 10 },
    { zero := BitVec.ofNat 26 11672381, component := 51 },
    { zero := BitVec.ofNat 26 9453341, component := 10 },
    { zero := BitVec.ofNat 26 11680541, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover328 : ActiveCover := {
  active := BitVec.ofNat 14 12424
  strata := [
    { zero := BitVec.ofNat 26 1187641, component := 51 },
    { zero := BitVec.ofNat 26 3283769, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover329 : ActiveCover := {
  active := BitVec.ofNat 14 12425
  strata := [
    { zero := BitVec.ofNat 26 1195800, component := 64 },
    { zero := BitVec.ofNat 26 3291928, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover330 : ActiveCover := {
  active := BitVec.ofNat 14 12436
  strata := [
    { zero := BitVec.ofNat 26 11542053, component := 18 },
    { zero := BitVec.ofNat 26 11672101, component := 18 },
    { zero := BitVec.ofNat 26 11550213, component := 18 },
    { zero := BitVec.ofNat 26 11680261, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover331 : ActiveCover := {
  active := BitVec.ofNat 14 12444
  strata := [
    { zero := BitVec.ofNat 26 3283489, component := 52 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover332 : ActiveCover := {
  active := BitVec.ofNat 14 12445
  strata := [
    { zero := BitVec.ofNat 26 3291648, component := 65 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover333 : ActiveCover := {
  active := BitVec.ofNat 14 13312
  strata := [
    { zero := BitVec.ofNat 26 12061375, component := 18 },
    { zero := BitVec.ofNat 26 12323391, component := 18 },
    { zero := BitVec.ofNat 26 12331551, component := 18 },
    { zero := BitVec.ofNat 26 12061629, component := 18 },
    { zero := BitVec.ofNat 26 12323645, component := 18 },
    { zero := BitVec.ofNat 26 12331805, component := 18 },
    { zero := BitVec.ofNat 26 12069534, component := 20 },
    { zero := BitVec.ofNat 26 12069788, component := 20 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover334 : ActiveCover := {
  active := BitVec.ofNat 14 13314
  strata := [
    { zero := BitVec.ofNat 26 3672766, component := 42 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover335 : ActiveCover := {
  active := BitVec.ofNat 14 13322
  strata := [
    { zero := BitVec.ofNat 26 3673016, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover336 : ActiveCover := {
  active := BitVec.ofNat 14 13328
  strata := [
    { zero := BitVec.ofNat 26 12061415, component := 18 },
    { zero := BitVec.ofNat 26 12323431, component := 18 },
    { zero := BitVec.ofNat 26 12331591, component := 18 },
    { zero := BitVec.ofNat 26 12061669, component := 18 },
    { zero := BitVec.ofNat 26 12323685, component := 18 },
    { zero := BitVec.ofNat 26 12331845, component := 18 },
    { zero := BitVec.ofNat 26 12069574, component := 20 },
    { zero := BitVec.ofNat 26 12069828, component := 20 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover337 : ActiveCover := {
  active := BitVec.ofNat 14 13330
  strata := [
    { zero := BitVec.ofNat 26 3672806, component := 41 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover338 : ActiveCover := {
  active := BitVec.ofNat 14 13332
  strata := [
    { zero := BitVec.ofNat 26 12061349, component := 18 },
    { zero := BitVec.ofNat 26 12323365, component := 18 },
    { zero := BitVec.ofNat 26 12331525, component := 18 },
    { zero := BitVec.ofNat 26 12069508, component := 20 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover339 : ActiveCover := {
  active := BitVec.ofNat 14 13338
  strata := [
    { zero := BitVec.ofNat 26 3673056, component := 42 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover340 : ActiveCover := {
  active := BitVec.ofNat 14 13342
  strata := [
    { zero := BitVec.ofNat 26 3672736, component := 42 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover341 : ActiveCover := {
  active := BitVec.ofNat 14 13376
  strata := [
    { zero := BitVec.ofNat 26 11537119, component := 18 },
    { zero := BitVec.ofNat 26 11799135, component := 18 },
    { zero := BitVec.ofNat 26 11537373, component := 18 },
    { zero := BitVec.ofNat 26 11799389, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover342 : ActiveCover := {
  active := BitVec.ofNat 14 13378
  strata := [
    { zero := BitVec.ofNat 26 3148510, component := 41 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover343 : ActiveCover := {
  active := BitVec.ofNat 14 13387
  strata := [
    { zero := BitVec.ofNat 26 3410776, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover344 : ActiveCover := {
  active := BitVec.ofNat 14 13392
  strata := [
    { zero := BitVec.ofNat 26 11537095, component := 18 },
    { zero := BitVec.ofNat 26 11799111, component := 18 },
    { zero := BitVec.ofNat 26 11537349, component := 18 },
    { zero := BitVec.ofNat 26 11799365, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover345 : ActiveCover := {
  active := BitVec.ofNat 14 13394
  strata := [
    { zero := BitVec.ofNat 26 3148486, component := 41 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover346 : ActiveCover := {
  active := BitVec.ofNat 14 13403
  strata := [
    { zero := BitVec.ofNat 26 3410752, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover347 : ActiveCover := {
  active := BitVec.ofNat 14 13504
  strata := [
    { zero := BitVec.ofNat 26 11536927, component := 18 },
    { zero := BitVec.ofNat 26 11537181, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover348 : ActiveCover := {
  active := BitVec.ofNat 14 13515
  strata := [
    { zero := BitVec.ofNat 26 3148568, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover349 : ActiveCover := {
  active := BitVec.ofNat 14 13524
  strata := [
    { zero := BitVec.ofNat 26 11536901, component := 18 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover350 : ActiveCover := {
  active := BitVec.ofNat 14 13535
  strata := [
    { zero := BitVec.ofNat 26 3148288, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover351 : ActiveCover := {
  active := BitVec.ofNat 14 14592
  strata := [
    { zero := BitVec.ofNat 26 1446271, component := 51 },
    { zero := BitVec.ofNat 26 1970495, component := 51 },
    { zero := BitVec.ofNat 26 1454431, component := 64 },
    { zero := BitVec.ofNat 26 1978655, component := 64 },
    { zero := BitVec.ofNat 26 9834877, component := 51 },
    { zero := BitVec.ofNat 26 10359101, component := 51 },
    { zero := BitVec.ofNat 26 9843037, component := 64 },
    { zero := BitVec.ofNat 26 10367261, component := 64 },
    { zero := BitVec.ofNat 26 1454558, component := 64 },
    { zero := BitVec.ofNat 26 1978782, component := 64 },
    { zero := BitVec.ofNat 26 9843164, component := 64 },
    { zero := BitVec.ofNat 26 10367388, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover352 : ActiveCover := {
  active := BitVec.ofNat 14 14600
  strata := [
    { zero := BitVec.ofNat 26 1446265, component := 51 },
    { zero := BitVec.ofNat 26 1970489, component := 51 },
    { zero := BitVec.ofNat 26 1454584, component := 64 },
    { zero := BitVec.ofNat 26 1978808, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover353 : ActiveCover := {
  active := BitVec.ofNat 14 14601
  strata := [
    { zero := BitVec.ofNat 26 1454424, component := 64 },
    { zero := BitVec.ofNat 26 1978648, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover354 : ActiveCover := {
  active := BitVec.ofNat 14 14608
  strata := [
    { zero := BitVec.ofNat 26 1446247, component := 49 },
    { zero := BitVec.ofNat 26 1454407, component := 62 },
    { zero := BitVec.ofNat 26 9834853, component := 49 },
    { zero := BitVec.ofNat 26 9843013, component := 62 },
    { zero := BitVec.ofNat 26 1454534, component := 62 },
    { zero := BitVec.ofNat 26 9843140, component := 62 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover355 : ActiveCover := {
  active := BitVec.ofNat 14 14616
  strata := [
    { zero := BitVec.ofNat 26 1446241, component := 49 },
    { zero := BitVec.ofNat 26 1454560, component := 62 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover356 : ActiveCover := {
  active := BitVec.ofNat 14 14617
  strata := [
    { zero := BitVec.ofNat 26 1454400, component := 62 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover357 : ActiveCover := {
  active := BitVec.ofNat 14 15104
  strata := [
    { zero := BitVec.ofNat 26 135679, component := 51 },
    { zero := BitVec.ofNat 26 659903, component := 51 },
    { zero := BitVec.ofNat 26 8524285, component := 51 },
    { zero := BitVec.ofNat 26 9048509, component := 51 },
    { zero := BitVec.ofNat 26 143838, component := 64 },
    { zero := BitVec.ofNat 26 668062, component := 64 },
    { zero := BitVec.ofNat 26 8532444, component := 64 },
    { zero := BitVec.ofNat 26 9056668, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover358 : ActiveCover := {
  active := BitVec.ofNat 14 15112
  strata := [
    { zero := BitVec.ofNat 26 135673, component := 51 },
    { zero := BitVec.ofNat 26 659897, component := 51 },
    { zero := BitVec.ofNat 26 143864, component := 64 },
    { zero := BitVec.ofNat 26 668088, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover359 : ActiveCover := {
  active := BitVec.ofNat 14 15152
  strata := [
    { zero := BitVec.ofNat 26 135399, component := 26 },
    { zero := BitVec.ofNat 26 143558, component := 61 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover360 : ActiveCover := {
  active := BitVec.ofNat 14 15156
  strata := [
    { zero := BitVec.ofNat 26 9048229, component := 26 },
    { zero := BitVec.ofNat 26 9056388, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover361 : ActiveCover := {
  active := BitVec.ofNat 14 15164
  strata := [
    { zero := BitVec.ofNat 26 659617, component := 26 },
    { zero := BitVec.ofNat 26 667808, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover362 : ActiveCover := {
  active := BitVec.ofNat 14 15232
  strata := [
    { zero := BitVec.ofNat 26 135487, component := 51 },
    { zero := BitVec.ofNat 26 143647, component := 64 },
    { zero := BitVec.ofNat 26 8524093, component := 51 },
    { zero := BitVec.ofNat 26 8532253, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover363 : ActiveCover := {
  active := BitVec.ofNat 14 15240
  strata := [
    { zero := BitVec.ofNat 26 135481, component := 51 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover364 : ActiveCover := {
  active := BitVec.ofNat 14 15241
  strata := [
    { zero := BitVec.ofNat 26 143640, component := 64 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover365 : ActiveCover := {
  active := BitVec.ofNat 14 15284
  strata := [
    { zero := BitVec.ofNat 26 8523813, component := 26 },
    { zero := BitVec.ofNat 26 8531973, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover366 : ActiveCover := {
  active := BitVec.ofNat 14 15292
  strata := [
    { zero := BitVec.ofNat 26 135201, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover367 : ActiveCover := {
  active := BitVec.ofNat 14 15293
  strata := [
    { zero := BitVec.ofNat 26 143360, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover368 : ActiveCover := {
  active := BitVec.ofNat 14 15616
  strata := [
    { zero := BitVec.ofNat 26 10223933, component := 10 },
    { zero := BitVec.ofNat 26 10232093, component := 10 },
    { zero := BitVec.ofNat 26 10232220, component := 13 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover369 : ActiveCover := {
  active := BitVec.ofNat 14 15618
  strata := [
    { zero := BitVec.ofNat 26 1835454, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover370 : ActiveCover := {
  active := BitVec.ofNat 14 15626
  strata := [
    { zero := BitVec.ofNat 26 1835448, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover371 : ActiveCover := {
  active := BitVec.ofNat 14 15632
  strata := [
    { zero := BitVec.ofNat 26 10223973, component := 17 },
    { zero := BitVec.ofNat 26 10232133, component := 17 },
    { zero := BitVec.ofNat 26 10232260, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover372 : ActiveCover := {
  active := BitVec.ofNat 14 15634
  strata := [
    { zero := BitVec.ofNat 26 1835494, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover373 : ActiveCover := {
  active := BitVec.ofNat 14 15642
  strata := [
    { zero := BitVec.ofNat 26 1835488, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover374 : ActiveCover := {
  active := BitVec.ofNat 14 15680
  strata := [
    { zero := BitVec.ofNat 26 9699677, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover375 : ActiveCover := {
  active := BitVec.ofNat 14 15682
  strata := [
    { zero := BitVec.ofNat 26 1311198, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover376 : ActiveCover := {
  active := BitVec.ofNat 14 15691
  strata := [
    { zero := BitVec.ofNat 26 1311064, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover377 : ActiveCover := {
  active := BitVec.ofNat 14 15696
  strata := [
    { zero := BitVec.ofNat 26 9699653, component := 17 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover378 : ActiveCover := {
  active := BitVec.ofNat 14 15698
  strata := [
    { zero := BitVec.ofNat 26 1311174, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover379 : ActiveCover := {
  active := BitVec.ofNat 14 15707
  strata := [
    { zero := BitVec.ofNat 26 1311040, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover380 : ActiveCover := {
  active := BitVec.ofNat 14 16128
  strata := [
    { zero := BitVec.ofNat 26 8913341, component := 10 },
    { zero := BitVec.ofNat 26 8921500, component := 13 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover381 : ActiveCover := {
  active := BitVec.ofNat 14 16130
  strata := [
    { zero := BitVec.ofNat 26 524734, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover382 : ActiveCover := {
  active := BitVec.ofNat 14 16138
  strata := [
    { zero := BitVec.ofNat 26 524728, component := 40 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover383 : ActiveCover := {
  active := BitVec.ofNat 14 16176
  strata := [
    { zero := BitVec.ofNat 26 8913127, component := 26 },
    { zero := BitVec.ofNat 26 8921286, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover384 : ActiveCover := {
  active := BitVec.ofNat 14 16178
  strata := [
    { zero := BitVec.ofNat 26 524518, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover385 : ActiveCover := {
  active := BitVec.ofNat 14 16180
  strata := [
    { zero := BitVec.ofNat 26 8913061, component := 26 },
    { zero := BitVec.ofNat 26 8921220, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover386 : ActiveCover := {
  active := BitVec.ofNat 14 16190
  strata := [
    { zero := BitVec.ofNat 26 524448, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover387 : ActiveCover := {
  active := BitVec.ofNat 14 16192
  strata := [
    { zero := BitVec.ofNat 26 8389085, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover388 : ActiveCover := {
  active := BitVec.ofNat 14 16194
  strata := [
    { zero := BitVec.ofNat 26 478, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover389 : ActiveCover := {
  active := BitVec.ofNat 14 16240
  strata := [
    { zero := BitVec.ofNat 26 8388807, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover390 : ActiveCover := {
  active := BitVec.ofNat 14 16242
  strata := [
    { zero := BitVec.ofNat 26 198, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover391 : ActiveCover := {
  active := BitVec.ofNat 14 16320
  strata := [
    { zero := BitVec.ofNat 26 8388893, component := 10 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover392 : ActiveCover := {
  active := BitVec.ofNat 14 16331
  strata := [
    { zero := BitVec.ofNat 26 280, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover393 : ActiveCover := {
  active := BitVec.ofNat 14 16372
  strata := [
    { zero := BitVec.ofNat 26 8388613, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def cover394 : ActiveCover := {
  active := BitVec.ofNat 14 16383
  strata := [
    { zero := BitVec.ofNat 26 0, component := 26 }
  ]
}

set_option maxRecDepth 1000000 in
def covers : List ActiveCover := [
  cover0, cover1, cover2, cover3, cover4, cover5, cover6, cover7, cover8, cover9, cover10, cover11, cover12, cover13, cover14, cover15, cover16, cover17, cover18, cover19, cover20, cover21, cover22, cover23, cover24, cover25, cover26, cover27, cover28, cover29, cover30, cover31, cover32, cover33, cover34, cover35, cover36, cover37, cover38, cover39, cover40, cover41, cover42, cover43, cover44, cover45, cover46, cover47, cover48, cover49, cover50, cover51, cover52, cover53, cover54, cover55, cover56, cover57, cover58, cover59, cover60, cover61, cover62, cover63, cover64, cover65, cover66, cover67, cover68, cover69, cover70, cover71, cover72, cover73, cover74, cover75, cover76, cover77, cover78, cover79, cover80, cover81, cover82, cover83, cover84, cover85, cover86, cover87, cover88, cover89, cover90, cover91, cover92, cover93, cover94, cover95, cover96, cover97, cover98, cover99, cover100, cover101, cover102, cover103, cover104, cover105, cover106, cover107, cover108, cover109, cover110, cover111, cover112, cover113, cover114, cover115, cover116, cover117, cover118, cover119, cover120, cover121, cover122, cover123, cover124, cover125, cover126, cover127, cover128, cover129, cover130, cover131, cover132, cover133, cover134, cover135, cover136, cover137, cover138, cover139, cover140, cover141, cover142, cover143, cover144, cover145, cover146, cover147, cover148, cover149, cover150, cover151, cover152, cover153, cover154, cover155, cover156, cover157, cover158, cover159, cover160, cover161, cover162, cover163, cover164, cover165, cover166, cover167, cover168, cover169, cover170, cover171, cover172, cover173, cover174, cover175, cover176, cover177, cover178, cover179, cover180, cover181, cover182, cover183, cover184, cover185, cover186, cover187, cover188, cover189, cover190, cover191, cover192, cover193, cover194, cover195, cover196, cover197, cover198, cover199, cover200, cover201, cover202, cover203, cover204, cover205, cover206, cover207, cover208, cover209, cover210, cover211, cover212, cover213, cover214, cover215, cover216, cover217, cover218, cover219, cover220, cover221, cover222, cover223, cover224, cover225, cover226, cover227, cover228, cover229, cover230, cover231, cover232, cover233, cover234, cover235, cover236, cover237, cover238, cover239, cover240, cover241, cover242, cover243, cover244, cover245, cover246, cover247, cover248, cover249, cover250, cover251, cover252, cover253, cover254, cover255, cover256, cover257, cover258, cover259, cover260, cover261, cover262, cover263, cover264, cover265, cover266, cover267, cover268, cover269, cover270, cover271, cover272, cover273, cover274, cover275, cover276, cover277, cover278, cover279, cover280, cover281, cover282, cover283, cover284, cover285, cover286, cover287, cover288, cover289, cover290, cover291, cover292, cover293, cover294, cover295, cover296, cover297, cover298, cover299, cover300, cover301, cover302, cover303, cover304, cover305, cover306, cover307, cover308, cover309, cover310, cover311, cover312, cover313, cover314, cover315, cover316, cover317, cover318, cover319, cover320, cover321, cover322, cover323, cover324, cover325, cover326, cover327, cover328, cover329, cover330, cover331, cover332, cover333, cover334, cover335, cover336, cover337, cover338, cover339, cover340, cover341, cover342, cover343, cover344, cover345, cover346, cover347, cover348, cover349, cover350, cover351, cover352, cover353, cover354, cover355, cover356, cover357, cover358, cover359, cover360, cover361, cover362, cover363, cover364, cover365, cover366, cover367, cover368, cover369, cover370, cover371, cover372, cover373, cover374, cover375, cover376, cover377, cover378, cover379, cover380, cover381, cover382, cover383, cover384, cover385, cover386, cover387, cover388, cover389, cover390, cover391, cover392, cover393, cover394
]

def activeMatches (active : BitVec 14) (pattern : BitVec 26) : Bool :=
  (active.getLsbD 0 == relationActive pattern 0) &&
    (active.getLsbD 1 == relationActive pattern 1) &&
    (active.getLsbD 2 == relationActive pattern 2) &&
    (active.getLsbD 3 == relationActive pattern 3) &&
    (active.getLsbD 4 == relationActive pattern 4) &&
    (active.getLsbD 5 == relationActive pattern 5) &&
    (active.getLsbD 6 == relationActive pattern 6) &&
    (active.getLsbD 7 == relationActive pattern 7) &&
    (active.getLsbD 8 == relationActive pattern 8) &&
    (active.getLsbD 9 == relationActive pattern 9) &&
    (active.getLsbD 10 == relationActive pattern 10) &&
    (active.getLsbD 11 == relationActive pattern 11) &&
    (active.getLsbD 12 == relationActive pattern 12) &&
    (active.getLsbD 13 == relationActive pattern 13)

def stratumMatches (stratum : Stratum) (pattern : BitVec 26) : Bool :=
  (stratum.zero &&& pattern) == 0

def activeCoverMatches (cover : ActiveCover) (pattern : BitVec 26) : Bool :=
  activeMatches cover.active pattern &&
    cover.strata.any fun stratum => stratumMatches stratum pattern

def covered (pattern : BitVec 26) : Bool :=
  covers.any fun cover => activeCoverMatches cover pattern

def relationLeftActiveProp (pattern : Fin 26 → Prop) : Fin 14 → Prop
  | 0 => pattern 0 ∧ pattern 7
  | 1 => pattern 0 ∧ pattern 13
  | 2 => pattern 1 ∧ pattern 8
  | 3 => pattern 1 ∧ pattern 23
  | 4 => pattern 3 ∧ pattern 25
  | 5 => pattern 4 ∧ pattern 20
  | 6 => pattern 5 ∧ pattern 13
  | 7 => pattern 6 ∧ pattern 19
  | 8 => pattern 9 ∧ pattern 16
  | 9 => pattern 9 ∧ pattern 18
  | 10 => pattern 10 ∧ pattern 17
  | 11 => pattern 10 ∧ pattern 21
  | 12 => pattern 14 ∧ pattern 22
  | 13 => pattern 15 ∧ pattern 25

def relationRightActiveProp (pattern : Fin 26 → Prop) : Fin 14 → Prop
  | 0 => pattern 2 ∧ pattern 5
  | 1 => pattern 17 ∧ pattern 23
  | 2 => pattern 3 ∧ pattern 6
  | 3 => pattern 2 ∧ pattern 22
  | 4 => pattern 4 ∧ pattern 24
  | 5 => pattern 8 ∧ pattern 21
  | 6 => pattern 12 ∧ pattern 19
  | 7 => pattern 7 ∧ pattern 18
  | 8 => pattern 11 ∧ pattern 14
  | 9 => pattern 20
  | 10 => pattern 12 ∧ pattern 15
  | 11 => pattern 11
  | 12 => pattern 24
  | 13 => pattern 16

def feasibleProp (pattern : Fin 26 → Prop) : Prop :=
  (relationLeftActiveProp pattern 0 ↔ relationRightActiveProp pattern 0) ∧
    (relationLeftActiveProp pattern 1 ↔ relationRightActiveProp pattern 1) ∧
    (relationLeftActiveProp pattern 2 ↔ relationRightActiveProp pattern 2) ∧
    (relationLeftActiveProp pattern 3 ↔ relationRightActiveProp pattern 3) ∧
    (relationLeftActiveProp pattern 4 ↔ relationRightActiveProp pattern 4) ∧
    (relationLeftActiveProp pattern 5 ↔ relationRightActiveProp pattern 5) ∧
    (relationLeftActiveProp pattern 6 ↔ relationRightActiveProp pattern 6) ∧
    (relationLeftActiveProp pattern 7 ↔ relationRightActiveProp pattern 7) ∧
    (relationLeftActiveProp pattern 8 ↔ relationRightActiveProp pattern 8) ∧
    (relationLeftActiveProp pattern 9 ↔ relationRightActiveProp pattern 9) ∧
    (relationLeftActiveProp pattern 10 ↔ relationRightActiveProp pattern 10) ∧
    (relationLeftActiveProp pattern 11 ↔ relationRightActiveProp pattern 11) ∧
    (relationLeftActiveProp pattern 12 ↔ relationRightActiveProp pattern 12) ∧
    (relationLeftActiveProp pattern 13 ↔ relationRightActiveProp pattern 13)

def activeMatchesProp (active : BitVec 14) (pattern : Fin 26 → Prop) : Prop :=
  (active.getLsbD 0 = true ↔ relationLeftActiveProp pattern 0) ∧
    (active.getLsbD 1 = true ↔ relationLeftActiveProp pattern 1) ∧
    (active.getLsbD 2 = true ↔ relationLeftActiveProp pattern 2) ∧
    (active.getLsbD 3 = true ↔ relationLeftActiveProp pattern 3) ∧
    (active.getLsbD 4 = true ↔ relationLeftActiveProp pattern 4) ∧
    (active.getLsbD 5 = true ↔ relationLeftActiveProp pattern 5) ∧
    (active.getLsbD 6 = true ↔ relationLeftActiveProp pattern 6) ∧
    (active.getLsbD 7 = true ↔ relationLeftActiveProp pattern 7) ∧
    (active.getLsbD 8 = true ↔ relationLeftActiveProp pattern 8) ∧
    (active.getLsbD 9 = true ↔ relationLeftActiveProp pattern 9) ∧
    (active.getLsbD 10 = true ↔ relationLeftActiveProp pattern 10) ∧
    (active.getLsbD 11 = true ↔ relationLeftActiveProp pattern 11) ∧
    (active.getLsbD 12 = true ↔ relationLeftActiveProp pattern 12) ∧
    (active.getLsbD 13 = true ↔ relationLeftActiveProp pattern 13)

def zeroMatchesProp (zero : BitVec 26) (pattern : Fin 26 → Prop) : Prop :=
  (zero.getLsbD 0 = true → ¬ pattern 0) ∧
    (zero.getLsbD 1 = true → ¬ pattern 1) ∧
    (zero.getLsbD 2 = true → ¬ pattern 2) ∧
    (zero.getLsbD 3 = true → ¬ pattern 3) ∧
    (zero.getLsbD 4 = true → ¬ pattern 4) ∧
    (zero.getLsbD 5 = true → ¬ pattern 5) ∧
    (zero.getLsbD 6 = true → ¬ pattern 6) ∧
    (zero.getLsbD 7 = true → ¬ pattern 7) ∧
    (zero.getLsbD 8 = true → ¬ pattern 8) ∧
    (zero.getLsbD 9 = true → ¬ pattern 9) ∧
    (zero.getLsbD 10 = true → ¬ pattern 10) ∧
    (zero.getLsbD 11 = true → ¬ pattern 11) ∧
    (zero.getLsbD 12 = true → ¬ pattern 12) ∧
    (zero.getLsbD 13 = true → ¬ pattern 13) ∧
    (zero.getLsbD 14 = true → ¬ pattern 14) ∧
    (zero.getLsbD 15 = true → ¬ pattern 15) ∧
    (zero.getLsbD 16 = true → ¬ pattern 16) ∧
    (zero.getLsbD 17 = true → ¬ pattern 17) ∧
    (zero.getLsbD 18 = true → ¬ pattern 18) ∧
    (zero.getLsbD 19 = true → ¬ pattern 19) ∧
    (zero.getLsbD 20 = true → ¬ pattern 20) ∧
    (zero.getLsbD 21 = true → ¬ pattern 21) ∧
    (zero.getLsbD 22 = true → ¬ pattern 22) ∧
    (zero.getLsbD 23 = true → ¬ pattern 23) ∧
    (zero.getLsbD 24 = true → ¬ pattern 24) ∧
    (zero.getLsbD 25 = true → ¬ pattern 25)

def activeCoverMatchesProp (cover : ActiveCover) (pattern : Fin 26 → Prop) : Prop :=
  activeMatchesProp cover.active pattern ∧
    ∃ stratum ∈ cover.strata, zeroMatchesProp stratum.zero pattern

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover0ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover0.active pattern) :
    ∃ stratum ∈ cover0.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover0,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover0, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover1ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover1.active pattern) :
    ∃ stratum ∈ cover1.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover1,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover1, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover2ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover2.active pattern) :
    ∃ stratum ∈ cover2.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover2,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover2, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover3ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover3.active pattern) :
    ∃ stratum ∈ cover3.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover3,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover3, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover4ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover4.active pattern) :
    ∃ stratum ∈ cover4.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover4,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover4, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover5ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover5.active pattern) :
    ∃ stratum ∈ cover5.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover5,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover5, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover6ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover6.active pattern) :
    ∃ stratum ∈ cover6.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover6,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover6, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover7ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover7.active pattern) :
    ∃ stratum ∈ cover7.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover7,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover7, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover8ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover8.active pattern) :
    ∃ stratum ∈ cover8.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover8,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover8, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover9ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover9.active pattern) :
    ∃ stratum ∈ cover9.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover9,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover9, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover10ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover10.active pattern) :
    ∃ stratum ∈ cover10.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover10,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover10, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover11ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover11.active pattern) :
    ∃ stratum ∈ cover11.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover11,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover11, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover12ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover12.active pattern) :
    ∃ stratum ∈ cover12.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover12,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover12, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover13ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover13.active pattern) :
    ∃ stratum ∈ cover13.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover13,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover13, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover14ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover14.active pattern) :
    ∃ stratum ∈ cover14.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover14,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover14, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover15ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover15.active pattern) :
    ∃ stratum ∈ cover15.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover15,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover15, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover16ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover16.active pattern) :
    ∃ stratum ∈ cover16.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover16,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover16, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover17ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover17.active pattern) :
    ∃ stratum ∈ cover17.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover17,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover17, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover18ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover18.active pattern) :
    ∃ stratum ∈ cover18.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover18,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover18, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover19ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover19.active pattern) :
    ∃ stratum ∈ cover19.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover19,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover19, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover20ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover20.active pattern) :
    ∃ stratum ∈ cover20.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover20,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover20, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover21ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover21.active pattern) :
    ∃ stratum ∈ cover21.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover21,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover21, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover22ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover22.active pattern) :
    ∃ stratum ∈ cover22.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover22,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover22, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover23ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover23.active pattern) :
    ∃ stratum ∈ cover23.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover23,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover23, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover24ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover24.active pattern) :
    ∃ stratum ∈ cover24.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover24,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover24, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover25ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover25.active pattern) :
    ∃ stratum ∈ cover25.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover25,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover25, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover26ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover26.active pattern) :
    ∃ stratum ∈ cover26.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover26,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover26, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover27ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover27.active pattern) :
    ∃ stratum ∈ cover27.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover27,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover27, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover28ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover28.active pattern) :
    ∃ stratum ∈ cover28.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover28,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover28, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover29ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover29.active pattern) :
    ∃ stratum ∈ cover29.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover29,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover29, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover30ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover30.active pattern) :
    ∃ stratum ∈ cover30.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover30,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover30, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover31ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover31.active pattern) :
    ∃ stratum ∈ cover31.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover31,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover31, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover32ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover32.active pattern) :
    ∃ stratum ∈ cover32.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover32,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover32, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover33ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover33.active pattern) :
    ∃ stratum ∈ cover33.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover33,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover33, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover34ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover34.active pattern) :
    ∃ stratum ∈ cover34.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover34,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover34, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover35ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover35.active pattern) :
    ∃ stratum ∈ cover35.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover35,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover35, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover36ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover36.active pattern) :
    ∃ stratum ∈ cover36.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover36,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover36, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover37ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover37.active pattern) :
    ∃ stratum ∈ cover37.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover37,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover37, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover38ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover38.active pattern) :
    ∃ stratum ∈ cover38.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover38,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover38, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover39ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover39.active pattern) :
    ∃ stratum ∈ cover39.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover39,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover39, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover40ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover40.active pattern) :
    ∃ stratum ∈ cover40.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover40,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover40, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover41ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover41.active pattern) :
    ∃ stratum ∈ cover41.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover41,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover41, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover42ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover42.active pattern) :
    ∃ stratum ∈ cover42.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover42,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover42, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover43ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover43.active pattern) :
    ∃ stratum ∈ cover43.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover43,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover43, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover44ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover44.active pattern) :
    ∃ stratum ∈ cover44.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover44,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover44, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover45ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover45.active pattern) :
    ∃ stratum ∈ cover45.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover45,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover45, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover46ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover46.active pattern) :
    ∃ stratum ∈ cover46.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover46,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover46, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover47ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover47.active pattern) :
    ∃ stratum ∈ cover47.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover47,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover47, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover48ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover48.active pattern) :
    ∃ stratum ∈ cover48.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover48,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover48, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover49ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover49.active pattern) :
    ∃ stratum ∈ cover49.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover49,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover49, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover50ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover50.active pattern) :
    ∃ stratum ∈ cover50.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover50,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover50, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover51ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover51.active pattern) :
    ∃ stratum ∈ cover51.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover51,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover51, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover52ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover52.active pattern) :
    ∃ stratum ∈ cover52.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover52,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover52, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover53ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover53.active pattern) :
    ∃ stratum ∈ cover53.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover53,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover53, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover54ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover54.active pattern) :
    ∃ stratum ∈ cover54.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover54,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover54, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover55ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover55.active pattern) :
    ∃ stratum ∈ cover55.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover55,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover55, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover56ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover56.active pattern) :
    ∃ stratum ∈ cover56.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover56,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover56, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover57ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover57.active pattern) :
    ∃ stratum ∈ cover57.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover57,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover57, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover58ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover58.active pattern) :
    ∃ stratum ∈ cover58.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover58,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover58, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover59ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover59.active pattern) :
    ∃ stratum ∈ cover59.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover59,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover59, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover60ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover60.active pattern) :
    ∃ stratum ∈ cover60.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover60,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover60, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover61ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover61.active pattern) :
    ∃ stratum ∈ cover61.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover61,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover61, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover62ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover62.active pattern) :
    ∃ stratum ∈ cover62.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover62,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover62, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover63ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover63.active pattern) :
    ∃ stratum ∈ cover63.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover63,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover63, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover64ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover64.active pattern) :
    ∃ stratum ∈ cover64.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover64,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover64, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover65ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover65.active pattern) :
    ∃ stratum ∈ cover65.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover65,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover65, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover66ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover66.active pattern) :
    ∃ stratum ∈ cover66.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover66,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover66, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover67ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover67.active pattern) :
    ∃ stratum ∈ cover67.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover67,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover67, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover68ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover68.active pattern) :
    ∃ stratum ∈ cover68.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover68,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover68, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover69ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover69.active pattern) :
    ∃ stratum ∈ cover69.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover69,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover69, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover70ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover70.active pattern) :
    ∃ stratum ∈ cover70.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover70,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover70, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover71ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover71.active pattern) :
    ∃ stratum ∈ cover71.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover71,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover71, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover72ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover72.active pattern) :
    ∃ stratum ∈ cover72.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover72,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover72, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover73ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover73.active pattern) :
    ∃ stratum ∈ cover73.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover73,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover73, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover74ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover74.active pattern) :
    ∃ stratum ∈ cover74.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover74,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover74, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover75ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover75.active pattern) :
    ∃ stratum ∈ cover75.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover75,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover75, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover76ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover76.active pattern) :
    ∃ stratum ∈ cover76.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover76,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover76, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover77ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover77.active pattern) :
    ∃ stratum ∈ cover77.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover77,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover77, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover78ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover78.active pattern) :
    ∃ stratum ∈ cover78.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover78,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover78, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover79ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover79.active pattern) :
    ∃ stratum ∈ cover79.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover79,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover79, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover80ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover80.active pattern) :
    ∃ stratum ∈ cover80.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover80,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover80, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover81ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover81.active pattern) :
    ∃ stratum ∈ cover81.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover81,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover81, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover82ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover82.active pattern) :
    ∃ stratum ∈ cover82.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover82,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover82, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover83ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover83.active pattern) :
    ∃ stratum ∈ cover83.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover83,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover83, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover84ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover84.active pattern) :
    ∃ stratum ∈ cover84.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover84,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover84, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover85ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover85.active pattern) :
    ∃ stratum ∈ cover85.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover85,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover85, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover86ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover86.active pattern) :
    ∃ stratum ∈ cover86.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover86,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover86, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover87ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover87.active pattern) :
    ∃ stratum ∈ cover87.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover87,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover87, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover88ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover88.active pattern) :
    ∃ stratum ∈ cover88.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover88,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover88, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover89ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover89.active pattern) :
    ∃ stratum ∈ cover89.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover89,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover89, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover90ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover90.active pattern) :
    ∃ stratum ∈ cover90.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover90,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover90, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover91ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover91.active pattern) :
    ∃ stratum ∈ cover91.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover91,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover91, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover92ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover92.active pattern) :
    ∃ stratum ∈ cover92.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover92,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover92, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover93ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover93.active pattern) :
    ∃ stratum ∈ cover93.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover93,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover93, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover94ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover94.active pattern) :
    ∃ stratum ∈ cover94.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover94,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover94, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover95ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover95.active pattern) :
    ∃ stratum ∈ cover95.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover95,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover95, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover96ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover96.active pattern) :
    ∃ stratum ∈ cover96.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover96,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover96, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover97ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover97.active pattern) :
    ∃ stratum ∈ cover97.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover97,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover97, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover98ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover98.active pattern) :
    ∃ stratum ∈ cover98.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover98,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover98, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover99ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover99.active pattern) :
    ∃ stratum ∈ cover99.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover99,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover99, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover100ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover100.active pattern) :
    ∃ stratum ∈ cover100.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover100,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover100, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover101ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover101.active pattern) :
    ∃ stratum ∈ cover101.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover101,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover101, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover102ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover102.active pattern) :
    ∃ stratum ∈ cover102.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover102,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover102, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover103ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover103.active pattern) :
    ∃ stratum ∈ cover103.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover103,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover103, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover104ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover104.active pattern) :
    ∃ stratum ∈ cover104.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover104,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover104, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover105ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover105.active pattern) :
    ∃ stratum ∈ cover105.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover105,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover105, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover106ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover106.active pattern) :
    ∃ stratum ∈ cover106.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover106,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover106, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover107ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover107.active pattern) :
    ∃ stratum ∈ cover107.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover107,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover107, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover108ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover108.active pattern) :
    ∃ stratum ∈ cover108.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover108,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover108, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover109ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover109.active pattern) :
    ∃ stratum ∈ cover109.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover109,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover109, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover110ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover110.active pattern) :
    ∃ stratum ∈ cover110.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover110,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover110, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover111ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover111.active pattern) :
    ∃ stratum ∈ cover111.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover111,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover111, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover112ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover112.active pattern) :
    ∃ stratum ∈ cover112.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover112,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover112, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover113ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover113.active pattern) :
    ∃ stratum ∈ cover113.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover113,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover113, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover114ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover114.active pattern) :
    ∃ stratum ∈ cover114.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover114,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover114, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover115ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover115.active pattern) :
    ∃ stratum ∈ cover115.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover115,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover115, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover116ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover116.active pattern) :
    ∃ stratum ∈ cover116.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover116,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover116, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover117ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover117.active pattern) :
    ∃ stratum ∈ cover117.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover117,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover117, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover118ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover118.active pattern) :
    ∃ stratum ∈ cover118.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover118,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover118, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover119ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover119.active pattern) :
    ∃ stratum ∈ cover119.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover119,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover119, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover120ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover120.active pattern) :
    ∃ stratum ∈ cover120.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover120,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover120, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover121ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover121.active pattern) :
    ∃ stratum ∈ cover121.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover121,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover121, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover122ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover122.active pattern) :
    ∃ stratum ∈ cover122.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover122,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover122, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover123ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover123.active pattern) :
    ∃ stratum ∈ cover123.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover123,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover123, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover124ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover124.active pattern) :
    ∃ stratum ∈ cover124.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover124,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover124, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover125ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover125.active pattern) :
    ∃ stratum ∈ cover125.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover125,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover125, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover126ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover126.active pattern) :
    ∃ stratum ∈ cover126.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover126,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover126, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover127ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover127.active pattern) :
    ∃ stratum ∈ cover127.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover127,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover127, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover128ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover128.active pattern) :
    ∃ stratum ∈ cover128.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover128,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover128, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover129ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover129.active pattern) :
    ∃ stratum ∈ cover129.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover129,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover129, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover130ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover130.active pattern) :
    ∃ stratum ∈ cover130.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover130,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover130, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover131ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover131.active pattern) :
    ∃ stratum ∈ cover131.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover131,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover131, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover132ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover132.active pattern) :
    ∃ stratum ∈ cover132.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover132,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover132, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover133ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover133.active pattern) :
    ∃ stratum ∈ cover133.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover133,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover133, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover134ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover134.active pattern) :
    ∃ stratum ∈ cover134.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover134,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover134, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover135ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover135.active pattern) :
    ∃ stratum ∈ cover135.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover135,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover135, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover136ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover136.active pattern) :
    ∃ stratum ∈ cover136.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover136,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover136, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover137ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover137.active pattern) :
    ∃ stratum ∈ cover137.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover137,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover137, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover138ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover138.active pattern) :
    ∃ stratum ∈ cover138.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover138,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover138, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover139ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover139.active pattern) :
    ∃ stratum ∈ cover139.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover139,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover139, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover140ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover140.active pattern) :
    ∃ stratum ∈ cover140.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover140,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover140, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover141ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover141.active pattern) :
    ∃ stratum ∈ cover141.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover141,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover141, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover142ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover142.active pattern) :
    ∃ stratum ∈ cover142.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover142,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover142, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover143ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover143.active pattern) :
    ∃ stratum ∈ cover143.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover143,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover143, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover144ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover144.active pattern) :
    ∃ stratum ∈ cover144.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover144,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover144, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover145ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover145.active pattern) :
    ∃ stratum ∈ cover145.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover145,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover145, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover146ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover146.active pattern) :
    ∃ stratum ∈ cover146.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover146,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover146, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover147ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover147.active pattern) :
    ∃ stratum ∈ cover147.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover147,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover147, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover148ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover148.active pattern) :
    ∃ stratum ∈ cover148.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover148,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover148, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover149ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover149.active pattern) :
    ∃ stratum ∈ cover149.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover149,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover149, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover150ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover150.active pattern) :
    ∃ stratum ∈ cover150.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover150,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover150, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover151ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover151.active pattern) :
    ∃ stratum ∈ cover151.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover151,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover151, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover152ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover152.active pattern) :
    ∃ stratum ∈ cover152.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover152,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover152, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover153ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover153.active pattern) :
    ∃ stratum ∈ cover153.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover153,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover153, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover154ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover154.active pattern) :
    ∃ stratum ∈ cover154.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover154,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover154, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover155ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover155.active pattern) :
    ∃ stratum ∈ cover155.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover155,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover155, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover156ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover156.active pattern) :
    ∃ stratum ∈ cover156.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover156,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover156, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover157ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover157.active pattern) :
    ∃ stratum ∈ cover157.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover157,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover157, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover158ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover158.active pattern) :
    ∃ stratum ∈ cover158.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover158,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover158, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover159ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover159.active pattern) :
    ∃ stratum ∈ cover159.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover159,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover159, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover160ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover160.active pattern) :
    ∃ stratum ∈ cover160.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover160,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover160, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover161ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover161.active pattern) :
    ∃ stratum ∈ cover161.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover161,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover161, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover162ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover162.active pattern) :
    ∃ stratum ∈ cover162.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover162,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover162, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover163ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover163.active pattern) :
    ∃ stratum ∈ cover163.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover163,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover163, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover164ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover164.active pattern) :
    ∃ stratum ∈ cover164.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover164,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover164, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover165ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover165.active pattern) :
    ∃ stratum ∈ cover165.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover165,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover165, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover166ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover166.active pattern) :
    ∃ stratum ∈ cover166.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover166,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover166, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover167ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover167.active pattern) :
    ∃ stratum ∈ cover167.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover167,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover167, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover168ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover168.active pattern) :
    ∃ stratum ∈ cover168.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover168,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover168, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover169ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover169.active pattern) :
    ∃ stratum ∈ cover169.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover169,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover169, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover170ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover170.active pattern) :
    ∃ stratum ∈ cover170.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover170,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover170, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover171ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover171.active pattern) :
    ∃ stratum ∈ cover171.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover171,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover171, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover172ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover172.active pattern) :
    ∃ stratum ∈ cover172.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover172,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover172, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover173ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover173.active pattern) :
    ∃ stratum ∈ cover173.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover173,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover173, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover174ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover174.active pattern) :
    ∃ stratum ∈ cover174.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover174,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover174, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover175ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover175.active pattern) :
    ∃ stratum ∈ cover175.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover175,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover175, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover176ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover176.active pattern) :
    ∃ stratum ∈ cover176.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover176,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover176, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover177ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover177.active pattern) :
    ∃ stratum ∈ cover177.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover177,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover177, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover178ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover178.active pattern) :
    ∃ stratum ∈ cover178.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover178,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover178, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover179ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover179.active pattern) :
    ∃ stratum ∈ cover179.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover179,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover179, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover180ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover180.active pattern) :
    ∃ stratum ∈ cover180.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover180,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover180, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover181ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover181.active pattern) :
    ∃ stratum ∈ cover181.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover181,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover181, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover182ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover182.active pattern) :
    ∃ stratum ∈ cover182.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover182,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover182, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover183ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover183.active pattern) :
    ∃ stratum ∈ cover183.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover183,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover183, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover184ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover184.active pattern) :
    ∃ stratum ∈ cover184.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover184,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover184, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover185ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover185.active pattern) :
    ∃ stratum ∈ cover185.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover185,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover185, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover186ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover186.active pattern) :
    ∃ stratum ∈ cover186.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover186,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover186, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover187ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover187.active pattern) :
    ∃ stratum ∈ cover187.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover187,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover187, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover188ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover188.active pattern) :
    ∃ stratum ∈ cover188.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover188,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover188, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover189ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover189.active pattern) :
    ∃ stratum ∈ cover189.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover189,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover189, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover190ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover190.active pattern) :
    ∃ stratum ∈ cover190.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover190,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover190, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover191ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover191.active pattern) :
    ∃ stratum ∈ cover191.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover191,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover191, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover192ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover192.active pattern) :
    ∃ stratum ∈ cover192.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover192,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover192, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover193ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover193.active pattern) :
    ∃ stratum ∈ cover193.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover193,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover193, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover194ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover194.active pattern) :
    ∃ stratum ∈ cover194.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover194,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover194, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover195ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover195.active pattern) :
    ∃ stratum ∈ cover195.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover195,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover195, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover196ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover196.active pattern) :
    ∃ stratum ∈ cover196.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover196,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover196, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover197ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover197.active pattern) :
    ∃ stratum ∈ cover197.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover197,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover197, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover198ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover198.active pattern) :
    ∃ stratum ∈ cover198.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover198,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover198, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover199ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover199.active pattern) :
    ∃ stratum ∈ cover199.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover199,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover199, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover200ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover200.active pattern) :
    ∃ stratum ∈ cover200.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover200,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover200, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover201ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover201.active pattern) :
    ∃ stratum ∈ cover201.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover201,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover201, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover202ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover202.active pattern) :
    ∃ stratum ∈ cover202.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover202,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover202, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover203ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover203.active pattern) :
    ∃ stratum ∈ cover203.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover203,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover203, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover204ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover204.active pattern) :
    ∃ stratum ∈ cover204.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover204,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover204, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover205ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover205.active pattern) :
    ∃ stratum ∈ cover205.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover205,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover205, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover206ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover206.active pattern) :
    ∃ stratum ∈ cover206.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover206,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover206, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover207ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover207.active pattern) :
    ∃ stratum ∈ cover207.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover207,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover207, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover208ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover208.active pattern) :
    ∃ stratum ∈ cover208.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover208,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover208, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover209ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover209.active pattern) :
    ∃ stratum ∈ cover209.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover209,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover209, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover210ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover210.active pattern) :
    ∃ stratum ∈ cover210.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover210,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover210, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover211ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover211.active pattern) :
    ∃ stratum ∈ cover211.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover211,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover211, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover212ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover212.active pattern) :
    ∃ stratum ∈ cover212.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover212,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover212, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover213ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover213.active pattern) :
    ∃ stratum ∈ cover213.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover213,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover213, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover214ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover214.active pattern) :
    ∃ stratum ∈ cover214.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover214,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover214, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover215ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover215.active pattern) :
    ∃ stratum ∈ cover215.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover215,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover215, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover216ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover216.active pattern) :
    ∃ stratum ∈ cover216.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover216,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover216, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover217ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover217.active pattern) :
    ∃ stratum ∈ cover217.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover217,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover217, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover218ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover218.active pattern) :
    ∃ stratum ∈ cover218.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover218,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover218, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover219ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover219.active pattern) :
    ∃ stratum ∈ cover219.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover219,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover219, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover220ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover220.active pattern) :
    ∃ stratum ∈ cover220.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover220,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover220, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover221ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover221.active pattern) :
    ∃ stratum ∈ cover221.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover221,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover221, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover222ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover222.active pattern) :
    ∃ stratum ∈ cover222.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover222,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover222, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover223ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover223.active pattern) :
    ∃ stratum ∈ cover223.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover223,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover223, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover224ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover224.active pattern) :
    ∃ stratum ∈ cover224.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover224,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover224, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover225ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover225.active pattern) :
    ∃ stratum ∈ cover225.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover225,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover225, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover226ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover226.active pattern) :
    ∃ stratum ∈ cover226.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover226,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover226, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover227ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover227.active pattern) :
    ∃ stratum ∈ cover227.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover227,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover227, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover228ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover228.active pattern) :
    ∃ stratum ∈ cover228.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover228,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover228, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover229ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover229.active pattern) :
    ∃ stratum ∈ cover229.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover229,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover229, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover230ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover230.active pattern) :
    ∃ stratum ∈ cover230.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover230,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover230, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover231ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover231.active pattern) :
    ∃ stratum ∈ cover231.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover231,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover231, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover232ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover232.active pattern) :
    ∃ stratum ∈ cover232.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover232,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover232, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover233ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover233.active pattern) :
    ∃ stratum ∈ cover233.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover233,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover233, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover234ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover234.active pattern) :
    ∃ stratum ∈ cover234.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover234,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover234, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover235ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover235.active pattern) :
    ∃ stratum ∈ cover235.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover235,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover235, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover236ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover236.active pattern) :
    ∃ stratum ∈ cover236.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover236,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover236, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover237ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover237.active pattern) :
    ∃ stratum ∈ cover237.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover237,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover237, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover238ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover238.active pattern) :
    ∃ stratum ∈ cover238.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover238,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover238, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover239ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover239.active pattern) :
    ∃ stratum ∈ cover239.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover239,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover239, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover240ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover240.active pattern) :
    ∃ stratum ∈ cover240.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover240,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover240, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover241ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover241.active pattern) :
    ∃ stratum ∈ cover241.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover241,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover241, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover242ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover242.active pattern) :
    ∃ stratum ∈ cover242.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover242,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover242, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover243ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover243.active pattern) :
    ∃ stratum ∈ cover243.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover243,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover243, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover244ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover244.active pattern) :
    ∃ stratum ∈ cover244.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover244,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover244, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover245ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover245.active pattern) :
    ∃ stratum ∈ cover245.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover245,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover245, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover246ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover246.active pattern) :
    ∃ stratum ∈ cover246.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover246,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover246, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover247ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover247.active pattern) :
    ∃ stratum ∈ cover247.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover247,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover247, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover248ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover248.active pattern) :
    ∃ stratum ∈ cover248.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover248,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover248, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover249ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover249.active pattern) :
    ∃ stratum ∈ cover249.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover249,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover249, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover250ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover250.active pattern) :
    ∃ stratum ∈ cover250.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover250,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover250, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover251ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover251.active pattern) :
    ∃ stratum ∈ cover251.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover251,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover251, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover252ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover252.active pattern) :
    ∃ stratum ∈ cover252.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover252,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover252, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover253ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover253.active pattern) :
    ∃ stratum ∈ cover253.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover253,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover253, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover254ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover254.active pattern) :
    ∃ stratum ∈ cover254.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover254,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover254, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover255ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover255.active pattern) :
    ∃ stratum ∈ cover255.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover255,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover255, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover256ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover256.active pattern) :
    ∃ stratum ∈ cover256.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover256,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover256, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover257ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover257.active pattern) :
    ∃ stratum ∈ cover257.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover257,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover257, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover258ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover258.active pattern) :
    ∃ stratum ∈ cover258.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover258,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover258, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover259ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover259.active pattern) :
    ∃ stratum ∈ cover259.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover259,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover259, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover260ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover260.active pattern) :
    ∃ stratum ∈ cover260.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover260,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover260, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover261ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover261.active pattern) :
    ∃ stratum ∈ cover261.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover261,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover261, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover262ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover262.active pattern) :
    ∃ stratum ∈ cover262.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover262,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover262, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover263ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover263.active pattern) :
    ∃ stratum ∈ cover263.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover263,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover263, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover264ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover264.active pattern) :
    ∃ stratum ∈ cover264.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover264,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover264, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover265ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover265.active pattern) :
    ∃ stratum ∈ cover265.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover265,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover265, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover266ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover266.active pattern) :
    ∃ stratum ∈ cover266.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover266,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover266, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover267ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover267.active pattern) :
    ∃ stratum ∈ cover267.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover267,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover267, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover268ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover268.active pattern) :
    ∃ stratum ∈ cover268.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover268,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover268, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover269ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover269.active pattern) :
    ∃ stratum ∈ cover269.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover269,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover269, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover270ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover270.active pattern) :
    ∃ stratum ∈ cover270.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover270,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover270, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover271ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover271.active pattern) :
    ∃ stratum ∈ cover271.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover271,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover271, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover272ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover272.active pattern) :
    ∃ stratum ∈ cover272.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover272,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover272, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover273ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover273.active pattern) :
    ∃ stratum ∈ cover273.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover273,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover273, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover274ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover274.active pattern) :
    ∃ stratum ∈ cover274.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover274,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover274, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover275ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover275.active pattern) :
    ∃ stratum ∈ cover275.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover275,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover275, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover276ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover276.active pattern) :
    ∃ stratum ∈ cover276.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover276,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover276, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover277ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover277.active pattern) :
    ∃ stratum ∈ cover277.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover277,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover277, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover278ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover278.active pattern) :
    ∃ stratum ∈ cover278.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover278,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover278, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover279ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover279.active pattern) :
    ∃ stratum ∈ cover279.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover279,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover279, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover280ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover280.active pattern) :
    ∃ stratum ∈ cover280.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover280,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover280, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover281ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover281.active pattern) :
    ∃ stratum ∈ cover281.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover281,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover281, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover282ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover282.active pattern) :
    ∃ stratum ∈ cover282.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover282,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover282, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover283ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover283.active pattern) :
    ∃ stratum ∈ cover283.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover283,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover283, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover284ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover284.active pattern) :
    ∃ stratum ∈ cover284.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover284,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover284, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover285ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover285.active pattern) :
    ∃ stratum ∈ cover285.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover285,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover285, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover286ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover286.active pattern) :
    ∃ stratum ∈ cover286.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover286,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover286, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover287ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover287.active pattern) :
    ∃ stratum ∈ cover287.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover287,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover287, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover288ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover288.active pattern) :
    ∃ stratum ∈ cover288.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover288,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover288, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover289ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover289.active pattern) :
    ∃ stratum ∈ cover289.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover289,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover289, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover290ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover290.active pattern) :
    ∃ stratum ∈ cover290.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover290,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover290, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover291ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover291.active pattern) :
    ∃ stratum ∈ cover291.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover291,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover291, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover292ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover292.active pattern) :
    ∃ stratum ∈ cover292.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover292,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover292, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover293ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover293.active pattern) :
    ∃ stratum ∈ cover293.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover293,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover293, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover294ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover294.active pattern) :
    ∃ stratum ∈ cover294.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover294,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover294, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover295ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover295.active pattern) :
    ∃ stratum ∈ cover295.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover295,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover295, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover296ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover296.active pattern) :
    ∃ stratum ∈ cover296.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover296,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover296, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover297ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover297.active pattern) :
    ∃ stratum ∈ cover297.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover297,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover297, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover298ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover298.active pattern) :
    ∃ stratum ∈ cover298.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover298,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover298, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover299ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover299.active pattern) :
    ∃ stratum ∈ cover299.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover299,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover299, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover300ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover300.active pattern) :
    ∃ stratum ∈ cover300.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover300,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover300, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover301ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover301.active pattern) :
    ∃ stratum ∈ cover301.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover301,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover301, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover302ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover302.active pattern) :
    ∃ stratum ∈ cover302.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover302,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover302, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover303ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover303.active pattern) :
    ∃ stratum ∈ cover303.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover303,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover303, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover304ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover304.active pattern) :
    ∃ stratum ∈ cover304.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover304,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover304, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover305ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover305.active pattern) :
    ∃ stratum ∈ cover305.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover305,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover305, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover306ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover306.active pattern) :
    ∃ stratum ∈ cover306.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover306,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover306, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover307ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover307.active pattern) :
    ∃ stratum ∈ cover307.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover307,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover307, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover308ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover308.active pattern) :
    ∃ stratum ∈ cover308.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover308,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover308, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover309ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover309.active pattern) :
    ∃ stratum ∈ cover309.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover309,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover309, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover310ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover310.active pattern) :
    ∃ stratum ∈ cover310.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover310,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover310, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover311ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover311.active pattern) :
    ∃ stratum ∈ cover311.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover311,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover311, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover312ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover312.active pattern) :
    ∃ stratum ∈ cover312.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover312,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover312, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover313ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover313.active pattern) :
    ∃ stratum ∈ cover313.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover313,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover313, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover314ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover314.active pattern) :
    ∃ stratum ∈ cover314.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover314,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover314, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover315ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover315.active pattern) :
    ∃ stratum ∈ cover315.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover315,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover315, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover316ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover316.active pattern) :
    ∃ stratum ∈ cover316.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover316,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover316, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover317ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover317.active pattern) :
    ∃ stratum ∈ cover317.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover317,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover317, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover318ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover318.active pattern) :
    ∃ stratum ∈ cover318.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover318,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover318, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover319ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover319.active pattern) :
    ∃ stratum ∈ cover319.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover319,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover319, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover320ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover320.active pattern) :
    ∃ stratum ∈ cover320.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover320,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover320, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover321ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover321.active pattern) :
    ∃ stratum ∈ cover321.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover321,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover321, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover322ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover322.active pattern) :
    ∃ stratum ∈ cover322.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover322,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover322, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover323ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover323.active pattern) :
    ∃ stratum ∈ cover323.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover323,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover323, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover324ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover324.active pattern) :
    ∃ stratum ∈ cover324.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover324,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover324, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover325ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover325.active pattern) :
    ∃ stratum ∈ cover325.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover325,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover325, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover326ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover326.active pattern) :
    ∃ stratum ∈ cover326.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover326,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover326, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover327ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover327.active pattern) :
    ∃ stratum ∈ cover327.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover327,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover327, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover328ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover328.active pattern) :
    ∃ stratum ∈ cover328.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover328,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover328, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover329ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover329.active pattern) :
    ∃ stratum ∈ cover329.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover329,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover329, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover330ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover330.active pattern) :
    ∃ stratum ∈ cover330.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover330,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover330, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover331ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover331.active pattern) :
    ∃ stratum ∈ cover331.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover331,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover331, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover332ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover332.active pattern) :
    ∃ stratum ∈ cover332.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover332,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover332, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover333ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover333.active pattern) :
    ∃ stratum ∈ cover333.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover333,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover333, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover334ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover334.active pattern) :
    ∃ stratum ∈ cover334.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover334,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover334, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover335ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover335.active pattern) :
    ∃ stratum ∈ cover335.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover335,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover335, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover336ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover336.active pattern) :
    ∃ stratum ∈ cover336.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover336,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover336, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover337ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover337.active pattern) :
    ∃ stratum ∈ cover337.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover337,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover337, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover338ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover338.active pattern) :
    ∃ stratum ∈ cover338.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover338,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover338, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover339ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover339.active pattern) :
    ∃ stratum ∈ cover339.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover339,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover339, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover340ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover340.active pattern) :
    ∃ stratum ∈ cover340.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover340,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover340, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover341ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover341.active pattern) :
    ∃ stratum ∈ cover341.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover341,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover341, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover342ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover342.active pattern) :
    ∃ stratum ∈ cover342.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover342,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover342, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover343ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover343.active pattern) :
    ∃ stratum ∈ cover343.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover343,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover343, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover344ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover344.active pattern) :
    ∃ stratum ∈ cover344.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover344,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover344, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover345ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover345.active pattern) :
    ∃ stratum ∈ cover345.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover345,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover345, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover346ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover346.active pattern) :
    ∃ stratum ∈ cover346.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover346,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover346, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover347ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover347.active pattern) :
    ∃ stratum ∈ cover347.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover347,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover347, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover348ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover348.active pattern) :
    ∃ stratum ∈ cover348.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover348,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover348, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover349ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover349.active pattern) :
    ∃ stratum ∈ cover349.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover349,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover349, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover350ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover350.active pattern) :
    ∃ stratum ∈ cover350.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover350,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover350, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover351ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover351.active pattern) :
    ∃ stratum ∈ cover351.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover351,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover351, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover352ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover352.active pattern) :
    ∃ stratum ∈ cover352.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover352,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover352, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover353ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover353.active pattern) :
    ∃ stratum ∈ cover353.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover353,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover353, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover354ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover354.active pattern) :
    ∃ stratum ∈ cover354.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover354,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover354, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover355ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover355.active pattern) :
    ∃ stratum ∈ cover355.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover355,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover355, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover356ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover356.active pattern) :
    ∃ stratum ∈ cover356.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover356,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover356, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover357ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover357.active pattern) :
    ∃ stratum ∈ cover357.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover357,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover357, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover358ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover358.active pattern) :
    ∃ stratum ∈ cover358.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover358,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover358, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover359ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover359.active pattern) :
    ∃ stratum ∈ cover359.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover359,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover359, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover360ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover360.active pattern) :
    ∃ stratum ∈ cover360.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover360,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover360, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover361ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover361.active pattern) :
    ∃ stratum ∈ cover361.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover361,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover361, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover362ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover362.active pattern) :
    ∃ stratum ∈ cover362.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover362,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover362, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover363ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover363.active pattern) :
    ∃ stratum ∈ cover363.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover363,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover363, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover364ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover364.active pattern) :
    ∃ stratum ∈ cover364.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover364,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover364, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover365ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover365.active pattern) :
    ∃ stratum ∈ cover365.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover365,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover365, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover366ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover366.active pattern) :
    ∃ stratum ∈ cover366.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover366,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover366, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover367ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover367.active pattern) :
    ∃ stratum ∈ cover367.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover367,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover367, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover368ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover368.active pattern) :
    ∃ stratum ∈ cover368.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover368,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover368, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover369ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover369.active pattern) :
    ∃ stratum ∈ cover369.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover369,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover369, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover370ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover370.active pattern) :
    ∃ stratum ∈ cover370.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover370,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover370, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover371ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover371.active pattern) :
    ∃ stratum ∈ cover371.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover371,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover371, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover372ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover372.active pattern) :
    ∃ stratum ∈ cover372.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover372,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover372, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover373ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover373.active pattern) :
    ∃ stratum ∈ cover373.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover373,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover373, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover374ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover374.active pattern) :
    ∃ stratum ∈ cover374.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover374,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover374, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover375ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover375.active pattern) :
    ∃ stratum ∈ cover375.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover375,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover375, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover376ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover376.active pattern) :
    ∃ stratum ∈ cover376.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover376,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover376, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover377ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover377.active pattern) :
    ∃ stratum ∈ cover377.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover377,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover377, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover378ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover378.active pattern) :
    ∃ stratum ∈ cover378.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover378,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover378, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover379ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover379.active pattern) :
    ∃ stratum ∈ cover379.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover379,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover379, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover380ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover380.active pattern) :
    ∃ stratum ∈ cover380.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover380,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover380, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover381ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover381.active pattern) :
    ∃ stratum ∈ cover381.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover381,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover381, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover382ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover382.active pattern) :
    ∃ stratum ∈ cover382.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover382,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover382, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover383ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover383.active pattern) :
    ∃ stratum ∈ cover383.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover383,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover383, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover384ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover384.active pattern) :
    ∃ stratum ∈ cover384.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover384,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover384, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover385ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover385.active pattern) :
    ∃ stratum ∈ cover385.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover385,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover385, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover386ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover386.active pattern) :
    ∃ stratum ∈ cover386.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover386,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover386, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover387ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover387.active pattern) :
    ∃ stratum ∈ cover387.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover387,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover387, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover388ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover388.active pattern) :
    ∃ stratum ∈ cover388.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover388,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover388, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover389ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover389.active pattern) :
    ∃ stratum ∈ cover389.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover389,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover389, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover390ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover390.active pattern) :
    ∃ stratum ∈ cover390.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover390,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover390, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover391ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover391.active pattern) :
    ∃ stratum ∈ cover391.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover391,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover391, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover392ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover392.active pattern) :
    ∃ stratum ∈ cover392.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover392,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover392, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover393ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover393.active pattern) :
    ∃ stratum ∈ cover393.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover393,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover393, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover394ZeroCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern)
    (activePattern : activeMatchesProp cover394.active pattern) :
    ∃ stratum ∈ cover394.strata, zeroMatchesProp stratum.zero pattern := by
  simp (config := { maxSteps := 1000000 }) only [feasibleProp, relationLeftActiveProp,
    relationRightActiveProp] at feasiblePattern
  simp (config := { maxSteps := 1000000 }) only [cover394,
    activeMatchesProp, relationLeftActiveProp] at activePattern
  simp (config := { maxSteps := 1000000 }) only [cover394, zeroMatchesProp,
    List.mem_cons, List.not_mem_nil, exists_eq_left, exists_eq_right]
  tauto

structure CertifiedCover where
  data : ActiveCover
  zeroCovered : ∀ pattern, feasibleProp pattern →
    activeMatchesProp data.active pattern →
    ∃ stratum ∈ data.strata, zeroMatchesProp stratum.zero pattern

def certified0 : CertifiedCover := ⟨cover0, cover0ZeroCovered⟩
def certified1 : CertifiedCover := ⟨cover1, cover1ZeroCovered⟩
def certified2 : CertifiedCover := ⟨cover2, cover2ZeroCovered⟩
def certified3 : CertifiedCover := ⟨cover3, cover3ZeroCovered⟩
def certified4 : CertifiedCover := ⟨cover4, cover4ZeroCovered⟩
def certified5 : CertifiedCover := ⟨cover5, cover5ZeroCovered⟩
def certified6 : CertifiedCover := ⟨cover6, cover6ZeroCovered⟩
def certified7 : CertifiedCover := ⟨cover7, cover7ZeroCovered⟩
def certified8 : CertifiedCover := ⟨cover8, cover8ZeroCovered⟩
def certified9 : CertifiedCover := ⟨cover9, cover9ZeroCovered⟩
def certified10 : CertifiedCover := ⟨cover10, cover10ZeroCovered⟩
def certified11 : CertifiedCover := ⟨cover11, cover11ZeroCovered⟩
def certified12 : CertifiedCover := ⟨cover12, cover12ZeroCovered⟩
def certified13 : CertifiedCover := ⟨cover13, cover13ZeroCovered⟩
def certified14 : CertifiedCover := ⟨cover14, cover14ZeroCovered⟩
def certified15 : CertifiedCover := ⟨cover15, cover15ZeroCovered⟩
def certified16 : CertifiedCover := ⟨cover16, cover16ZeroCovered⟩
def certified17 : CertifiedCover := ⟨cover17, cover17ZeroCovered⟩
def certified18 : CertifiedCover := ⟨cover18, cover18ZeroCovered⟩
def certified19 : CertifiedCover := ⟨cover19, cover19ZeroCovered⟩
def certified20 : CertifiedCover := ⟨cover20, cover20ZeroCovered⟩
def certified21 : CertifiedCover := ⟨cover21, cover21ZeroCovered⟩
def certified22 : CertifiedCover := ⟨cover22, cover22ZeroCovered⟩
def certified23 : CertifiedCover := ⟨cover23, cover23ZeroCovered⟩
def certified24 : CertifiedCover := ⟨cover24, cover24ZeroCovered⟩
def certified25 : CertifiedCover := ⟨cover25, cover25ZeroCovered⟩
def certified26 : CertifiedCover := ⟨cover26, cover26ZeroCovered⟩
def certified27 : CertifiedCover := ⟨cover27, cover27ZeroCovered⟩
def certified28 : CertifiedCover := ⟨cover28, cover28ZeroCovered⟩
def certified29 : CertifiedCover := ⟨cover29, cover29ZeroCovered⟩
def certified30 : CertifiedCover := ⟨cover30, cover30ZeroCovered⟩
def certified31 : CertifiedCover := ⟨cover31, cover31ZeroCovered⟩
def certified32 : CertifiedCover := ⟨cover32, cover32ZeroCovered⟩
def certified33 : CertifiedCover := ⟨cover33, cover33ZeroCovered⟩
def certified34 : CertifiedCover := ⟨cover34, cover34ZeroCovered⟩
def certified35 : CertifiedCover := ⟨cover35, cover35ZeroCovered⟩
def certified36 : CertifiedCover := ⟨cover36, cover36ZeroCovered⟩
def certified37 : CertifiedCover := ⟨cover37, cover37ZeroCovered⟩
def certified38 : CertifiedCover := ⟨cover38, cover38ZeroCovered⟩
def certified39 : CertifiedCover := ⟨cover39, cover39ZeroCovered⟩
def certified40 : CertifiedCover := ⟨cover40, cover40ZeroCovered⟩
def certified41 : CertifiedCover := ⟨cover41, cover41ZeroCovered⟩
def certified42 : CertifiedCover := ⟨cover42, cover42ZeroCovered⟩
def certified43 : CertifiedCover := ⟨cover43, cover43ZeroCovered⟩
def certified44 : CertifiedCover := ⟨cover44, cover44ZeroCovered⟩
def certified45 : CertifiedCover := ⟨cover45, cover45ZeroCovered⟩
def certified46 : CertifiedCover := ⟨cover46, cover46ZeroCovered⟩
def certified47 : CertifiedCover := ⟨cover47, cover47ZeroCovered⟩
def certified48 : CertifiedCover := ⟨cover48, cover48ZeroCovered⟩
def certified49 : CertifiedCover := ⟨cover49, cover49ZeroCovered⟩
def certified50 : CertifiedCover := ⟨cover50, cover50ZeroCovered⟩
def certified51 : CertifiedCover := ⟨cover51, cover51ZeroCovered⟩
def certified52 : CertifiedCover := ⟨cover52, cover52ZeroCovered⟩
def certified53 : CertifiedCover := ⟨cover53, cover53ZeroCovered⟩
def certified54 : CertifiedCover := ⟨cover54, cover54ZeroCovered⟩
def certified55 : CertifiedCover := ⟨cover55, cover55ZeroCovered⟩
def certified56 : CertifiedCover := ⟨cover56, cover56ZeroCovered⟩
def certified57 : CertifiedCover := ⟨cover57, cover57ZeroCovered⟩
def certified58 : CertifiedCover := ⟨cover58, cover58ZeroCovered⟩
def certified59 : CertifiedCover := ⟨cover59, cover59ZeroCovered⟩
def certified60 : CertifiedCover := ⟨cover60, cover60ZeroCovered⟩
def certified61 : CertifiedCover := ⟨cover61, cover61ZeroCovered⟩
def certified62 : CertifiedCover := ⟨cover62, cover62ZeroCovered⟩
def certified63 : CertifiedCover := ⟨cover63, cover63ZeroCovered⟩
def certified64 : CertifiedCover := ⟨cover64, cover64ZeroCovered⟩
def certified65 : CertifiedCover := ⟨cover65, cover65ZeroCovered⟩
def certified66 : CertifiedCover := ⟨cover66, cover66ZeroCovered⟩
def certified67 : CertifiedCover := ⟨cover67, cover67ZeroCovered⟩
def certified68 : CertifiedCover := ⟨cover68, cover68ZeroCovered⟩
def certified69 : CertifiedCover := ⟨cover69, cover69ZeroCovered⟩
def certified70 : CertifiedCover := ⟨cover70, cover70ZeroCovered⟩
def certified71 : CertifiedCover := ⟨cover71, cover71ZeroCovered⟩
def certified72 : CertifiedCover := ⟨cover72, cover72ZeroCovered⟩
def certified73 : CertifiedCover := ⟨cover73, cover73ZeroCovered⟩
def certified74 : CertifiedCover := ⟨cover74, cover74ZeroCovered⟩
def certified75 : CertifiedCover := ⟨cover75, cover75ZeroCovered⟩
def certified76 : CertifiedCover := ⟨cover76, cover76ZeroCovered⟩
def certified77 : CertifiedCover := ⟨cover77, cover77ZeroCovered⟩
def certified78 : CertifiedCover := ⟨cover78, cover78ZeroCovered⟩
def certified79 : CertifiedCover := ⟨cover79, cover79ZeroCovered⟩
def certified80 : CertifiedCover := ⟨cover80, cover80ZeroCovered⟩
def certified81 : CertifiedCover := ⟨cover81, cover81ZeroCovered⟩
def certified82 : CertifiedCover := ⟨cover82, cover82ZeroCovered⟩
def certified83 : CertifiedCover := ⟨cover83, cover83ZeroCovered⟩
def certified84 : CertifiedCover := ⟨cover84, cover84ZeroCovered⟩
def certified85 : CertifiedCover := ⟨cover85, cover85ZeroCovered⟩
def certified86 : CertifiedCover := ⟨cover86, cover86ZeroCovered⟩
def certified87 : CertifiedCover := ⟨cover87, cover87ZeroCovered⟩
def certified88 : CertifiedCover := ⟨cover88, cover88ZeroCovered⟩
def certified89 : CertifiedCover := ⟨cover89, cover89ZeroCovered⟩
def certified90 : CertifiedCover := ⟨cover90, cover90ZeroCovered⟩
def certified91 : CertifiedCover := ⟨cover91, cover91ZeroCovered⟩
def certified92 : CertifiedCover := ⟨cover92, cover92ZeroCovered⟩
def certified93 : CertifiedCover := ⟨cover93, cover93ZeroCovered⟩
def certified94 : CertifiedCover := ⟨cover94, cover94ZeroCovered⟩
def certified95 : CertifiedCover := ⟨cover95, cover95ZeroCovered⟩
def certified96 : CertifiedCover := ⟨cover96, cover96ZeroCovered⟩
def certified97 : CertifiedCover := ⟨cover97, cover97ZeroCovered⟩
def certified98 : CertifiedCover := ⟨cover98, cover98ZeroCovered⟩
def certified99 : CertifiedCover := ⟨cover99, cover99ZeroCovered⟩
def certified100 : CertifiedCover := ⟨cover100, cover100ZeroCovered⟩
def certified101 : CertifiedCover := ⟨cover101, cover101ZeroCovered⟩
def certified102 : CertifiedCover := ⟨cover102, cover102ZeroCovered⟩
def certified103 : CertifiedCover := ⟨cover103, cover103ZeroCovered⟩
def certified104 : CertifiedCover := ⟨cover104, cover104ZeroCovered⟩
def certified105 : CertifiedCover := ⟨cover105, cover105ZeroCovered⟩
def certified106 : CertifiedCover := ⟨cover106, cover106ZeroCovered⟩
def certified107 : CertifiedCover := ⟨cover107, cover107ZeroCovered⟩
def certified108 : CertifiedCover := ⟨cover108, cover108ZeroCovered⟩
def certified109 : CertifiedCover := ⟨cover109, cover109ZeroCovered⟩
def certified110 : CertifiedCover := ⟨cover110, cover110ZeroCovered⟩
def certified111 : CertifiedCover := ⟨cover111, cover111ZeroCovered⟩
def certified112 : CertifiedCover := ⟨cover112, cover112ZeroCovered⟩
def certified113 : CertifiedCover := ⟨cover113, cover113ZeroCovered⟩
def certified114 : CertifiedCover := ⟨cover114, cover114ZeroCovered⟩
def certified115 : CertifiedCover := ⟨cover115, cover115ZeroCovered⟩
def certified116 : CertifiedCover := ⟨cover116, cover116ZeroCovered⟩
def certified117 : CertifiedCover := ⟨cover117, cover117ZeroCovered⟩
def certified118 : CertifiedCover := ⟨cover118, cover118ZeroCovered⟩
def certified119 : CertifiedCover := ⟨cover119, cover119ZeroCovered⟩
def certified120 : CertifiedCover := ⟨cover120, cover120ZeroCovered⟩
def certified121 : CertifiedCover := ⟨cover121, cover121ZeroCovered⟩
def certified122 : CertifiedCover := ⟨cover122, cover122ZeroCovered⟩
def certified123 : CertifiedCover := ⟨cover123, cover123ZeroCovered⟩
def certified124 : CertifiedCover := ⟨cover124, cover124ZeroCovered⟩
def certified125 : CertifiedCover := ⟨cover125, cover125ZeroCovered⟩
def certified126 : CertifiedCover := ⟨cover126, cover126ZeroCovered⟩
def certified127 : CertifiedCover := ⟨cover127, cover127ZeroCovered⟩
def certified128 : CertifiedCover := ⟨cover128, cover128ZeroCovered⟩
def certified129 : CertifiedCover := ⟨cover129, cover129ZeroCovered⟩
def certified130 : CertifiedCover := ⟨cover130, cover130ZeroCovered⟩
def certified131 : CertifiedCover := ⟨cover131, cover131ZeroCovered⟩
def certified132 : CertifiedCover := ⟨cover132, cover132ZeroCovered⟩
def certified133 : CertifiedCover := ⟨cover133, cover133ZeroCovered⟩
def certified134 : CertifiedCover := ⟨cover134, cover134ZeroCovered⟩
def certified135 : CertifiedCover := ⟨cover135, cover135ZeroCovered⟩
def certified136 : CertifiedCover := ⟨cover136, cover136ZeroCovered⟩
def certified137 : CertifiedCover := ⟨cover137, cover137ZeroCovered⟩
def certified138 : CertifiedCover := ⟨cover138, cover138ZeroCovered⟩
def certified139 : CertifiedCover := ⟨cover139, cover139ZeroCovered⟩
def certified140 : CertifiedCover := ⟨cover140, cover140ZeroCovered⟩
def certified141 : CertifiedCover := ⟨cover141, cover141ZeroCovered⟩
def certified142 : CertifiedCover := ⟨cover142, cover142ZeroCovered⟩
def certified143 : CertifiedCover := ⟨cover143, cover143ZeroCovered⟩
def certified144 : CertifiedCover := ⟨cover144, cover144ZeroCovered⟩
def certified145 : CertifiedCover := ⟨cover145, cover145ZeroCovered⟩
def certified146 : CertifiedCover := ⟨cover146, cover146ZeroCovered⟩
def certified147 : CertifiedCover := ⟨cover147, cover147ZeroCovered⟩
def certified148 : CertifiedCover := ⟨cover148, cover148ZeroCovered⟩
def certified149 : CertifiedCover := ⟨cover149, cover149ZeroCovered⟩
def certified150 : CertifiedCover := ⟨cover150, cover150ZeroCovered⟩
def certified151 : CertifiedCover := ⟨cover151, cover151ZeroCovered⟩
def certified152 : CertifiedCover := ⟨cover152, cover152ZeroCovered⟩
def certified153 : CertifiedCover := ⟨cover153, cover153ZeroCovered⟩
def certified154 : CertifiedCover := ⟨cover154, cover154ZeroCovered⟩
def certified155 : CertifiedCover := ⟨cover155, cover155ZeroCovered⟩
def certified156 : CertifiedCover := ⟨cover156, cover156ZeroCovered⟩
def certified157 : CertifiedCover := ⟨cover157, cover157ZeroCovered⟩
def certified158 : CertifiedCover := ⟨cover158, cover158ZeroCovered⟩
def certified159 : CertifiedCover := ⟨cover159, cover159ZeroCovered⟩
def certified160 : CertifiedCover := ⟨cover160, cover160ZeroCovered⟩
def certified161 : CertifiedCover := ⟨cover161, cover161ZeroCovered⟩
def certified162 : CertifiedCover := ⟨cover162, cover162ZeroCovered⟩
def certified163 : CertifiedCover := ⟨cover163, cover163ZeroCovered⟩
def certified164 : CertifiedCover := ⟨cover164, cover164ZeroCovered⟩
def certified165 : CertifiedCover := ⟨cover165, cover165ZeroCovered⟩
def certified166 : CertifiedCover := ⟨cover166, cover166ZeroCovered⟩
def certified167 : CertifiedCover := ⟨cover167, cover167ZeroCovered⟩
def certified168 : CertifiedCover := ⟨cover168, cover168ZeroCovered⟩
def certified169 : CertifiedCover := ⟨cover169, cover169ZeroCovered⟩
def certified170 : CertifiedCover := ⟨cover170, cover170ZeroCovered⟩
def certified171 : CertifiedCover := ⟨cover171, cover171ZeroCovered⟩
def certified172 : CertifiedCover := ⟨cover172, cover172ZeroCovered⟩
def certified173 : CertifiedCover := ⟨cover173, cover173ZeroCovered⟩
def certified174 : CertifiedCover := ⟨cover174, cover174ZeroCovered⟩
def certified175 : CertifiedCover := ⟨cover175, cover175ZeroCovered⟩
def certified176 : CertifiedCover := ⟨cover176, cover176ZeroCovered⟩
def certified177 : CertifiedCover := ⟨cover177, cover177ZeroCovered⟩
def certified178 : CertifiedCover := ⟨cover178, cover178ZeroCovered⟩
def certified179 : CertifiedCover := ⟨cover179, cover179ZeroCovered⟩
def certified180 : CertifiedCover := ⟨cover180, cover180ZeroCovered⟩
def certified181 : CertifiedCover := ⟨cover181, cover181ZeroCovered⟩
def certified182 : CertifiedCover := ⟨cover182, cover182ZeroCovered⟩
def certified183 : CertifiedCover := ⟨cover183, cover183ZeroCovered⟩
def certified184 : CertifiedCover := ⟨cover184, cover184ZeroCovered⟩
def certified185 : CertifiedCover := ⟨cover185, cover185ZeroCovered⟩
def certified186 : CertifiedCover := ⟨cover186, cover186ZeroCovered⟩
def certified187 : CertifiedCover := ⟨cover187, cover187ZeroCovered⟩
def certified188 : CertifiedCover := ⟨cover188, cover188ZeroCovered⟩
def certified189 : CertifiedCover := ⟨cover189, cover189ZeroCovered⟩
def certified190 : CertifiedCover := ⟨cover190, cover190ZeroCovered⟩
def certified191 : CertifiedCover := ⟨cover191, cover191ZeroCovered⟩
def certified192 : CertifiedCover := ⟨cover192, cover192ZeroCovered⟩
def certified193 : CertifiedCover := ⟨cover193, cover193ZeroCovered⟩
def certified194 : CertifiedCover := ⟨cover194, cover194ZeroCovered⟩
def certified195 : CertifiedCover := ⟨cover195, cover195ZeroCovered⟩
def certified196 : CertifiedCover := ⟨cover196, cover196ZeroCovered⟩
def certified197 : CertifiedCover := ⟨cover197, cover197ZeroCovered⟩
def certified198 : CertifiedCover := ⟨cover198, cover198ZeroCovered⟩
def certified199 : CertifiedCover := ⟨cover199, cover199ZeroCovered⟩
def certified200 : CertifiedCover := ⟨cover200, cover200ZeroCovered⟩
def certified201 : CertifiedCover := ⟨cover201, cover201ZeroCovered⟩
def certified202 : CertifiedCover := ⟨cover202, cover202ZeroCovered⟩
def certified203 : CertifiedCover := ⟨cover203, cover203ZeroCovered⟩
def certified204 : CertifiedCover := ⟨cover204, cover204ZeroCovered⟩
def certified205 : CertifiedCover := ⟨cover205, cover205ZeroCovered⟩
def certified206 : CertifiedCover := ⟨cover206, cover206ZeroCovered⟩
def certified207 : CertifiedCover := ⟨cover207, cover207ZeroCovered⟩
def certified208 : CertifiedCover := ⟨cover208, cover208ZeroCovered⟩
def certified209 : CertifiedCover := ⟨cover209, cover209ZeroCovered⟩
def certified210 : CertifiedCover := ⟨cover210, cover210ZeroCovered⟩
def certified211 : CertifiedCover := ⟨cover211, cover211ZeroCovered⟩
def certified212 : CertifiedCover := ⟨cover212, cover212ZeroCovered⟩
def certified213 : CertifiedCover := ⟨cover213, cover213ZeroCovered⟩
def certified214 : CertifiedCover := ⟨cover214, cover214ZeroCovered⟩
def certified215 : CertifiedCover := ⟨cover215, cover215ZeroCovered⟩
def certified216 : CertifiedCover := ⟨cover216, cover216ZeroCovered⟩
def certified217 : CertifiedCover := ⟨cover217, cover217ZeroCovered⟩
def certified218 : CertifiedCover := ⟨cover218, cover218ZeroCovered⟩
def certified219 : CertifiedCover := ⟨cover219, cover219ZeroCovered⟩
def certified220 : CertifiedCover := ⟨cover220, cover220ZeroCovered⟩
def certified221 : CertifiedCover := ⟨cover221, cover221ZeroCovered⟩
def certified222 : CertifiedCover := ⟨cover222, cover222ZeroCovered⟩
def certified223 : CertifiedCover := ⟨cover223, cover223ZeroCovered⟩
def certified224 : CertifiedCover := ⟨cover224, cover224ZeroCovered⟩
def certified225 : CertifiedCover := ⟨cover225, cover225ZeroCovered⟩
def certified226 : CertifiedCover := ⟨cover226, cover226ZeroCovered⟩
def certified227 : CertifiedCover := ⟨cover227, cover227ZeroCovered⟩
def certified228 : CertifiedCover := ⟨cover228, cover228ZeroCovered⟩
def certified229 : CertifiedCover := ⟨cover229, cover229ZeroCovered⟩
def certified230 : CertifiedCover := ⟨cover230, cover230ZeroCovered⟩
def certified231 : CertifiedCover := ⟨cover231, cover231ZeroCovered⟩
def certified232 : CertifiedCover := ⟨cover232, cover232ZeroCovered⟩
def certified233 : CertifiedCover := ⟨cover233, cover233ZeroCovered⟩
def certified234 : CertifiedCover := ⟨cover234, cover234ZeroCovered⟩
def certified235 : CertifiedCover := ⟨cover235, cover235ZeroCovered⟩
def certified236 : CertifiedCover := ⟨cover236, cover236ZeroCovered⟩
def certified237 : CertifiedCover := ⟨cover237, cover237ZeroCovered⟩
def certified238 : CertifiedCover := ⟨cover238, cover238ZeroCovered⟩
def certified239 : CertifiedCover := ⟨cover239, cover239ZeroCovered⟩
def certified240 : CertifiedCover := ⟨cover240, cover240ZeroCovered⟩
def certified241 : CertifiedCover := ⟨cover241, cover241ZeroCovered⟩
def certified242 : CertifiedCover := ⟨cover242, cover242ZeroCovered⟩
def certified243 : CertifiedCover := ⟨cover243, cover243ZeroCovered⟩
def certified244 : CertifiedCover := ⟨cover244, cover244ZeroCovered⟩
def certified245 : CertifiedCover := ⟨cover245, cover245ZeroCovered⟩
def certified246 : CertifiedCover := ⟨cover246, cover246ZeroCovered⟩
def certified247 : CertifiedCover := ⟨cover247, cover247ZeroCovered⟩
def certified248 : CertifiedCover := ⟨cover248, cover248ZeroCovered⟩
def certified249 : CertifiedCover := ⟨cover249, cover249ZeroCovered⟩
def certified250 : CertifiedCover := ⟨cover250, cover250ZeroCovered⟩
def certified251 : CertifiedCover := ⟨cover251, cover251ZeroCovered⟩
def certified252 : CertifiedCover := ⟨cover252, cover252ZeroCovered⟩
def certified253 : CertifiedCover := ⟨cover253, cover253ZeroCovered⟩
def certified254 : CertifiedCover := ⟨cover254, cover254ZeroCovered⟩
def certified255 : CertifiedCover := ⟨cover255, cover255ZeroCovered⟩
def certified256 : CertifiedCover := ⟨cover256, cover256ZeroCovered⟩
def certified257 : CertifiedCover := ⟨cover257, cover257ZeroCovered⟩
def certified258 : CertifiedCover := ⟨cover258, cover258ZeroCovered⟩
def certified259 : CertifiedCover := ⟨cover259, cover259ZeroCovered⟩
def certified260 : CertifiedCover := ⟨cover260, cover260ZeroCovered⟩
def certified261 : CertifiedCover := ⟨cover261, cover261ZeroCovered⟩
def certified262 : CertifiedCover := ⟨cover262, cover262ZeroCovered⟩
def certified263 : CertifiedCover := ⟨cover263, cover263ZeroCovered⟩
def certified264 : CertifiedCover := ⟨cover264, cover264ZeroCovered⟩
def certified265 : CertifiedCover := ⟨cover265, cover265ZeroCovered⟩
def certified266 : CertifiedCover := ⟨cover266, cover266ZeroCovered⟩
def certified267 : CertifiedCover := ⟨cover267, cover267ZeroCovered⟩
def certified268 : CertifiedCover := ⟨cover268, cover268ZeroCovered⟩
def certified269 : CertifiedCover := ⟨cover269, cover269ZeroCovered⟩
def certified270 : CertifiedCover := ⟨cover270, cover270ZeroCovered⟩
def certified271 : CertifiedCover := ⟨cover271, cover271ZeroCovered⟩
def certified272 : CertifiedCover := ⟨cover272, cover272ZeroCovered⟩
def certified273 : CertifiedCover := ⟨cover273, cover273ZeroCovered⟩
def certified274 : CertifiedCover := ⟨cover274, cover274ZeroCovered⟩
def certified275 : CertifiedCover := ⟨cover275, cover275ZeroCovered⟩
def certified276 : CertifiedCover := ⟨cover276, cover276ZeroCovered⟩
def certified277 : CertifiedCover := ⟨cover277, cover277ZeroCovered⟩
def certified278 : CertifiedCover := ⟨cover278, cover278ZeroCovered⟩
def certified279 : CertifiedCover := ⟨cover279, cover279ZeroCovered⟩
def certified280 : CertifiedCover := ⟨cover280, cover280ZeroCovered⟩
def certified281 : CertifiedCover := ⟨cover281, cover281ZeroCovered⟩
def certified282 : CertifiedCover := ⟨cover282, cover282ZeroCovered⟩
def certified283 : CertifiedCover := ⟨cover283, cover283ZeroCovered⟩
def certified284 : CertifiedCover := ⟨cover284, cover284ZeroCovered⟩
def certified285 : CertifiedCover := ⟨cover285, cover285ZeroCovered⟩
def certified286 : CertifiedCover := ⟨cover286, cover286ZeroCovered⟩
def certified287 : CertifiedCover := ⟨cover287, cover287ZeroCovered⟩
def certified288 : CertifiedCover := ⟨cover288, cover288ZeroCovered⟩
def certified289 : CertifiedCover := ⟨cover289, cover289ZeroCovered⟩
def certified290 : CertifiedCover := ⟨cover290, cover290ZeroCovered⟩
def certified291 : CertifiedCover := ⟨cover291, cover291ZeroCovered⟩
def certified292 : CertifiedCover := ⟨cover292, cover292ZeroCovered⟩
def certified293 : CertifiedCover := ⟨cover293, cover293ZeroCovered⟩
def certified294 : CertifiedCover := ⟨cover294, cover294ZeroCovered⟩
def certified295 : CertifiedCover := ⟨cover295, cover295ZeroCovered⟩
def certified296 : CertifiedCover := ⟨cover296, cover296ZeroCovered⟩
def certified297 : CertifiedCover := ⟨cover297, cover297ZeroCovered⟩
def certified298 : CertifiedCover := ⟨cover298, cover298ZeroCovered⟩
def certified299 : CertifiedCover := ⟨cover299, cover299ZeroCovered⟩
def certified300 : CertifiedCover := ⟨cover300, cover300ZeroCovered⟩
def certified301 : CertifiedCover := ⟨cover301, cover301ZeroCovered⟩
def certified302 : CertifiedCover := ⟨cover302, cover302ZeroCovered⟩
def certified303 : CertifiedCover := ⟨cover303, cover303ZeroCovered⟩
def certified304 : CertifiedCover := ⟨cover304, cover304ZeroCovered⟩
def certified305 : CertifiedCover := ⟨cover305, cover305ZeroCovered⟩
def certified306 : CertifiedCover := ⟨cover306, cover306ZeroCovered⟩
def certified307 : CertifiedCover := ⟨cover307, cover307ZeroCovered⟩
def certified308 : CertifiedCover := ⟨cover308, cover308ZeroCovered⟩
def certified309 : CertifiedCover := ⟨cover309, cover309ZeroCovered⟩
def certified310 : CertifiedCover := ⟨cover310, cover310ZeroCovered⟩
def certified311 : CertifiedCover := ⟨cover311, cover311ZeroCovered⟩
def certified312 : CertifiedCover := ⟨cover312, cover312ZeroCovered⟩
def certified313 : CertifiedCover := ⟨cover313, cover313ZeroCovered⟩
def certified314 : CertifiedCover := ⟨cover314, cover314ZeroCovered⟩
def certified315 : CertifiedCover := ⟨cover315, cover315ZeroCovered⟩
def certified316 : CertifiedCover := ⟨cover316, cover316ZeroCovered⟩
def certified317 : CertifiedCover := ⟨cover317, cover317ZeroCovered⟩
def certified318 : CertifiedCover := ⟨cover318, cover318ZeroCovered⟩
def certified319 : CertifiedCover := ⟨cover319, cover319ZeroCovered⟩
def certified320 : CertifiedCover := ⟨cover320, cover320ZeroCovered⟩
def certified321 : CertifiedCover := ⟨cover321, cover321ZeroCovered⟩
def certified322 : CertifiedCover := ⟨cover322, cover322ZeroCovered⟩
def certified323 : CertifiedCover := ⟨cover323, cover323ZeroCovered⟩
def certified324 : CertifiedCover := ⟨cover324, cover324ZeroCovered⟩
def certified325 : CertifiedCover := ⟨cover325, cover325ZeroCovered⟩
def certified326 : CertifiedCover := ⟨cover326, cover326ZeroCovered⟩
def certified327 : CertifiedCover := ⟨cover327, cover327ZeroCovered⟩
def certified328 : CertifiedCover := ⟨cover328, cover328ZeroCovered⟩
def certified329 : CertifiedCover := ⟨cover329, cover329ZeroCovered⟩
def certified330 : CertifiedCover := ⟨cover330, cover330ZeroCovered⟩
def certified331 : CertifiedCover := ⟨cover331, cover331ZeroCovered⟩
def certified332 : CertifiedCover := ⟨cover332, cover332ZeroCovered⟩
def certified333 : CertifiedCover := ⟨cover333, cover333ZeroCovered⟩
def certified334 : CertifiedCover := ⟨cover334, cover334ZeroCovered⟩
def certified335 : CertifiedCover := ⟨cover335, cover335ZeroCovered⟩
def certified336 : CertifiedCover := ⟨cover336, cover336ZeroCovered⟩
def certified337 : CertifiedCover := ⟨cover337, cover337ZeroCovered⟩
def certified338 : CertifiedCover := ⟨cover338, cover338ZeroCovered⟩
def certified339 : CertifiedCover := ⟨cover339, cover339ZeroCovered⟩
def certified340 : CertifiedCover := ⟨cover340, cover340ZeroCovered⟩
def certified341 : CertifiedCover := ⟨cover341, cover341ZeroCovered⟩
def certified342 : CertifiedCover := ⟨cover342, cover342ZeroCovered⟩
def certified343 : CertifiedCover := ⟨cover343, cover343ZeroCovered⟩
def certified344 : CertifiedCover := ⟨cover344, cover344ZeroCovered⟩
def certified345 : CertifiedCover := ⟨cover345, cover345ZeroCovered⟩
def certified346 : CertifiedCover := ⟨cover346, cover346ZeroCovered⟩
def certified347 : CertifiedCover := ⟨cover347, cover347ZeroCovered⟩
def certified348 : CertifiedCover := ⟨cover348, cover348ZeroCovered⟩
def certified349 : CertifiedCover := ⟨cover349, cover349ZeroCovered⟩
def certified350 : CertifiedCover := ⟨cover350, cover350ZeroCovered⟩
def certified351 : CertifiedCover := ⟨cover351, cover351ZeroCovered⟩
def certified352 : CertifiedCover := ⟨cover352, cover352ZeroCovered⟩
def certified353 : CertifiedCover := ⟨cover353, cover353ZeroCovered⟩
def certified354 : CertifiedCover := ⟨cover354, cover354ZeroCovered⟩
def certified355 : CertifiedCover := ⟨cover355, cover355ZeroCovered⟩
def certified356 : CertifiedCover := ⟨cover356, cover356ZeroCovered⟩
def certified357 : CertifiedCover := ⟨cover357, cover357ZeroCovered⟩
def certified358 : CertifiedCover := ⟨cover358, cover358ZeroCovered⟩
def certified359 : CertifiedCover := ⟨cover359, cover359ZeroCovered⟩
def certified360 : CertifiedCover := ⟨cover360, cover360ZeroCovered⟩
def certified361 : CertifiedCover := ⟨cover361, cover361ZeroCovered⟩
def certified362 : CertifiedCover := ⟨cover362, cover362ZeroCovered⟩
def certified363 : CertifiedCover := ⟨cover363, cover363ZeroCovered⟩
def certified364 : CertifiedCover := ⟨cover364, cover364ZeroCovered⟩
def certified365 : CertifiedCover := ⟨cover365, cover365ZeroCovered⟩
def certified366 : CertifiedCover := ⟨cover366, cover366ZeroCovered⟩
def certified367 : CertifiedCover := ⟨cover367, cover367ZeroCovered⟩
def certified368 : CertifiedCover := ⟨cover368, cover368ZeroCovered⟩
def certified369 : CertifiedCover := ⟨cover369, cover369ZeroCovered⟩
def certified370 : CertifiedCover := ⟨cover370, cover370ZeroCovered⟩
def certified371 : CertifiedCover := ⟨cover371, cover371ZeroCovered⟩
def certified372 : CertifiedCover := ⟨cover372, cover372ZeroCovered⟩
def certified373 : CertifiedCover := ⟨cover373, cover373ZeroCovered⟩
def certified374 : CertifiedCover := ⟨cover374, cover374ZeroCovered⟩
def certified375 : CertifiedCover := ⟨cover375, cover375ZeroCovered⟩
def certified376 : CertifiedCover := ⟨cover376, cover376ZeroCovered⟩
def certified377 : CertifiedCover := ⟨cover377, cover377ZeroCovered⟩
def certified378 : CertifiedCover := ⟨cover378, cover378ZeroCovered⟩
def certified379 : CertifiedCover := ⟨cover379, cover379ZeroCovered⟩
def certified380 : CertifiedCover := ⟨cover380, cover380ZeroCovered⟩
def certified381 : CertifiedCover := ⟨cover381, cover381ZeroCovered⟩
def certified382 : CertifiedCover := ⟨cover382, cover382ZeroCovered⟩
def certified383 : CertifiedCover := ⟨cover383, cover383ZeroCovered⟩
def certified384 : CertifiedCover := ⟨cover384, cover384ZeroCovered⟩
def certified385 : CertifiedCover := ⟨cover385, cover385ZeroCovered⟩
def certified386 : CertifiedCover := ⟨cover386, cover386ZeroCovered⟩
def certified387 : CertifiedCover := ⟨cover387, cover387ZeroCovered⟩
def certified388 : CertifiedCover := ⟨cover388, cover388ZeroCovered⟩
def certified389 : CertifiedCover := ⟨cover389, cover389ZeroCovered⟩
def certified390 : CertifiedCover := ⟨cover390, cover390ZeroCovered⟩
def certified391 : CertifiedCover := ⟨cover391, cover391ZeroCovered⟩
def certified392 : CertifiedCover := ⟨cover392, cover392ZeroCovered⟩
def certified393 : CertifiedCover := ⟨cover393, cover393ZeroCovered⟩
def certified394 : CertifiedCover := ⟨cover394, cover394ZeroCovered⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem feasibleHasCertifiedCover (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern) :
    ∃ certificate : CertifiedCover,
      activeMatchesProp certificate.data.active pattern := by
  have activeDisjunction :
    activeMatchesProp cover0.active pattern ∨
      activeMatchesProp cover1.active pattern ∨
      activeMatchesProp cover2.active pattern ∨
      activeMatchesProp cover3.active pattern ∨
      activeMatchesProp cover4.active pattern ∨
      activeMatchesProp cover5.active pattern ∨
      activeMatchesProp cover6.active pattern ∨
      activeMatchesProp cover7.active pattern ∨
      activeMatchesProp cover8.active pattern ∨
      activeMatchesProp cover9.active pattern ∨
      activeMatchesProp cover10.active pattern ∨
      activeMatchesProp cover11.active pattern ∨
      activeMatchesProp cover12.active pattern ∨
      activeMatchesProp cover13.active pattern ∨
      activeMatchesProp cover14.active pattern ∨
      activeMatchesProp cover15.active pattern ∨
      activeMatchesProp cover16.active pattern ∨
      activeMatchesProp cover17.active pattern ∨
      activeMatchesProp cover18.active pattern ∨
      activeMatchesProp cover19.active pattern ∨
      activeMatchesProp cover20.active pattern ∨
      activeMatchesProp cover21.active pattern ∨
      activeMatchesProp cover22.active pattern ∨
      activeMatchesProp cover23.active pattern ∨
      activeMatchesProp cover24.active pattern ∨
      activeMatchesProp cover25.active pattern ∨
      activeMatchesProp cover26.active pattern ∨
      activeMatchesProp cover27.active pattern ∨
      activeMatchesProp cover28.active pattern ∨
      activeMatchesProp cover29.active pattern ∨
      activeMatchesProp cover30.active pattern ∨
      activeMatchesProp cover31.active pattern ∨
      activeMatchesProp cover32.active pattern ∨
      activeMatchesProp cover33.active pattern ∨
      activeMatchesProp cover34.active pattern ∨
      activeMatchesProp cover35.active pattern ∨
      activeMatchesProp cover36.active pattern ∨
      activeMatchesProp cover37.active pattern ∨
      activeMatchesProp cover38.active pattern ∨
      activeMatchesProp cover39.active pattern ∨
      activeMatchesProp cover40.active pattern ∨
      activeMatchesProp cover41.active pattern ∨
      activeMatchesProp cover42.active pattern ∨
      activeMatchesProp cover43.active pattern ∨
      activeMatchesProp cover44.active pattern ∨
      activeMatchesProp cover45.active pattern ∨
      activeMatchesProp cover46.active pattern ∨
      activeMatchesProp cover47.active pattern ∨
      activeMatchesProp cover48.active pattern ∨
      activeMatchesProp cover49.active pattern ∨
      activeMatchesProp cover50.active pattern ∨
      activeMatchesProp cover51.active pattern ∨
      activeMatchesProp cover52.active pattern ∨
      activeMatchesProp cover53.active pattern ∨
      activeMatchesProp cover54.active pattern ∨
      activeMatchesProp cover55.active pattern ∨
      activeMatchesProp cover56.active pattern ∨
      activeMatchesProp cover57.active pattern ∨
      activeMatchesProp cover58.active pattern ∨
      activeMatchesProp cover59.active pattern ∨
      activeMatchesProp cover60.active pattern ∨
      activeMatchesProp cover61.active pattern ∨
      activeMatchesProp cover62.active pattern ∨
      activeMatchesProp cover63.active pattern ∨
      activeMatchesProp cover64.active pattern ∨
      activeMatchesProp cover65.active pattern ∨
      activeMatchesProp cover66.active pattern ∨
      activeMatchesProp cover67.active pattern ∨
      activeMatchesProp cover68.active pattern ∨
      activeMatchesProp cover69.active pattern ∨
      activeMatchesProp cover70.active pattern ∨
      activeMatchesProp cover71.active pattern ∨
      activeMatchesProp cover72.active pattern ∨
      activeMatchesProp cover73.active pattern ∨
      activeMatchesProp cover74.active pattern ∨
      activeMatchesProp cover75.active pattern ∨
      activeMatchesProp cover76.active pattern ∨
      activeMatchesProp cover77.active pattern ∨
      activeMatchesProp cover78.active pattern ∨
      activeMatchesProp cover79.active pattern ∨
      activeMatchesProp cover80.active pattern ∨
      activeMatchesProp cover81.active pattern ∨
      activeMatchesProp cover82.active pattern ∨
      activeMatchesProp cover83.active pattern ∨
      activeMatchesProp cover84.active pattern ∨
      activeMatchesProp cover85.active pattern ∨
      activeMatchesProp cover86.active pattern ∨
      activeMatchesProp cover87.active pattern ∨
      activeMatchesProp cover88.active pattern ∨
      activeMatchesProp cover89.active pattern ∨
      activeMatchesProp cover90.active pattern ∨
      activeMatchesProp cover91.active pattern ∨
      activeMatchesProp cover92.active pattern ∨
      activeMatchesProp cover93.active pattern ∨
      activeMatchesProp cover94.active pattern ∨
      activeMatchesProp cover95.active pattern ∨
      activeMatchesProp cover96.active pattern ∨
      activeMatchesProp cover97.active pattern ∨
      activeMatchesProp cover98.active pattern ∨
      activeMatchesProp cover99.active pattern ∨
      activeMatchesProp cover100.active pattern ∨
      activeMatchesProp cover101.active pattern ∨
      activeMatchesProp cover102.active pattern ∨
      activeMatchesProp cover103.active pattern ∨
      activeMatchesProp cover104.active pattern ∨
      activeMatchesProp cover105.active pattern ∨
      activeMatchesProp cover106.active pattern ∨
      activeMatchesProp cover107.active pattern ∨
      activeMatchesProp cover108.active pattern ∨
      activeMatchesProp cover109.active pattern ∨
      activeMatchesProp cover110.active pattern ∨
      activeMatchesProp cover111.active pattern ∨
      activeMatchesProp cover112.active pattern ∨
      activeMatchesProp cover113.active pattern ∨
      activeMatchesProp cover114.active pattern ∨
      activeMatchesProp cover115.active pattern ∨
      activeMatchesProp cover116.active pattern ∨
      activeMatchesProp cover117.active pattern ∨
      activeMatchesProp cover118.active pattern ∨
      activeMatchesProp cover119.active pattern ∨
      activeMatchesProp cover120.active pattern ∨
      activeMatchesProp cover121.active pattern ∨
      activeMatchesProp cover122.active pattern ∨
      activeMatchesProp cover123.active pattern ∨
      activeMatchesProp cover124.active pattern ∨
      activeMatchesProp cover125.active pattern ∨
      activeMatchesProp cover126.active pattern ∨
      activeMatchesProp cover127.active pattern ∨
      activeMatchesProp cover128.active pattern ∨
      activeMatchesProp cover129.active pattern ∨
      activeMatchesProp cover130.active pattern ∨
      activeMatchesProp cover131.active pattern ∨
      activeMatchesProp cover132.active pattern ∨
      activeMatchesProp cover133.active pattern ∨
      activeMatchesProp cover134.active pattern ∨
      activeMatchesProp cover135.active pattern ∨
      activeMatchesProp cover136.active pattern ∨
      activeMatchesProp cover137.active pattern ∨
      activeMatchesProp cover138.active pattern ∨
      activeMatchesProp cover139.active pattern ∨
      activeMatchesProp cover140.active pattern ∨
      activeMatchesProp cover141.active pattern ∨
      activeMatchesProp cover142.active pattern ∨
      activeMatchesProp cover143.active pattern ∨
      activeMatchesProp cover144.active pattern ∨
      activeMatchesProp cover145.active pattern ∨
      activeMatchesProp cover146.active pattern ∨
      activeMatchesProp cover147.active pattern ∨
      activeMatchesProp cover148.active pattern ∨
      activeMatchesProp cover149.active pattern ∨
      activeMatchesProp cover150.active pattern ∨
      activeMatchesProp cover151.active pattern ∨
      activeMatchesProp cover152.active pattern ∨
      activeMatchesProp cover153.active pattern ∨
      activeMatchesProp cover154.active pattern ∨
      activeMatchesProp cover155.active pattern ∨
      activeMatchesProp cover156.active pattern ∨
      activeMatchesProp cover157.active pattern ∨
      activeMatchesProp cover158.active pattern ∨
      activeMatchesProp cover159.active pattern ∨
      activeMatchesProp cover160.active pattern ∨
      activeMatchesProp cover161.active pattern ∨
      activeMatchesProp cover162.active pattern ∨
      activeMatchesProp cover163.active pattern ∨
      activeMatchesProp cover164.active pattern ∨
      activeMatchesProp cover165.active pattern ∨
      activeMatchesProp cover166.active pattern ∨
      activeMatchesProp cover167.active pattern ∨
      activeMatchesProp cover168.active pattern ∨
      activeMatchesProp cover169.active pattern ∨
      activeMatchesProp cover170.active pattern ∨
      activeMatchesProp cover171.active pattern ∨
      activeMatchesProp cover172.active pattern ∨
      activeMatchesProp cover173.active pattern ∨
      activeMatchesProp cover174.active pattern ∨
      activeMatchesProp cover175.active pattern ∨
      activeMatchesProp cover176.active pattern ∨
      activeMatchesProp cover177.active pattern ∨
      activeMatchesProp cover178.active pattern ∨
      activeMatchesProp cover179.active pattern ∨
      activeMatchesProp cover180.active pattern ∨
      activeMatchesProp cover181.active pattern ∨
      activeMatchesProp cover182.active pattern ∨
      activeMatchesProp cover183.active pattern ∨
      activeMatchesProp cover184.active pattern ∨
      activeMatchesProp cover185.active pattern ∨
      activeMatchesProp cover186.active pattern ∨
      activeMatchesProp cover187.active pattern ∨
      activeMatchesProp cover188.active pattern ∨
      activeMatchesProp cover189.active pattern ∨
      activeMatchesProp cover190.active pattern ∨
      activeMatchesProp cover191.active pattern ∨
      activeMatchesProp cover192.active pattern ∨
      activeMatchesProp cover193.active pattern ∨
      activeMatchesProp cover194.active pattern ∨
      activeMatchesProp cover195.active pattern ∨
      activeMatchesProp cover196.active pattern ∨
      activeMatchesProp cover197.active pattern ∨
      activeMatchesProp cover198.active pattern ∨
      activeMatchesProp cover199.active pattern ∨
      activeMatchesProp cover200.active pattern ∨
      activeMatchesProp cover201.active pattern ∨
      activeMatchesProp cover202.active pattern ∨
      activeMatchesProp cover203.active pattern ∨
      activeMatchesProp cover204.active pattern ∨
      activeMatchesProp cover205.active pattern ∨
      activeMatchesProp cover206.active pattern ∨
      activeMatchesProp cover207.active pattern ∨
      activeMatchesProp cover208.active pattern ∨
      activeMatchesProp cover209.active pattern ∨
      activeMatchesProp cover210.active pattern ∨
      activeMatchesProp cover211.active pattern ∨
      activeMatchesProp cover212.active pattern ∨
      activeMatchesProp cover213.active pattern ∨
      activeMatchesProp cover214.active pattern ∨
      activeMatchesProp cover215.active pattern ∨
      activeMatchesProp cover216.active pattern ∨
      activeMatchesProp cover217.active pattern ∨
      activeMatchesProp cover218.active pattern ∨
      activeMatchesProp cover219.active pattern ∨
      activeMatchesProp cover220.active pattern ∨
      activeMatchesProp cover221.active pattern ∨
      activeMatchesProp cover222.active pattern ∨
      activeMatchesProp cover223.active pattern ∨
      activeMatchesProp cover224.active pattern ∨
      activeMatchesProp cover225.active pattern ∨
      activeMatchesProp cover226.active pattern ∨
      activeMatchesProp cover227.active pattern ∨
      activeMatchesProp cover228.active pattern ∨
      activeMatchesProp cover229.active pattern ∨
      activeMatchesProp cover230.active pattern ∨
      activeMatchesProp cover231.active pattern ∨
      activeMatchesProp cover232.active pattern ∨
      activeMatchesProp cover233.active pattern ∨
      activeMatchesProp cover234.active pattern ∨
      activeMatchesProp cover235.active pattern ∨
      activeMatchesProp cover236.active pattern ∨
      activeMatchesProp cover237.active pattern ∨
      activeMatchesProp cover238.active pattern ∨
      activeMatchesProp cover239.active pattern ∨
      activeMatchesProp cover240.active pattern ∨
      activeMatchesProp cover241.active pattern ∨
      activeMatchesProp cover242.active pattern ∨
      activeMatchesProp cover243.active pattern ∨
      activeMatchesProp cover244.active pattern ∨
      activeMatchesProp cover245.active pattern ∨
      activeMatchesProp cover246.active pattern ∨
      activeMatchesProp cover247.active pattern ∨
      activeMatchesProp cover248.active pattern ∨
      activeMatchesProp cover249.active pattern ∨
      activeMatchesProp cover250.active pattern ∨
      activeMatchesProp cover251.active pattern ∨
      activeMatchesProp cover252.active pattern ∨
      activeMatchesProp cover253.active pattern ∨
      activeMatchesProp cover254.active pattern ∨
      activeMatchesProp cover255.active pattern ∨
      activeMatchesProp cover256.active pattern ∨
      activeMatchesProp cover257.active pattern ∨
      activeMatchesProp cover258.active pattern ∨
      activeMatchesProp cover259.active pattern ∨
      activeMatchesProp cover260.active pattern ∨
      activeMatchesProp cover261.active pattern ∨
      activeMatchesProp cover262.active pattern ∨
      activeMatchesProp cover263.active pattern ∨
      activeMatchesProp cover264.active pattern ∨
      activeMatchesProp cover265.active pattern ∨
      activeMatchesProp cover266.active pattern ∨
      activeMatchesProp cover267.active pattern ∨
      activeMatchesProp cover268.active pattern ∨
      activeMatchesProp cover269.active pattern ∨
      activeMatchesProp cover270.active pattern ∨
      activeMatchesProp cover271.active pattern ∨
      activeMatchesProp cover272.active pattern ∨
      activeMatchesProp cover273.active pattern ∨
      activeMatchesProp cover274.active pattern ∨
      activeMatchesProp cover275.active pattern ∨
      activeMatchesProp cover276.active pattern ∨
      activeMatchesProp cover277.active pattern ∨
      activeMatchesProp cover278.active pattern ∨
      activeMatchesProp cover279.active pattern ∨
      activeMatchesProp cover280.active pattern ∨
      activeMatchesProp cover281.active pattern ∨
      activeMatchesProp cover282.active pattern ∨
      activeMatchesProp cover283.active pattern ∨
      activeMatchesProp cover284.active pattern ∨
      activeMatchesProp cover285.active pattern ∨
      activeMatchesProp cover286.active pattern ∨
      activeMatchesProp cover287.active pattern ∨
      activeMatchesProp cover288.active pattern ∨
      activeMatchesProp cover289.active pattern ∨
      activeMatchesProp cover290.active pattern ∨
      activeMatchesProp cover291.active pattern ∨
      activeMatchesProp cover292.active pattern ∨
      activeMatchesProp cover293.active pattern ∨
      activeMatchesProp cover294.active pattern ∨
      activeMatchesProp cover295.active pattern ∨
      activeMatchesProp cover296.active pattern ∨
      activeMatchesProp cover297.active pattern ∨
      activeMatchesProp cover298.active pattern ∨
      activeMatchesProp cover299.active pattern ∨
      activeMatchesProp cover300.active pattern ∨
      activeMatchesProp cover301.active pattern ∨
      activeMatchesProp cover302.active pattern ∨
      activeMatchesProp cover303.active pattern ∨
      activeMatchesProp cover304.active pattern ∨
      activeMatchesProp cover305.active pattern ∨
      activeMatchesProp cover306.active pattern ∨
      activeMatchesProp cover307.active pattern ∨
      activeMatchesProp cover308.active pattern ∨
      activeMatchesProp cover309.active pattern ∨
      activeMatchesProp cover310.active pattern ∨
      activeMatchesProp cover311.active pattern ∨
      activeMatchesProp cover312.active pattern ∨
      activeMatchesProp cover313.active pattern ∨
      activeMatchesProp cover314.active pattern ∨
      activeMatchesProp cover315.active pattern ∨
      activeMatchesProp cover316.active pattern ∨
      activeMatchesProp cover317.active pattern ∨
      activeMatchesProp cover318.active pattern ∨
      activeMatchesProp cover319.active pattern ∨
      activeMatchesProp cover320.active pattern ∨
      activeMatchesProp cover321.active pattern ∨
      activeMatchesProp cover322.active pattern ∨
      activeMatchesProp cover323.active pattern ∨
      activeMatchesProp cover324.active pattern ∨
      activeMatchesProp cover325.active pattern ∨
      activeMatchesProp cover326.active pattern ∨
      activeMatchesProp cover327.active pattern ∨
      activeMatchesProp cover328.active pattern ∨
      activeMatchesProp cover329.active pattern ∨
      activeMatchesProp cover330.active pattern ∨
      activeMatchesProp cover331.active pattern ∨
      activeMatchesProp cover332.active pattern ∨
      activeMatchesProp cover333.active pattern ∨
      activeMatchesProp cover334.active pattern ∨
      activeMatchesProp cover335.active pattern ∨
      activeMatchesProp cover336.active pattern ∨
      activeMatchesProp cover337.active pattern ∨
      activeMatchesProp cover338.active pattern ∨
      activeMatchesProp cover339.active pattern ∨
      activeMatchesProp cover340.active pattern ∨
      activeMatchesProp cover341.active pattern ∨
      activeMatchesProp cover342.active pattern ∨
      activeMatchesProp cover343.active pattern ∨
      activeMatchesProp cover344.active pattern ∨
      activeMatchesProp cover345.active pattern ∨
      activeMatchesProp cover346.active pattern ∨
      activeMatchesProp cover347.active pattern ∨
      activeMatchesProp cover348.active pattern ∨
      activeMatchesProp cover349.active pattern ∨
      activeMatchesProp cover350.active pattern ∨
      activeMatchesProp cover351.active pattern ∨
      activeMatchesProp cover352.active pattern ∨
      activeMatchesProp cover353.active pattern ∨
      activeMatchesProp cover354.active pattern ∨
      activeMatchesProp cover355.active pattern ∨
      activeMatchesProp cover356.active pattern ∨
      activeMatchesProp cover357.active pattern ∨
      activeMatchesProp cover358.active pattern ∨
      activeMatchesProp cover359.active pattern ∨
      activeMatchesProp cover360.active pattern ∨
      activeMatchesProp cover361.active pattern ∨
      activeMatchesProp cover362.active pattern ∨
      activeMatchesProp cover363.active pattern ∨
      activeMatchesProp cover364.active pattern ∨
      activeMatchesProp cover365.active pattern ∨
      activeMatchesProp cover366.active pattern ∨
      activeMatchesProp cover367.active pattern ∨
      activeMatchesProp cover368.active pattern ∨
      activeMatchesProp cover369.active pattern ∨
      activeMatchesProp cover370.active pattern ∨
      activeMatchesProp cover371.active pattern ∨
      activeMatchesProp cover372.active pattern ∨
      activeMatchesProp cover373.active pattern ∨
      activeMatchesProp cover374.active pattern ∨
      activeMatchesProp cover375.active pattern ∨
      activeMatchesProp cover376.active pattern ∨
      activeMatchesProp cover377.active pattern ∨
      activeMatchesProp cover378.active pattern ∨
      activeMatchesProp cover379.active pattern ∨
      activeMatchesProp cover380.active pattern ∨
      activeMatchesProp cover381.active pattern ∨
      activeMatchesProp cover382.active pattern ∨
      activeMatchesProp cover383.active pattern ∨
      activeMatchesProp cover384.active pattern ∨
      activeMatchesProp cover385.active pattern ∨
      activeMatchesProp cover386.active pattern ∨
      activeMatchesProp cover387.active pattern ∨
      activeMatchesProp cover388.active pattern ∨
      activeMatchesProp cover389.active pattern ∨
      activeMatchesProp cover390.active pattern ∨
      activeMatchesProp cover391.active pattern ∨
      activeMatchesProp cover392.active pattern ∨
      activeMatchesProp cover393.active pattern ∨
      activeMatchesProp cover394.active pattern := by
    simp (config := { maxSteps := 10000000 }) only [feasibleProp, relationLeftActiveProp,
      relationRightActiveProp] at feasiblePattern
    simp (config := { maxSteps := 10000000 }) only [activeMatchesProp,
      relationLeftActiveProp, cover0, cover1, cover2, cover3, cover4, cover5, cover6, cover7, cover8, cover9, cover10, cover11, cover12, cover13, cover14, cover15, cover16, cover17, cover18, cover19, cover20, cover21, cover22, cover23, cover24, cover25, cover26, cover27, cover28, cover29, cover30, cover31, cover32, cover33, cover34, cover35, cover36, cover37, cover38, cover39, cover40, cover41, cover42, cover43, cover44, cover45, cover46, cover47, cover48, cover49, cover50, cover51, cover52, cover53, cover54, cover55, cover56, cover57, cover58, cover59, cover60, cover61, cover62, cover63, cover64, cover65, cover66, cover67, cover68, cover69, cover70, cover71, cover72, cover73, cover74, cover75, cover76, cover77, cover78, cover79, cover80, cover81, cover82, cover83, cover84, cover85, cover86, cover87, cover88, cover89, cover90, cover91, cover92, cover93, cover94, cover95, cover96, cover97, cover98, cover99, cover100, cover101, cover102, cover103, cover104, cover105, cover106, cover107, cover108, cover109, cover110, cover111, cover112, cover113, cover114, cover115, cover116, cover117, cover118, cover119, cover120, cover121, cover122, cover123, cover124, cover125, cover126, cover127, cover128, cover129, cover130, cover131, cover132, cover133, cover134, cover135, cover136, cover137, cover138, cover139, cover140, cover141, cover142, cover143, cover144, cover145, cover146, cover147, cover148, cover149, cover150, cover151, cover152, cover153, cover154, cover155, cover156, cover157, cover158, cover159, cover160, cover161, cover162, cover163, cover164, cover165, cover166, cover167, cover168, cover169, cover170, cover171, cover172, cover173, cover174, cover175, cover176, cover177, cover178, cover179, cover180, cover181, cover182, cover183, cover184, cover185, cover186, cover187, cover188, cover189, cover190, cover191, cover192, cover193, cover194, cover195, cover196, cover197, cover198, cover199, cover200, cover201, cover202, cover203, cover204, cover205, cover206, cover207, cover208, cover209, cover210, cover211, cover212, cover213, cover214, cover215, cover216, cover217, cover218, cover219, cover220, cover221, cover222, cover223, cover224, cover225, cover226, cover227, cover228, cover229, cover230, cover231, cover232, cover233, cover234, cover235, cover236, cover237, cover238, cover239, cover240, cover241, cover242, cover243, cover244, cover245, cover246, cover247, cover248, cover249, cover250, cover251, cover252, cover253, cover254, cover255, cover256, cover257, cover258, cover259, cover260, cover261, cover262, cover263, cover264, cover265, cover266, cover267, cover268, cover269, cover270, cover271, cover272, cover273, cover274, cover275, cover276, cover277, cover278, cover279, cover280, cover281, cover282, cover283, cover284, cover285, cover286, cover287, cover288, cover289, cover290, cover291, cover292, cover293, cover294, cover295, cover296, cover297, cover298, cover299, cover300, cover301, cover302, cover303, cover304, cover305, cover306, cover307, cover308, cover309, cover310, cover311, cover312, cover313, cover314, cover315, cover316, cover317, cover318, cover319, cover320, cover321, cover322, cover323, cover324, cover325, cover326, cover327, cover328, cover329, cover330, cover331, cover332, cover333, cover334, cover335, cover336, cover337, cover338, cover339, cover340, cover341, cover342, cover343, cover344, cover345, cover346, cover347, cover348, cover349, cover350, cover351, cover352, cover353, cover354, cover355, cover356, cover357, cover358, cover359, cover360, cover361, cover362, cover363, cover364, cover365, cover366, cover367, cover368, cover369, cover370, cover371, cover372, cover373, cover374, cover375, cover376, cover377, cover378, cover379, cover380, cover381, cover382, cover383, cover384, cover385, cover386, cover387, cover388, cover389, cover390, cover391, cover392, cover393, cover394]
    tauto
  rcases activeDisjunction with active0 | active1 | active2 | active3 | active4 | active5 | active6 | active7 | active8 | active9 | active10 | active11 | active12 | active13 | active14 | active15 | active16 | active17 | active18 | active19 | active20 | active21 | active22 | active23 | active24 | active25 | active26 | active27 | active28 | active29 | active30 | active31 | active32 | active33 | active34 | active35 | active36 | active37 | active38 | active39 | active40 | active41 | active42 | active43 | active44 | active45 | active46 | active47 | active48 | active49 | active50 | active51 | active52 | active53 | active54 | active55 | active56 | active57 | active58 | active59 | active60 | active61 | active62 | active63 | active64 | active65 | active66 | active67 | active68 | active69 | active70 | active71 | active72 | active73 | active74 | active75 | active76 | active77 | active78 | active79 | active80 | active81 | active82 | active83 | active84 | active85 | active86 | active87 | active88 | active89 | active90 | active91 | active92 | active93 | active94 | active95 | active96 | active97 | active98 | active99 | active100 | active101 | active102 | active103 | active104 | active105 | active106 | active107 | active108 | active109 | active110 | active111 | active112 | active113 | active114 | active115 | active116 | active117 | active118 | active119 | active120 | active121 | active122 | active123 | active124 | active125 | active126 | active127 | active128 | active129 | active130 | active131 | active132 | active133 | active134 | active135 | active136 | active137 | active138 | active139 | active140 | active141 | active142 | active143 | active144 | active145 | active146 | active147 | active148 | active149 | active150 | active151 | active152 | active153 | active154 | active155 | active156 | active157 | active158 | active159 | active160 | active161 | active162 | active163 | active164 | active165 | active166 | active167 | active168 | active169 | active170 | active171 | active172 | active173 | active174 | active175 | active176 | active177 | active178 | active179 | active180 | active181 | active182 | active183 | active184 | active185 | active186 | active187 | active188 | active189 | active190 | active191 | active192 | active193 | active194 | active195 | active196 | active197 | active198 | active199 | active200 | active201 | active202 | active203 | active204 | active205 | active206 | active207 | active208 | active209 | active210 | active211 | active212 | active213 | active214 | active215 | active216 | active217 | active218 | active219 | active220 | active221 | active222 | active223 | active224 | active225 | active226 | active227 | active228 | active229 | active230 | active231 | active232 | active233 | active234 | active235 | active236 | active237 | active238 | active239 | active240 | active241 | active242 | active243 | active244 | active245 | active246 | active247 | active248 | active249 | active250 | active251 | active252 | active253 | active254 | active255 | active256 | active257 | active258 | active259 | active260 | active261 | active262 | active263 | active264 | active265 | active266 | active267 | active268 | active269 | active270 | active271 | active272 | active273 | active274 | active275 | active276 | active277 | active278 | active279 | active280 | active281 | active282 | active283 | active284 | active285 | active286 | active287 | active288 | active289 | active290 | active291 | active292 | active293 | active294 | active295 | active296 | active297 | active298 | active299 | active300 | active301 | active302 | active303 | active304 | active305 | active306 | active307 | active308 | active309 | active310 | active311 | active312 | active313 | active314 | active315 | active316 | active317 | active318 | active319 | active320 | active321 | active322 | active323 | active324 | active325 | active326 | active327 | active328 | active329 | active330 | active331 | active332 | active333 | active334 | active335 | active336 | active337 | active338 | active339 | active340 | active341 | active342 | active343 | active344 | active345 | active346 | active347 | active348 | active349 | active350 | active351 | active352 | active353 | active354 | active355 | active356 | active357 | active358 | active359 | active360 | active361 | active362 | active363 | active364 | active365 | active366 | active367 | active368 | active369 | active370 | active371 | active372 | active373 | active374 | active375 | active376 | active377 | active378 | active379 | active380 | active381 | active382 | active383 | active384 | active385 | active386 | active387 | active388 | active389 | active390 | active391 | active392 | active393 | active394
  · exact ⟨certified0, active0⟩
  · exact ⟨certified1, active1⟩
  · exact ⟨certified2, active2⟩
  · exact ⟨certified3, active3⟩
  · exact ⟨certified4, active4⟩
  · exact ⟨certified5, active5⟩
  · exact ⟨certified6, active6⟩
  · exact ⟨certified7, active7⟩
  · exact ⟨certified8, active8⟩
  · exact ⟨certified9, active9⟩
  · exact ⟨certified10, active10⟩
  · exact ⟨certified11, active11⟩
  · exact ⟨certified12, active12⟩
  · exact ⟨certified13, active13⟩
  · exact ⟨certified14, active14⟩
  · exact ⟨certified15, active15⟩
  · exact ⟨certified16, active16⟩
  · exact ⟨certified17, active17⟩
  · exact ⟨certified18, active18⟩
  · exact ⟨certified19, active19⟩
  · exact ⟨certified20, active20⟩
  · exact ⟨certified21, active21⟩
  · exact ⟨certified22, active22⟩
  · exact ⟨certified23, active23⟩
  · exact ⟨certified24, active24⟩
  · exact ⟨certified25, active25⟩
  · exact ⟨certified26, active26⟩
  · exact ⟨certified27, active27⟩
  · exact ⟨certified28, active28⟩
  · exact ⟨certified29, active29⟩
  · exact ⟨certified30, active30⟩
  · exact ⟨certified31, active31⟩
  · exact ⟨certified32, active32⟩
  · exact ⟨certified33, active33⟩
  · exact ⟨certified34, active34⟩
  · exact ⟨certified35, active35⟩
  · exact ⟨certified36, active36⟩
  · exact ⟨certified37, active37⟩
  · exact ⟨certified38, active38⟩
  · exact ⟨certified39, active39⟩
  · exact ⟨certified40, active40⟩
  · exact ⟨certified41, active41⟩
  · exact ⟨certified42, active42⟩
  · exact ⟨certified43, active43⟩
  · exact ⟨certified44, active44⟩
  · exact ⟨certified45, active45⟩
  · exact ⟨certified46, active46⟩
  · exact ⟨certified47, active47⟩
  · exact ⟨certified48, active48⟩
  · exact ⟨certified49, active49⟩
  · exact ⟨certified50, active50⟩
  · exact ⟨certified51, active51⟩
  · exact ⟨certified52, active52⟩
  · exact ⟨certified53, active53⟩
  · exact ⟨certified54, active54⟩
  · exact ⟨certified55, active55⟩
  · exact ⟨certified56, active56⟩
  · exact ⟨certified57, active57⟩
  · exact ⟨certified58, active58⟩
  · exact ⟨certified59, active59⟩
  · exact ⟨certified60, active60⟩
  · exact ⟨certified61, active61⟩
  · exact ⟨certified62, active62⟩
  · exact ⟨certified63, active63⟩
  · exact ⟨certified64, active64⟩
  · exact ⟨certified65, active65⟩
  · exact ⟨certified66, active66⟩
  · exact ⟨certified67, active67⟩
  · exact ⟨certified68, active68⟩
  · exact ⟨certified69, active69⟩
  · exact ⟨certified70, active70⟩
  · exact ⟨certified71, active71⟩
  · exact ⟨certified72, active72⟩
  · exact ⟨certified73, active73⟩
  · exact ⟨certified74, active74⟩
  · exact ⟨certified75, active75⟩
  · exact ⟨certified76, active76⟩
  · exact ⟨certified77, active77⟩
  · exact ⟨certified78, active78⟩
  · exact ⟨certified79, active79⟩
  · exact ⟨certified80, active80⟩
  · exact ⟨certified81, active81⟩
  · exact ⟨certified82, active82⟩
  · exact ⟨certified83, active83⟩
  · exact ⟨certified84, active84⟩
  · exact ⟨certified85, active85⟩
  · exact ⟨certified86, active86⟩
  · exact ⟨certified87, active87⟩
  · exact ⟨certified88, active88⟩
  · exact ⟨certified89, active89⟩
  · exact ⟨certified90, active90⟩
  · exact ⟨certified91, active91⟩
  · exact ⟨certified92, active92⟩
  · exact ⟨certified93, active93⟩
  · exact ⟨certified94, active94⟩
  · exact ⟨certified95, active95⟩
  · exact ⟨certified96, active96⟩
  · exact ⟨certified97, active97⟩
  · exact ⟨certified98, active98⟩
  · exact ⟨certified99, active99⟩
  · exact ⟨certified100, active100⟩
  · exact ⟨certified101, active101⟩
  · exact ⟨certified102, active102⟩
  · exact ⟨certified103, active103⟩
  · exact ⟨certified104, active104⟩
  · exact ⟨certified105, active105⟩
  · exact ⟨certified106, active106⟩
  · exact ⟨certified107, active107⟩
  · exact ⟨certified108, active108⟩
  · exact ⟨certified109, active109⟩
  · exact ⟨certified110, active110⟩
  · exact ⟨certified111, active111⟩
  · exact ⟨certified112, active112⟩
  · exact ⟨certified113, active113⟩
  · exact ⟨certified114, active114⟩
  · exact ⟨certified115, active115⟩
  · exact ⟨certified116, active116⟩
  · exact ⟨certified117, active117⟩
  · exact ⟨certified118, active118⟩
  · exact ⟨certified119, active119⟩
  · exact ⟨certified120, active120⟩
  · exact ⟨certified121, active121⟩
  · exact ⟨certified122, active122⟩
  · exact ⟨certified123, active123⟩
  · exact ⟨certified124, active124⟩
  · exact ⟨certified125, active125⟩
  · exact ⟨certified126, active126⟩
  · exact ⟨certified127, active127⟩
  · exact ⟨certified128, active128⟩
  · exact ⟨certified129, active129⟩
  · exact ⟨certified130, active130⟩
  · exact ⟨certified131, active131⟩
  · exact ⟨certified132, active132⟩
  · exact ⟨certified133, active133⟩
  · exact ⟨certified134, active134⟩
  · exact ⟨certified135, active135⟩
  · exact ⟨certified136, active136⟩
  · exact ⟨certified137, active137⟩
  · exact ⟨certified138, active138⟩
  · exact ⟨certified139, active139⟩
  · exact ⟨certified140, active140⟩
  · exact ⟨certified141, active141⟩
  · exact ⟨certified142, active142⟩
  · exact ⟨certified143, active143⟩
  · exact ⟨certified144, active144⟩
  · exact ⟨certified145, active145⟩
  · exact ⟨certified146, active146⟩
  · exact ⟨certified147, active147⟩
  · exact ⟨certified148, active148⟩
  · exact ⟨certified149, active149⟩
  · exact ⟨certified150, active150⟩
  · exact ⟨certified151, active151⟩
  · exact ⟨certified152, active152⟩
  · exact ⟨certified153, active153⟩
  · exact ⟨certified154, active154⟩
  · exact ⟨certified155, active155⟩
  · exact ⟨certified156, active156⟩
  · exact ⟨certified157, active157⟩
  · exact ⟨certified158, active158⟩
  · exact ⟨certified159, active159⟩
  · exact ⟨certified160, active160⟩
  · exact ⟨certified161, active161⟩
  · exact ⟨certified162, active162⟩
  · exact ⟨certified163, active163⟩
  · exact ⟨certified164, active164⟩
  · exact ⟨certified165, active165⟩
  · exact ⟨certified166, active166⟩
  · exact ⟨certified167, active167⟩
  · exact ⟨certified168, active168⟩
  · exact ⟨certified169, active169⟩
  · exact ⟨certified170, active170⟩
  · exact ⟨certified171, active171⟩
  · exact ⟨certified172, active172⟩
  · exact ⟨certified173, active173⟩
  · exact ⟨certified174, active174⟩
  · exact ⟨certified175, active175⟩
  · exact ⟨certified176, active176⟩
  · exact ⟨certified177, active177⟩
  · exact ⟨certified178, active178⟩
  · exact ⟨certified179, active179⟩
  · exact ⟨certified180, active180⟩
  · exact ⟨certified181, active181⟩
  · exact ⟨certified182, active182⟩
  · exact ⟨certified183, active183⟩
  · exact ⟨certified184, active184⟩
  · exact ⟨certified185, active185⟩
  · exact ⟨certified186, active186⟩
  · exact ⟨certified187, active187⟩
  · exact ⟨certified188, active188⟩
  · exact ⟨certified189, active189⟩
  · exact ⟨certified190, active190⟩
  · exact ⟨certified191, active191⟩
  · exact ⟨certified192, active192⟩
  · exact ⟨certified193, active193⟩
  · exact ⟨certified194, active194⟩
  · exact ⟨certified195, active195⟩
  · exact ⟨certified196, active196⟩
  · exact ⟨certified197, active197⟩
  · exact ⟨certified198, active198⟩
  · exact ⟨certified199, active199⟩
  · exact ⟨certified200, active200⟩
  · exact ⟨certified201, active201⟩
  · exact ⟨certified202, active202⟩
  · exact ⟨certified203, active203⟩
  · exact ⟨certified204, active204⟩
  · exact ⟨certified205, active205⟩
  · exact ⟨certified206, active206⟩
  · exact ⟨certified207, active207⟩
  · exact ⟨certified208, active208⟩
  · exact ⟨certified209, active209⟩
  · exact ⟨certified210, active210⟩
  · exact ⟨certified211, active211⟩
  · exact ⟨certified212, active212⟩
  · exact ⟨certified213, active213⟩
  · exact ⟨certified214, active214⟩
  · exact ⟨certified215, active215⟩
  · exact ⟨certified216, active216⟩
  · exact ⟨certified217, active217⟩
  · exact ⟨certified218, active218⟩
  · exact ⟨certified219, active219⟩
  · exact ⟨certified220, active220⟩
  · exact ⟨certified221, active221⟩
  · exact ⟨certified222, active222⟩
  · exact ⟨certified223, active223⟩
  · exact ⟨certified224, active224⟩
  · exact ⟨certified225, active225⟩
  · exact ⟨certified226, active226⟩
  · exact ⟨certified227, active227⟩
  · exact ⟨certified228, active228⟩
  · exact ⟨certified229, active229⟩
  · exact ⟨certified230, active230⟩
  · exact ⟨certified231, active231⟩
  · exact ⟨certified232, active232⟩
  · exact ⟨certified233, active233⟩
  · exact ⟨certified234, active234⟩
  · exact ⟨certified235, active235⟩
  · exact ⟨certified236, active236⟩
  · exact ⟨certified237, active237⟩
  · exact ⟨certified238, active238⟩
  · exact ⟨certified239, active239⟩
  · exact ⟨certified240, active240⟩
  · exact ⟨certified241, active241⟩
  · exact ⟨certified242, active242⟩
  · exact ⟨certified243, active243⟩
  · exact ⟨certified244, active244⟩
  · exact ⟨certified245, active245⟩
  · exact ⟨certified246, active246⟩
  · exact ⟨certified247, active247⟩
  · exact ⟨certified248, active248⟩
  · exact ⟨certified249, active249⟩
  · exact ⟨certified250, active250⟩
  · exact ⟨certified251, active251⟩
  · exact ⟨certified252, active252⟩
  · exact ⟨certified253, active253⟩
  · exact ⟨certified254, active254⟩
  · exact ⟨certified255, active255⟩
  · exact ⟨certified256, active256⟩
  · exact ⟨certified257, active257⟩
  · exact ⟨certified258, active258⟩
  · exact ⟨certified259, active259⟩
  · exact ⟨certified260, active260⟩
  · exact ⟨certified261, active261⟩
  · exact ⟨certified262, active262⟩
  · exact ⟨certified263, active263⟩
  · exact ⟨certified264, active264⟩
  · exact ⟨certified265, active265⟩
  · exact ⟨certified266, active266⟩
  · exact ⟨certified267, active267⟩
  · exact ⟨certified268, active268⟩
  · exact ⟨certified269, active269⟩
  · exact ⟨certified270, active270⟩
  · exact ⟨certified271, active271⟩
  · exact ⟨certified272, active272⟩
  · exact ⟨certified273, active273⟩
  · exact ⟨certified274, active274⟩
  · exact ⟨certified275, active275⟩
  · exact ⟨certified276, active276⟩
  · exact ⟨certified277, active277⟩
  · exact ⟨certified278, active278⟩
  · exact ⟨certified279, active279⟩
  · exact ⟨certified280, active280⟩
  · exact ⟨certified281, active281⟩
  · exact ⟨certified282, active282⟩
  · exact ⟨certified283, active283⟩
  · exact ⟨certified284, active284⟩
  · exact ⟨certified285, active285⟩
  · exact ⟨certified286, active286⟩
  · exact ⟨certified287, active287⟩
  · exact ⟨certified288, active288⟩
  · exact ⟨certified289, active289⟩
  · exact ⟨certified290, active290⟩
  · exact ⟨certified291, active291⟩
  · exact ⟨certified292, active292⟩
  · exact ⟨certified293, active293⟩
  · exact ⟨certified294, active294⟩
  · exact ⟨certified295, active295⟩
  · exact ⟨certified296, active296⟩
  · exact ⟨certified297, active297⟩
  · exact ⟨certified298, active298⟩
  · exact ⟨certified299, active299⟩
  · exact ⟨certified300, active300⟩
  · exact ⟨certified301, active301⟩
  · exact ⟨certified302, active302⟩
  · exact ⟨certified303, active303⟩
  · exact ⟨certified304, active304⟩
  · exact ⟨certified305, active305⟩
  · exact ⟨certified306, active306⟩
  · exact ⟨certified307, active307⟩
  · exact ⟨certified308, active308⟩
  · exact ⟨certified309, active309⟩
  · exact ⟨certified310, active310⟩
  · exact ⟨certified311, active311⟩
  · exact ⟨certified312, active312⟩
  · exact ⟨certified313, active313⟩
  · exact ⟨certified314, active314⟩
  · exact ⟨certified315, active315⟩
  · exact ⟨certified316, active316⟩
  · exact ⟨certified317, active317⟩
  · exact ⟨certified318, active318⟩
  · exact ⟨certified319, active319⟩
  · exact ⟨certified320, active320⟩
  · exact ⟨certified321, active321⟩
  · exact ⟨certified322, active322⟩
  · exact ⟨certified323, active323⟩
  · exact ⟨certified324, active324⟩
  · exact ⟨certified325, active325⟩
  · exact ⟨certified326, active326⟩
  · exact ⟨certified327, active327⟩
  · exact ⟨certified328, active328⟩
  · exact ⟨certified329, active329⟩
  · exact ⟨certified330, active330⟩
  · exact ⟨certified331, active331⟩
  · exact ⟨certified332, active332⟩
  · exact ⟨certified333, active333⟩
  · exact ⟨certified334, active334⟩
  · exact ⟨certified335, active335⟩
  · exact ⟨certified336, active336⟩
  · exact ⟨certified337, active337⟩
  · exact ⟨certified338, active338⟩
  · exact ⟨certified339, active339⟩
  · exact ⟨certified340, active340⟩
  · exact ⟨certified341, active341⟩
  · exact ⟨certified342, active342⟩
  · exact ⟨certified343, active343⟩
  · exact ⟨certified344, active344⟩
  · exact ⟨certified345, active345⟩
  · exact ⟨certified346, active346⟩
  · exact ⟨certified347, active347⟩
  · exact ⟨certified348, active348⟩
  · exact ⟨certified349, active349⟩
  · exact ⟨certified350, active350⟩
  · exact ⟨certified351, active351⟩
  · exact ⟨certified352, active352⟩
  · exact ⟨certified353, active353⟩
  · exact ⟨certified354, active354⟩
  · exact ⟨certified355, active355⟩
  · exact ⟨certified356, active356⟩
  · exact ⟨certified357, active357⟩
  · exact ⟨certified358, active358⟩
  · exact ⟨certified359, active359⟩
  · exact ⟨certified360, active360⟩
  · exact ⟨certified361, active361⟩
  · exact ⟨certified362, active362⟩
  · exact ⟨certified363, active363⟩
  · exact ⟨certified364, active364⟩
  · exact ⟨certified365, active365⟩
  · exact ⟨certified366, active366⟩
  · exact ⟨certified367, active367⟩
  · exact ⟨certified368, active368⟩
  · exact ⟨certified369, active369⟩
  · exact ⟨certified370, active370⟩
  · exact ⟨certified371, active371⟩
  · exact ⟨certified372, active372⟩
  · exact ⟨certified373, active373⟩
  · exact ⟨certified374, active374⟩
  · exact ⟨certified375, active375⟩
  · exact ⟨certified376, active376⟩
  · exact ⟨certified377, active377⟩
  · exact ⟨certified378, active378⟩
  · exact ⟨certified379, active379⟩
  · exact ⟨certified380, active380⟩
  · exact ⟨certified381, active381⟩
  · exact ⟨certified382, active382⟩
  · exact ⟨certified383, active383⟩
  · exact ⟨certified384, active384⟩
  · exact ⟨certified385, active385⟩
  · exact ⟨certified386, active386⟩
  · exact ⟨certified387, active387⟩
  · exact ⟨certified388, active388⟩
  · exact ⟨certified389, active389⟩
  · exact ⟨certified390, active390⟩
  · exact ⟨certified391, active391⟩
  · exact ⟨certified392, active392⟩
  · exact ⟨certified393, active393⟩
  · exact ⟨certified394, active394⟩

theorem everyFeasiblePatternCovered (pattern : Fin 26 → Prop)
    (feasiblePattern : feasibleProp pattern) :
    ∃ cover, activeMatchesProp cover.active pattern ∧
      ∃ stratum ∈ cover.strata, zeroMatchesProp stratum.zero pattern := by
  obtain ⟨certificate, activePattern⟩ :=
    feasibleHasCertifiedCover pattern feasiblePattern
  exact ⟨certificate.data, activePattern,
    certificate.zeroCovered pattern feasiblePattern activePattern⟩

end Krenn.CollapseSupportCoverData

#print axioms Krenn.CollapseSupportCoverData.everyFeasiblePatternCovered
