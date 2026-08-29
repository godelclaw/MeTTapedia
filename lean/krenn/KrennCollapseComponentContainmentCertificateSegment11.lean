import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 205 through 246.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk205 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4672, zeroMask := 232927,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 10587359,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 2328799,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 33787351,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 44141783,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 35883223,
        component := 21 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 8490461,
        component := 11 }
    witnesses := [.chain 6, .killed 6 (some 7), .killed 6 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 10717661,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 6 (some 7), .killed 6 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 42044885,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 4), .killed 25 (some 7), .killed 25 (some 6), .killed 25 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4672, zeroMask := 44272085,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk205_valid :
    List.Forall StratumCertificate.Valid certificateChunk205 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk206 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4674, zeroMask := 101854,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4674, zeroMask := 2198750,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4674, zeroMask := 33656278,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4674, zeroMask := 35753174,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk206_valid :
    List.Forall StratumCertificate.Valid certificateChunk206 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk207 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4720, zeroMask := 232647,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4720, zeroMask := 8490183,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk207_valid :
    List.Forall StratumCertificate.Valid certificateChunk207 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk208 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4722, zeroMask := 101574,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk208_valid :
    List.Forall StratumCertificate.Valid certificateChunk208 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk209 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4736, zeroMask := 236863,
        component := 51 }
    witnesses := [.killed 15 (some 10), .chain 8, .killed 1 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 33758527,
        component := 51 }
    witnesses := [.killed 25 (some 10), .chain 8, .killed 1 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 10591295,
        component := 15 }
    witnesses := [.killed 12 (some 5), .killed 21 (some 4), .chain 8, .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 44112959,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 2332735,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 35854399,
        component := 43 }
    witnesses := [.chain 8, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 245023,
        component := 64 }
    witnesses := [.killed 15 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 33766687,
        component := 64 }
    witnesses := [.killed 25 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 10599455,
        component := 15 }
    witnesses := [.killed 12 (some 13), .killed 21 (some 4), .chain 8, .killed 13 (some 12), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 44121119,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 2340895,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .killed 13 (some 12), .killed 15 (some 0), .killed 21 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 35862559,
        component := 53 }
    witnesses := [.chain 8, .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 8494397,
        component := 11 }
    witnesses := [.killed 12 (some 5), .chain 8, .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 42016061,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 10721597,
        component := 51 }
    witnesses := [.killed 15 (some 21), .chain 8, .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 44243261,
        component := 51 }
    witnesses := [.killed 25 (some 21), .chain 8, .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 8502557,
        component := 11 }
    witnesses := [.killed 12 (some 13), .chain 8, .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 42024221,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 10729757,
        component := 64 }
    witnesses := [.killed 15 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4736, zeroMask := 44251421,
        component := 64 }
    witnesses := [.killed 25 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk209_valid :
    List.Forall StratumCertificate.Valid certificateChunk209 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk210 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4740, zeroMask := 44112949,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4740, zeroMask := 44242997,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 8, .killed 5 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4740, zeroMask := 44121109,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4740, zeroMask := 44251157,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk210_valid :
    List.Forall StratumCertificate.Valid certificateChunk210 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk211 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4744, zeroMask := 236857,
        component := 51 }
    witnesses := [.killed 15 (some 10), .chain 8, .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4744, zeroMask := 33758521,
        component := 51 }
    witnesses := [.killed 25 (some 10), .chain 8, .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4744, zeroMask := 2332985,
        component := 51 }
    witnesses := [.killed 15 (some 21), .chain 8, .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4744, zeroMask := 35854649,
        component := 51 }
    witnesses := [.killed 25 (some 21), .chain 8, .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk211_valid :
    List.Forall StratumCertificate.Valid certificateChunk211 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk212 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4745, zeroMask := 245016,
        component := 64 }
    witnesses := [.killed 15 (some 10), .chain 8, .chain 5, .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4745, zeroMask := 33766680,
        component := 64 }
    witnesses := [.killed 25 (some 10), .chain 8, .chain 5, .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4745, zeroMask := 2341144,
        component := 64 }
    witnesses := [.killed 15 (some 21), .chain 8, .chain 5, .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4745, zeroMask := 35862808,
        component := 64 }
    witnesses := [.killed 25 (some 21), .chain 8, .chain 5, .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk212_valid :
    List.Forall StratumCertificate.Valid certificateChunk212 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk213 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4748, zeroMask := 35854385,
        component := 43 }
    witnesses := [.chain 8, .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk213_valid :
    List.Forall StratumCertificate.Valid certificateChunk213 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk214 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4749, zeroMask := 35862544,
        component := 53 }
    witnesses := [.chain 8, .chain 66, .chain 74, .chain 5, .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk214_valid :
    List.Forall StratumCertificate.Valid certificateChunk214 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk215 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4788, zeroMask := 8494117,
        component := 15 }
    witnesses := [.killed 12 (some 5), .chain 11, .chain 8, .killed 5 (some 12), .chain 20, .chain 22, .chain 24, .killed 5 (some 12), .chain 13, .chain 14, .killed 5 (some 12), .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4788, zeroMask := 8502277,
        component := 15 }
    witnesses := [.killed 12 (some 13), .chain 11, .chain 8, .killed 13 (some 12), .chain 20, .chain 22, .chain 24, .killed 13 (some 12), .chain 13, .chain 14, .killed 13 (some 12), .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk215_valid :
    List.Forall StratumCertificate.Valid certificateChunk215 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk216 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4796, zeroMask := 236577,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 10 (some 15), .killed 10 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 17), .killed 10 (some 15), .killed 10 (some 15), .chain 80, .chain 82, .chain 84, .chain 45, .chain 86, .chain 36, .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 10 (some 15), .killed 10 (some 15), .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk216_valid :
    List.Forall StratumCertificate.Valid certificateChunk216 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk217 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4797, zeroMask := 244736,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 10 (some 15), .killed 10 (some 12), .killed 10 (some 12), .chain 47, .killed 13 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 11, .chain 51, .killed 13 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 8, .killed 13 (some 12), .killed 15 (some 10), .chain 60, .chain 62, .chain 20, .chain 64, .chain 66, .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 10 (some 15), .killed 10 (some 15), .chain 74, .chain 5, .killed 12 (some 17), .killed 10 (some 15), .killed 10 (some 15), .chain 80, .chain 82, .chain 84, .chain 45, .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 10 (some 15), .killed 10 (some 15), .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk217_valid :
    List.Forall StratumCertificate.Valid certificateChunk217 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk218 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4800, zeroMask := 232735,
        component := 35 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 17), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4800, zeroMask := 10587167,
        component := 15 }
    witnesses := [.chain 6, .killed 21 (some 4), .chain 8, .chain 9, .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4800, zeroMask := 2328607,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 0), .killed 21 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4800, zeroMask := 8490269,
        component := 11 }
    witnesses := [.chain 6, .chain 8, .chain 9, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4800, zeroMask := 10717469,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 8, .chain 9, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk218_valid :
    List.Forall StratumCertificate.Valid certificateChunk218 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk219 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4804, zeroMask := 44141589,
        component := 2 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4804, zeroMask := 44271637,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk219_valid :
    List.Forall StratumCertificate.Valid certificateChunk219 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk220 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4811, zeroMask := 101656,
        component := 35 }
    witnesses := [.chain 32, .chain 6, .chain 8, .chain 9, .chain 5, .chain 75, .chain 37, .chain 38, .chain 41, .chain 87, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk220_valid :
    List.Forall StratumCertificate.Valid certificateChunk220 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk221 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4815, zeroMask := 35752976,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 15 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 10), .killed 21 (some 25), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .chain 66, .killed 21 (some 4), .chain 68, .killed 21 (some 4), .chain 70, .killed 10 (some 4), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk221_valid :
    List.Forall StratumCertificate.Valid certificateChunk221 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk222 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4852, zeroMask := 8489989,
        component := 15 }
    witnesses := [.chain 6, .chain 11, .chain 8, .chain 9, .chain 20, .chain 22, .chain 24, .chain 25, .chain 13, .chain 14, .chain 15, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk222_valid :
    List.Forall StratumCertificate.Valid certificateChunk222 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk223 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4863, zeroMask := 101376,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .chain 47, .chain 49, .chain 17, .killed 15 (some 10), .chain 11, .chain 51, .chain 53, .chain 55, .killed 15 (some 10), .chain 8, .chain 9, .killed 15 (some 10), .chain 60, .chain 62, .chain 20, .chain 64, .chain 66, .chain 26, .chain 68, .chain 28, .chain 70, .killed 10 (some 15), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .chain 80, .chain 82, .chain 84, .chain 45, .chain 86, .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk223_valid :
    List.Forall StratumCertificate.Valid certificateChunk223 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk224 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5120, zeroMask := 45681343,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45942847,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951007,
        component := 2 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45681399,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45942903,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 18), .killed 5 (some 18), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951063,
        component := 2 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45681597,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45943101,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951261,
        component := 2 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45681653,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45943157,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 18), .killed 5 (some 18), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951317,
        component := 2 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45689502,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951134,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45689558,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951190,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45689756,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951388,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45689812,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5120, zeroMask := 45951444,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk224_valid :
    List.Forall StratumCertificate.Valid certificateChunk224 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk225 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5122, zeroMask := 37292734,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5122, zeroMask := 37554366,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5122, zeroMask := 37292790,
        component := 21 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 5122, zeroMask := 37554422,
        component := 21 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk225_valid :
    List.Forall StratumCertificate.Valid certificateChunk225 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk226 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5124, zeroMask := 45681333,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5124, zeroMask := 45942837,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5124, zeroMask := 45950997,
        component := 2 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5124, zeroMask := 45689492,
        component := 5 }
    witnesses := [.chain 7, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5124, zeroMask := 45951124,
        component := 5 }
    witnesses := [.chain 7, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk226_valid :
    List.Forall StratumCertificate.Valid certificateChunk226 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk227 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5130, zeroMask := 37292984,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 3), .chain 37, .chain 38, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5130, zeroMask := 37554616,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 3), .chain 37, .chain 38, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5130, zeroMask := 37293040,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 6), .chain 37, .chain 38, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5130, zeroMask := 37554672,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 6), .chain 37, .chain 38, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk227_valid :
    List.Forall StratumCertificate.Valid certificateChunk227 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk228 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5134, zeroMask := 37292720,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5134, zeroMask := 37554352,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk228_valid :
    List.Forall StratumCertificate.Valid certificateChunk228 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk229 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5184, zeroMask := 45157079,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5184, zeroMask := 45418583,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5184, zeroMask := 45157333,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5184, zeroMask := 45418837,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk229_valid :
    List.Forall StratumCertificate.Valid certificateChunk229 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk230 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5186, zeroMask := 36768470,
        component := 21 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 5186, zeroMask := 37030102,
        component := 21 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk230_valid :
    List.Forall StratumCertificate.Valid certificateChunk230 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk231 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5195, zeroMask := 37030224,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 4 (some 8), .killed 25 (some 4), .killed 21 (some 4), .killed 18 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 25 (some 21), .killed 18 (some 6), .killed 4 (some 21), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .killed 25 (some 21), .killed 18 (some 6), .killed 4 (some 21), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk231_valid :
    List.Forall StratumCertificate.Valid certificateChunk231 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk232 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5312, zeroMask := 45156895,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5312, zeroMask := 45157149,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk232_valid :
    List.Forall StratumCertificate.Valid certificateChunk232 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk233 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5316, zeroMask := 45156885,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk233_valid :
    List.Forall StratumCertificate.Valid certificateChunk233 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk234 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5323, zeroMask := 36768536,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .killed 21 (some 9), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk234_valid :
    List.Forall StratumCertificate.Valid certificateChunk234 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk235 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5327, zeroMask := 36768272,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .chain 9, .chain 59, .killed 21 (some 9), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .chain 66, .killed 21 (some 4), .chain 68, .killed 21 (some 4), .chain 70, .killed 21 (some 4), .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk235_valid :
    List.Forall StratumCertificate.Valid certificateChunk235 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk236 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5632, zeroMask := 44632255,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44632311,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44632509,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44632565,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44640414,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44640470,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44640668,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5632, zeroMask := 44640724,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk236_valid :
    List.Forall StratumCertificate.Valid certificateChunk236 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk237 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5634, zeroMask := 36243646,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5634, zeroMask := 36243702,
        component := 21 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk237_valid :
    List.Forall StratumCertificate.Valid certificateChunk237 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk238 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5636, zeroMask := 44632245,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5636, zeroMask := 44640404,
        component := 5 }
    witnesses := [.chain 7, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk238_valid :
    List.Forall StratumCertificate.Valid certificateChunk238 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk239 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5642, zeroMask := 36243896,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 3), .chain 37, .chain 38, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 5642, zeroMask := 36243952,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 6), .chain 37, .chain 38, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk239_valid :
    List.Forall StratumCertificate.Valid certificateChunk239 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk240 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5646, zeroMask := 36243632,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk240_valid :
    List.Forall StratumCertificate.Valid certificateChunk240 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk241 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5696, zeroMask := 44107991,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5696, zeroMask := 44108245,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk241_valid :
    List.Forall StratumCertificate.Valid certificateChunk241 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk242 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5698, zeroMask := 35719382,
        component := 21 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk242_valid :
    List.Forall StratumCertificate.Valid certificateChunk242 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk243 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5824, zeroMask := 44107807,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 5824, zeroMask := 44108061,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk243_valid :
    List.Forall StratumCertificate.Valid certificateChunk243 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk244 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5828, zeroMask := 44107797,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk244_valid :
    List.Forall StratumCertificate.Valid certificateChunk244 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk245 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5835, zeroMask := 35719448,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .killed 21 (some 25), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk245_valid :
    List.Forall StratumCertificate.Valid certificateChunk245 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk246 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5839, zeroMask := 35719184,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .chain 9, .chain 59, .killed 21 (some 25), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .chain 66, .killed 21 (some 4), .chain 68, .killed 21 (some 4), .chain 70, .killed 21 (some 4), .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk246_valid :
    List.Forall StratumCertificate.Valid certificateChunk246 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
