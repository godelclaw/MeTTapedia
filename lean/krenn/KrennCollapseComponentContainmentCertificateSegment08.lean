import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 141 through 156.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk141 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3620, zeroMask := 59326629,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 19 (some 7), .chain 14, .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3620, zeroMask := 63520929,
        component := 25 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .chain 11, .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3620, zeroMask := 59334788,
        component := 6 }
    witnesses := [.chain 7, .chain 11, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3620, zeroMask := 63529120,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .chain 11, .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk141_valid :
    List.Forall StratumCertificate.Valid certificateChunk141 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk142 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3630, zeroMask := 50938016,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 11, .chain 45, .chain 36, .chain 37, .chain 38, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk142_valid :
    List.Forall StratumCertificate.Valid certificateChunk142 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk143 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3648, zeroMask := 58802645,
        component := 3 }
    witnesses := [.chain 6, .chain 7, .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk143_valid :
    List.Forall StratumCertificate.Valid certificateChunk143 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk144 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3650, zeroMask := 50414038,
        component := 24 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk144_valid :
    List.Forall StratumCertificate.Valid certificateChunk144 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk145 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3680, zeroMask := 58802375,
        component := 24 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 0 (some 23), .killed 0 (some 23), .chain 7, .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk145_valid :
    List.Forall StratumCertificate.Valid certificateChunk145 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk146 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3682, zeroMask := 50413766,
        component := 24 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk146_valid :
    List.Forall StratumCertificate.Valid certificateChunk146 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk147 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3776, zeroMask := 58802461,
        component := 10 }
    witnesses := [.chain 6, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk147_valid :
    List.Forall StratumCertificate.Valid certificateChunk147 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk148 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3779, zeroMask := 54608154,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .killed 14 (some 25), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk148_valid :
    List.Forall StratumCertificate.Valid certificateChunk148 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk149 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3787, zeroMask := 50413848,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .killed 14 (some 25), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk149_valid :
    List.Forall StratumCertificate.Valid certificateChunk149 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk150 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3808, zeroMask := 58802191,
        component := 3 }
    witnesses := [.chain 6, .chain 7, .chain 11, .chain 8, .chain 9, .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk150_valid :
    List.Forall StratumCertificate.Valid certificateChunk150 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk151 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3811, zeroMask := 54607882,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .chain 11, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 25), .killed 14 (some 25), .killed 3 (some 14), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 14), .killed 25 (some 14), .killed 22 (some 3), .killed 22 (some 3), .killed 25 (some 14), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk151_valid :
    List.Forall StratumCertificate.Valid certificateChunk151 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk152 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3812, zeroMask := 58802181,
        component := 3 }
    witnesses := [.chain 6, .chain 7, .chain 11, .chain 8, .chain 9, .chain 13, .chain 14, .chain 15, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk152_valid :
    List.Forall StratumCertificate.Valid certificateChunk152 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk153 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3823, zeroMask := 50413568,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .chain 11, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 25), .killed 14 (some 25), .killed 25 (some 14), .chain 64, .chain 66, .chain 26, .chain 68, .chain 28, .chain 70, .chain 30, .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 14), .killed 25 (some 14), .chain 84, .chain 45, .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 25 (some 14), .killed 25 (some 14), .chain 13, .chain 14, .chain 10, .killed 24 (some 14), .chain 1, .killed 16 (some 25), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk153_valid :
    List.Forall StratumCertificate.Valid certificateChunk153 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk154 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4096, zeroMask := 1286143,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11640575,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3382015,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 1547647,
        component := 51 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 18), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11902079,
        component := 15 }
    witnesses := [.killed 12 (some 5), .killed 21 (some 4), .killed 6 (some 18), .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3643519,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35332031,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 1806271,
        component := 34 }
    witnesses := [.killed 17 (some 0), .killed 1 (some 2), .killed 0 (some 2), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45686463,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12160703,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37427903,
        component := 43 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3902143,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35593535,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 18), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 2067775,
        component := 35 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 19 (some 18), .killed 5 (some 18), .killed 2 (some 0), .killed 2 (some 17), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45947967,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 18), .killed 5 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12422207,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 21 (some 4), .killed 19 (some 18), .killed 5 (some 18), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37689407,
        component := 43 }
    witnesses := [.killed 19 (some 18), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 4163647,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 1555807,
        component := 64 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 18), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11910239,
        component := 15 }
    witnesses := [.killed 12 (some 13), .killed 21 (some 4), .killed 6 (some 18), .killed 6 (some 12), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3651679,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35601695,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 18), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 2075935,
        component := 35 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 19 (some 18), .killed 13 (some 18), .killed 2 (some 0), .killed 2 (some 17), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45956127,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12430367,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 21 (some 4), .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37697567,
        component := 53 }
    witnesses := [.killed 19 (some 18), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 4171807,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 21 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 34807799,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35360759,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45162231,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45715191,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 36903671,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37456631,
        component := 21 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35069303,
        component := 49 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 4), .killed 10 (some 4), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35622263,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 25 (some 4), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45423735,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 18), .killed 5 (some 12), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45976695,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 6 (some 18), .killed 5 (some 18), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37165175,
        component := 43 }
    witnesses := [.killed 6 (some 18), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37718135,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 17), .killed 21 (some 4), .killed 18 (some 17), .killed 21 (some 4), .killed 18 (some 15), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35077463,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 4), .killed 10 (some 4), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35630423,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 25 (some 4), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45431895,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45984855,
        component := 2 }
    witnesses := [.killed 19 (some 13), .killed 10 (some 15), .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37173335,
        component := 53 }
    witnesses := [.killed 6 (some 18), .killed 18 (some 0), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37726295,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 4), .killed 13 (some 17), .killed 21 (some 4), .killed 18 (some 17), .killed 21 (some 4), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 9543677,
        component := 11 }
    witnesses := [.killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11770877,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 9805181,
        component := 16 }
    witnesses := [.killed 12 (some 5), .killed 3 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12032381,
        component := 51 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 18), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43589565,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 10063805,
        component := 11 }
    witnesses := [.killed 19 (some 5), .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45816765,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12291005,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43851069,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 10325309,
        component := 11 }
    witnesses := [.killed 19 (some 5), .killed 19 (some 18), .killed 5 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 46078269,
        component := 51 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 18), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12552509,
        component := 10 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 19 (some 18), .killed 5 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 9813341,
        component := 16 }
    witnesses := [.killed 12 (some 13), .killed 3 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12040541,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 18), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43859229,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 10333469,
        component := 11 }
    witnesses := [.killed 19 (some 13), .killed 19 (some 18), .killed 13 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 46086429,
        component := 64 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 18), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12560669,
        component := 10 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 19 (some 18), .killed 13 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43065333,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43618293,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 4), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45292533,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45845493,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43326837,
        component := 17 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 25 (some 4), .killed 5 (some 4), .killed 12 (some 4), .killed 10 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43879797,
        component := 16 }
    witnesses := [.killed 19 (some 5), .killed 25 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45554037,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 18), .killed 5 (some 12), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 46106997,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 6 (some 18), .killed 5 (some 18), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43334997,
        component := 17 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 25 (some 4), .killed 13 (some 4), .killed 12 (some 4), .killed 10 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43887957,
        component := 16 }
    witnesses := [.killed 19 (some 13), .killed 25 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45562197,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 46115157,
        component := 2 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 6 (some 18), .killed 6 (some 18), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 1294302,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 1555934,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11648734,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3390174,
        component := 66 }
    witnesses := [.killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11910366,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3651806,
        component := 61 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 15), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35340190,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 1814430,
        component := 35 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35601822,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 2076062,
        component := 35 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45694622,
        component := 5 }
    witnesses := [.killed 10 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12168862,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37436062,
        component := 53 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 3910302,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 21 (some 4), .killed 19 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 19), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45956254,
        component := 5 }
    witnesses := [.killed 10 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12430494,
        component := 19 }
    witnesses := [.killed 21 (some 4), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37697694,
        component := 53 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 4171934,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 19 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 19), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 34815958,
        component := 61 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 25 (some 4), .killed 10 (some 4), .killed 10 (some 8), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35368918,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35077590,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 4), .killed 10 (some 4), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 35630550,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45170390,
        component := 21 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45723350,
        component := 5 }
    witnesses := [.killed 10 (some 15), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 36911830,
        component := 55 }
    witnesses := [.killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37464790,
        component := 21 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45432022,
        component := 21 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45984982,
        component := 5 }
    witnesses := [.killed 10 (some 15), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37173462,
        component := 55 }
    witnesses := [.killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 37726422,
        component := 21 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 9551836,
        component := 35 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 6 (some 7), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 11779036,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 9813468,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 3 (some 4), .killed 2 (some 7), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12040668,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43597724,
        component := 13 }
    witnesses := [.killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 0, .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 10071964,
        component := 14 }
    witnesses := [.chain 0, .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45824924,
        component := 5 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12299164,
        component := 20 }
    witnesses := [.killed 17 (some 15), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43859356,
        component := 13 }
    witnesses := [.killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 10333596,
        component := 14 }
    witnesses := [.chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 46086556,
        component := 5 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 12560796,
        component := 13 }
    witnesses := [.killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43073492,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 23 (some 4), .killed 23 (some 8), .killed 13 (some 4), .killed 13 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43626452,
        component := 19 }
    witnesses := [.killed 8 (some 4), .killed 25 (some 4), .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45300692,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45853652,
        component := 5 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43335124,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 23 (some 4), .killed 18 (some 8), .killed 13 (some 4), .killed 13 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 18 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 43888084,
        component := 19 }
    witnesses := [.killed 8 (some 4), .killed 25 (some 4), .killed 18 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 45562324,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 4), .killed 21 (some 4), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4096, zeroMask := 46115284,
        component := 5 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk154_valid :
    List.Forall StratumCertificate.Valid certificateChunk154 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk155 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4098, zeroMask := 1155070,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 1416702,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 3251966,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 3513598,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 35200958,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 1 (some 2), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 1675198,
        component := 34 }
    witnesses := [.chain 32, .killed 1 (some 2), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 35462590,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 1 (some 2), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 1936830,
        component := 34 }
    witnesses := [.chain 32, .killed 1 (some 2), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 37297854,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 3772094,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 37559486,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 4033726,
        component := 33 }
    witnesses := [.chain 32, .killed 21 (some 4), .killed 3 (some 4), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 34676726,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 35229686,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 34938358,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 35491318,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 36773622,
        component := 21 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 37326582,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 37035254,
        component := 21 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4098, zeroMask := 37588214,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk155_valid :
    List.Forall StratumCertificate.Valid certificateChunk155 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk156 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4100, zeroMask := 45686453,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45715125,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45816501,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45845173,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45947957,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 18), .killed 5 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45976629,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 18), .killed 5 (some 18), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 46078005,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 18), .killed 5 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 46106677,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 18), .killed 5 (some 18), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45956117,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45984789,
        component := 2 }
    witnesses := [.killed 19 (some 13), .killed 10 (some 15), .killed 19 (some 18), .killed 13 (some 18), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 46086165,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 19 (some 18), .killed 13 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 46114837,
        component := 2 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 19 (some 18), .killed 13 (some 18), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45694612,
        component := 5 }
    witnesses := [.killed 10 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45723284,
        component := 5 }
    witnesses := [.killed 10 (some 15), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45824660,
        component := 5 }
    witnesses := [.killed 17 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45853332,
        component := 5 }
    witnesses := [.killed 17 (some 15), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45956244,
        component := 5 }
    witnesses := [.killed 10 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 45984916,
        component := 5 }
    witnesses := [.killed 10 (some 15), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 46086292,
        component := 5 }
    witnesses := [.killed 17 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4100, zeroMask := 46114964,
        component := 5 }
    witnesses := [.killed 17 (some 15), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk156_valid :
    List.Forall StratumCertificate.Valid certificateChunk156 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
