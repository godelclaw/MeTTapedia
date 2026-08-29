import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 315 through 378.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk315 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12296, zeroMask := 1187833,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 3283961,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 1449849,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 3545977,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 1712057,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 3808185,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 1974073,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 4070201,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 1196024,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 3292152,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 1720248,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12296, zeroMask := 3816376,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk315_valid :
    List.Forall StratumCertificate.Valid certificateChunk315 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk316 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12297, zeroMask := 1458008,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12297, zeroMask := 3554136,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12297, zeroMask := 1982232,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12297, zeroMask := 4078360,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk316_valid :
    List.Forall StratumCertificate.Valid certificateChunk316 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk317 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12298, zeroMask := 1056760,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12298, zeroMask := 1580984,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 37, .chain 38, .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk317_valid :
    List.Forall StratumCertificate.Valid certificateChunk317 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk318 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12304, zeroMask := 1187815,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11542247,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 3283687,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 1449831,
        component := 49 }
    witnesses := [.killed 9 (some 10), .chain 20, .killed 10 (some 9), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11804263,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 18), .killed 5 (some 12), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 3545703,
        component := 52 }
    witnesses := [.killed 6 (some 18), .chain 20, .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 1457991,
        component := 62 }
    witnesses := [.killed 9 (some 10), .chain 20, .killed 10 (some 9), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11812423,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 6 (some 18), .killed 6 (some 12), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 3553863,
        component := 65 }
    witnesses := [.killed 0 (some 18), .killed 6 (some 18), .killed 6 (some 0), .chain 20, .killed 18 (some 0), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 9445349,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11672549,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 9707365,
        component := 17 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 20, .killed 5 (some 9), .killed 12 (some 9), .killed 10 (some 9), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .chain 3, .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11934565,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 18), .killed 5 (some 12), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 9715525,
        component := 17 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 20, .killed 13 (some 9), .killed 12 (some 9), .killed 10 (some 9), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .chain 3, .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11942725,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 6 (some 18), .killed 6 (some 12), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 1195974,
        component := 61 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 20, .killed 10 (some 9), .killed 10 (some 8), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11550406,
        component := 41 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 3291846,
        component := 66 }
    witnesses := [.chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 9453508,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 23 (some 9), .killed 23 (some 8), .killed 13 (some 9), .killed 13 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12304, zeroMask := 11680708,
        component := 65 }
    witnesses := [.killed 8 (some 23), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk318_valid :
    List.Forall StratumCertificate.Valid certificateChunk318 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk319 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12306, zeroMask := 1056742,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12306, zeroMask := 3153638,
        component := 41 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk319_valid :
    List.Forall StratumCertificate.Valid certificateChunk319 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk320 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12308, zeroMask := 12066469,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12196517,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12328485,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 18), .killed 5 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12458533,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 18), .killed 5 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12336645,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12466693,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 19 (some 18), .killed 13 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12074628,
        component := 20 }
    witnesses := [.killed 10 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12308, zeroMask := 12204676,
        component := 20 }
    witnesses := [.killed 17 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk320_valid :
    List.Forall StratumCertificate.Valid certificateChunk320 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk321 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12312, zeroMask := 1187809,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12312, zeroMask := 3283937,
        component := 52 }
    witnesses := [.killed 6 (some 7), .chain 20, .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12312, zeroMask := 1449825,
        component := 49 }
    witnesses := [.killed 9 (some 10), .chain 20, .killed 10 (some 9), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 12312, zeroMask := 3545953,
        component := 49 }
    witnesses := [.killed 9 (some 21), .chain 20, .killed 21 (some 9), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 12312, zeroMask := 1196000,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12312, zeroMask := 3292128,
        component := 65 }
    witnesses := [.killed 8 (some 5), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk321_valid :
    List.Forall StratumCertificate.Valid certificateChunk321 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk322 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12313, zeroMask := 1457984,
        component := 62 }
    witnesses := [.killed 9 (some 10), .chain 20, .killed 10 (some 9), .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 12313, zeroMask := 3554112,
        component := 62 }
    witnesses := [.killed 9 (some 21), .chain 20, .killed 21 (some 9), .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk322_valid :
    List.Forall StratumCertificate.Valid certificateChunk322 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk323 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12314, zeroMask := 1056736,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk323_valid :
    List.Forall StratumCertificate.Valid certificateChunk323 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk324 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12316, zeroMask := 3807905,
        component := 52 }
    witnesses := [.killed 19 (some 7), .chain 20, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12316, zeroMask := 4069921,
        component := 52 }
    witnesses := [.killed 19 (some 18), .chain 20, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12316, zeroMask := 3816096,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 20, .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk324_valid :
    List.Forall StratumCertificate.Valid certificateChunk324 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk325 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12317, zeroMask := 4078080,
        component := 65 }
    witnesses := [.killed 19 (some 18), .killed 19 (some 18), .chain 62, .chain 20, .killed 18 (some 19), .chain 74, .chain 5, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk325_valid :
    List.Forall StratumCertificate.Valid certificateChunk325 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk326 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12318, zeroMask := 3677856,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 20, .chain 86, .chain 36, .chain 37, .chain 38, .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk326_valid :
    List.Forall StratumCertificate.Valid certificateChunk326 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk327 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12416, zeroMask := 1187647,
        component := 51 }
    witnesses := [.killed 9 (some 10), .chain 8, .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 11542079,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 3283519,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 1195807,
        component := 64 }
    witnesses := [.killed 9 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 11550239,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 3291679,
        component := 65 }
    witnesses := [.killed 0 (some 4), .chain 8, .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 9445181,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 8, .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 11672381,
        component := 51 }
    witnesses := [.killed 9 (some 21), .chain 8, .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 9453341,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 8, .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12416, zeroMask := 11680541,
        component := 64 }
    witnesses := [.killed 9 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk327_valid :
    List.Forall StratumCertificate.Valid certificateChunk327 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk328 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12424, zeroMask := 1187641,
        component := 51 }
    witnesses := [.killed 9 (some 10), .chain 8, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12424, zeroMask := 3283769,
        component := 51 }
    witnesses := [.killed 9 (some 21), .chain 8, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk328_valid :
    List.Forall StratumCertificate.Valid certificateChunk328 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk329 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12425, zeroMask := 1195800,
        component := 64 }
    witnesses := [.killed 9 (some 10), .chain 8, .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12425, zeroMask := 3291928,
        component := 64 }
    witnesses := [.killed 9 (some 21), .chain 8, .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk329_valid :
    List.Forall StratumCertificate.Valid certificateChunk329 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk330 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12436, zeroMask := 11542053,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12436, zeroMask := 11672101,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 8, .killed 5 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12436, zeroMask := 11550213,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12436, zeroMask := 11680261,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk330_valid :
    List.Forall StratumCertificate.Valid certificateChunk330 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk331 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12444, zeroMask := 3283489,
        component := 52 }
    witnesses := [.chain 8, .chain 20, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk331_valid :
    List.Forall StratumCertificate.Valid certificateChunk331 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk332 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12445, zeroMask := 3291648,
        component := 65 }
    witnesses := [.chain 51, .chain 8, .chain 62, .chain 20, .chain 66, .chain 74, .chain 5, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk332_valid :
    List.Forall StratumCertificate.Valid certificateChunk332 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk333 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13312, zeroMask := 12061375,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12323391,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12331551,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12061629,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12323645,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12331805,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12069534,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13312, zeroMask := 12069788,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk333_valid :
    List.Forall StratumCertificate.Valid certificateChunk333 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk334 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13314, zeroMask := 3672766,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk334_valid :
    List.Forall StratumCertificate.Valid certificateChunk334 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk335 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13322, zeroMask := 3673016,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 37, .chain 38, .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk335_valid :
    List.Forall StratumCertificate.Valid certificateChunk335 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk336 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13328, zeroMask := 12061415,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12323431,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 18), .killed 5 (some 18), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12331591,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 6 (some 18), .killed 6 (some 18), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12061669,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12323685,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 18), .killed 5 (some 18), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12331845,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 6 (some 18), .killed 6 (some 18), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12069574,
        component := 20 }
    witnesses := [.chain 7, .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13328, zeroMask := 12069828,
        component := 20 }
    witnesses := [.chain 7, .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk336_valid :
    List.Forall StratumCertificate.Valid certificateChunk336 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk337 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13330, zeroMask := 3672806,
        component := 41 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk337_valid :
    List.Forall StratumCertificate.Valid certificateChunk337 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk338 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13332, zeroMask := 12061349,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13332, zeroMask := 12323365,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13332, zeroMask := 12331525,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13332, zeroMask := 12069508,
        component := 20 }
    witnesses := [.chain 7, .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk338_valid :
    List.Forall StratumCertificate.Valid certificateChunk338 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk339 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13338, zeroMask := 3673056,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 20, .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk339_valid :
    List.Forall StratumCertificate.Valid certificateChunk339 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk340 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13342, zeroMask := 3672736,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 20, .chain 86, .chain 36, .chain 37, .chain 38, .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk340_valid :
    List.Forall StratumCertificate.Valid certificateChunk340 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk341 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13376, zeroMask := 11537119,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13376, zeroMask := 11799135,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13376, zeroMask := 11537373,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13376, zeroMask := 11799389,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk341_valid :
    List.Forall StratumCertificate.Valid certificateChunk341 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk342 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13378, zeroMask := 3148510,
        component := 41 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk342_valid :
    List.Forall StratumCertificate.Valid certificateChunk342 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk343 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13387, zeroMask := 3410776,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 9), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 9 (some 21), .killed 9 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .killed 9 (some 21), .killed 9 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk343_valid :
    List.Forall StratumCertificate.Valid certificateChunk343 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk344 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13392, zeroMask := 11537095,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13392, zeroMask := 11799111,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13392, zeroMask := 11537349,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13392, zeroMask := 11799365,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk344_valid :
    List.Forall StratumCertificate.Valid certificateChunk344 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk345 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13394, zeroMask := 3148486,
        component := 41 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk345_valid :
    List.Forall StratumCertificate.Valid certificateChunk345 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk346 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13403, zeroMask := 3410752,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 8 (some 9), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 9), .killed 6 (some 8), .chain 20, .killed 21 (some 9), .killed 18 (some 8), .killed 21 (some 9), .killed 18 (some 8), .killed 21 (some 9), .killed 18 (some 8), .killed 21 (some 9), .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 9 (some 21), .killed 9 (some 6), .killed 9 (some 21), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .killed 9 (some 21), .killed 9 (some 6), .killed 9 (some 21), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk346_valid :
    List.Forall StratumCertificate.Valid certificateChunk346 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk347 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13504, zeroMask := 11536927,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 13504, zeroMask := 11537181,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk347_valid :
    List.Forall StratumCertificate.Valid certificateChunk347 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk348 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13515, zeroMask := 3148568,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .killed 21 (some 9), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk348_valid :
    List.Forall StratumCertificate.Valid certificateChunk348 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk349 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13524, zeroMask := 11536901,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk349_valid :
    List.Forall StratumCertificate.Valid certificateChunk349 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk350 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13535, zeroMask := 3148288,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 21 (some 9), .chain 51, .chain 53, .chain 55, .chain 57, .chain 8, .chain 9, .chain 59, .killed 21 (some 9), .chain 62, .chain 20, .killed 21 (some 9), .chain 66, .killed 21 (some 9), .chain 68, .killed 21 (some 9), .chain 70, .killed 21 (some 9), .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 86, .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 10, .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk350_valid :
    List.Forall StratumCertificate.Valid certificateChunk350 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk351 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14592, zeroMask := 1446271,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 18), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 1970495,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 18), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 1454431,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 18), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 1978655,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 18), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 9834877,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 18), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 10359101,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 18), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 9843037,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 18), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 10367261,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 18), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 1454558,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 1978782,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 9843164,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14592, zeroMask := 10367388,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk351_valid :
    List.Forall StratumCertificate.Valid certificateChunk351 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk352 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14600, zeroMask := 1446265,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14600, zeroMask := 1970489,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14600, zeroMask := 1454584,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14600, zeroMask := 1978808,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk352_valid :
    List.Forall StratumCertificate.Valid certificateChunk352 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk353 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14601, zeroMask := 1454424,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 14601, zeroMask := 1978648,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk353_valid :
    List.Forall StratumCertificate.Valid certificateChunk353 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk354 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14608, zeroMask := 1446247,
        component := 49 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 14608, zeroMask := 1454407,
        component := 62 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 14608, zeroMask := 9834853,
        component := 49 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 14608, zeroMask := 9843013,
        component := 62 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 14608, zeroMask := 1454534,
        component := 62 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 14608, zeroMask := 9843140,
        component := 62 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk354_valid :
    List.Forall StratumCertificate.Valid certificateChunk354 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk355 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14616, zeroMask := 1446241,
        component := 49 }
    witnesses := [.chain 18, .chain 20, .chain 31, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 14616, zeroMask := 1454560,
        component := 62 }
    witnesses := [.chain 18, .chain 20, .chain 31, .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk355_valid :
    List.Forall StratumCertificate.Valid certificateChunk355 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk356 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14617, zeroMask := 1454400,
        component := 62 }
    witnesses := [.chain 18, .chain 20, .chain 31, .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk356_valid :
    List.Forall StratumCertificate.Valid certificateChunk356 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk357 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15104, zeroMask := 135679,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 1 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 659903,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 1 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 8524285,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 9048509,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 143838,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 668062,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 8532444,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15104, zeroMask := 9056668,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk357_valid :
    List.Forall StratumCertificate.Valid certificateChunk357 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk358 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15112, zeroMask := 135673,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15112, zeroMask := 659897,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15112, zeroMask := 143864,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15112, zeroMask := 668088,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk358_valid :
    List.Forall StratumCertificate.Valid certificateChunk358 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk359 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15152, zeroMask := 135399,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 56, .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 15152, zeroMask := 143558,
        component := 61 }
    witnesses := [.chain 18, .chain 11, .chain 56, .chain 20, .chain 31, .chain 73, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk359_valid :
    List.Forall StratumCertificate.Valid certificateChunk359 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk360 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15156, zeroMask := 9048229,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 56, .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 15156, zeroMask := 9056388,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .chain 56, .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .chain 20, .killed 23 (some 19), .killed 23 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 17), .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk360_valid :
    List.Forall StratumCertificate.Valid certificateChunk360 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk361 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15164, zeroMask := 659617,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 56, .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 17), .killed 19 (some 7), .chain 78, .killed 19 (some 7), .chain 82, .killed 19 (some 7), .chain 45, .chain 86, .chain 36, .chain 37, .killed 0 (some 17), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 15164, zeroMask := 667808,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .chain 56, .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .chain 78, .killed 19 (some 7), .chain 82, .killed 19 (some 7), .chain 45, .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk361_valid :
    List.Forall StratumCertificate.Valid certificateChunk361 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk362 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15232, zeroMask := 135487,
        component := 51 }
    witnesses := [.chain 18, .chain 8, .killed 1 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15232, zeroMask := 143647,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15232, zeroMask := 8524093,
        component := 51 }
    witnesses := [.chain 18, .chain 8, .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 15232, zeroMask := 8532253,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk362_valid :
    List.Forall StratumCertificate.Valid certificateChunk362 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk363 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15240, zeroMask := 135481,
        component := 51 }
    witnesses := [.chain 18, .chain 8, .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk363_valid :
    List.Forall StratumCertificate.Valid certificateChunk363 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk364 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15241, zeroMask := 143640,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .chain 5, .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk364_valid :
    List.Forall StratumCertificate.Valid certificateChunk364 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk365 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15284, zeroMask := 8523813,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 56, .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 17), .killed 12 (some 17), .chain 44, .chain 90, .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 15284, zeroMask := 8531973,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .chain 56, .chain 8, .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .chain 20, .killed 23 (some 0), .killed 23 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 12 (some 17), .chain 44, .chain 90, .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk365_valid :
    List.Forall StratumCertificate.Valid certificateChunk365 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk366 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15292, zeroMask := 135201,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 56, .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 17), .chain 40, .chain 78, .chain 80, .chain 82, .chain 84, .chain 45, .chain 86, .chain 36, .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 12 (some 17), .chain 44, .chain 90, .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk366_valid :
    List.Forall StratumCertificate.Valid certificateChunk366 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk367 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15293, zeroMask := 143360,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .chain 34, .killed 13 (some 12), .killed 17 (some 12), .chain 47, .killed 13 (some 12), .killed 17 (some 12), .chain 18, .chain 11, .chain 51, .killed 13 (some 12), .killed 17 (some 12), .chain 56, .chain 8, .killed 13 (some 12), .chain 58, .chain 60, .chain 62, .chain 20, .chain 64, .chain 66, .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .chain 31, .chain 73, .chain 74, .chain 5, .killed 12 (some 17), .chain 40, .chain 78, .chain 80, .chain 82, .chain 84, .chain 45, .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .chain 44, .chain 90, .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk367_valid :
    List.Forall StratumCertificate.Valid certificateChunk367 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk368 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15616, zeroMask := 10223933,
        component := 10 }
    witnesses := [.killed 19 (some 5), .chain 7, .chain 16, .chain 18, .killed 19 (some 18), .killed 5 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 15616, zeroMask := 10232093,
        component := 10 }
    witnesses := [.killed 19 (some 13), .chain 7, .chain 16, .chain 18, .killed 19 (some 18), .killed 13 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 15616, zeroMask := 10232220,
        component := 13 }
    witnesses := [.chain 7, .chain 16, .chain 18, .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk368_valid :
    List.Forall StratumCertificate.Valid certificateChunk368 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk369 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15618, zeroMask := 1835454,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .killed 1 (some 2), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk369_valid :
    List.Forall StratumCertificate.Valid certificateChunk369 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk370 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15626, zeroMask := 1835448,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .chain 37, .chain 38, .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk370_valid :
    List.Forall StratumCertificate.Valid certificateChunk370 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk371 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15632, zeroMask := 10223973,
        component := 17 }
    witnesses := [.killed 19 (some 5), .chain 7, .chain 16, .chain 18, .chain 20, .killed 5 (some 19), .chain 29, .chain 31, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .chain 3, .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 15632, zeroMask := 10232133,
        component := 17 }
    witnesses := [.killed 19 (some 13), .chain 7, .chain 16, .chain 18, .chain 20, .killed 13 (some 19), .chain 29, .chain 31, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .chain 3, .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 15632, zeroMask := 10232260,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 23), .killed 13 (some 23), .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 23 (some 19), .killed 18 (some 8), .killed 13 (some 19), .killed 13 (some 8), .chain 29, .killed 18 (some 8), .chain 31, .killed 18 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk371_valid :
    List.Forall StratumCertificate.Valid certificateChunk371 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk372 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15634, zeroMask := 1835494,
        component := 26 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 19 (some 5), .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 8), .killed 5 (some 19), .killed 5 (some 8), .chain 29, .killed 18 (some 8), .chain 31, .killed 18 (some 8), .killed 5 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk372_valid :
    List.Forall StratumCertificate.Valid certificateChunk372 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk373 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15642, zeroMask := 1835488,
        component := 26 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 19 (some 5), .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 8), .killed 5 (some 19), .killed 5 (some 8), .chain 29, .killed 18 (some 8), .chain 31, .killed 18 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk373_valid :
    List.Forall StratumCertificate.Valid certificateChunk373 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk374 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15680, zeroMask := 9699677,
        component := 10 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .killed 6 (some 18), .killed 6 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk374_valid :
    List.Forall StratumCertificate.Valid certificateChunk374 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk375 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15682, zeroMask := 1311198,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk375_valid :
    List.Forall StratumCertificate.Valid certificateChunk375 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk376 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15691, zeroMask := 1311064,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .chain 79, .killed 18 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .chain 21, .killed 18 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk376_valid :
    List.Forall StratumCertificate.Valid certificateChunk376 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk377 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15696, zeroMask := 9699653,
        component := 17 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .chain 20, .chain 27, .chain 29, .chain 31, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .chain 3, .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk377_valid :
    List.Forall StratumCertificate.Valid certificateChunk377 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk378 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15698, zeroMask := 1311174,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .chain 65, .killed 18 (some 8), .chain 27, .killed 18 (some 8), .chain 29, .killed 18 (some 8), .chain 31, .killed 18 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk378_valid :
    List.Forall StratumCertificate.Valid certificateChunk378 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
