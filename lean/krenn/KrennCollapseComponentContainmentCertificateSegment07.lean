import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 101 through 140.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk101 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2177, zeroMask := 22278922,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2177, zeroMask := 55800586,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2177, zeroMask := 30667528,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2177, zeroMask := 64189192,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk101_valid :
    List.Forall StratumCertificate.Valid certificateChunk101 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk102 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2184, zeroMask := 18076457,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2184, zeroMask := 51598121,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk102_valid :
    List.Forall StratumCertificate.Valid certificateChunk102 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk103 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2185, zeroMask := 18084616,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2185, zeroMask := 51606280,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk103_valid :
    List.Forall StratumCertificate.Valid certificateChunk103 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk104 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2240, zeroMask := 18072335,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2240, zeroMask := 26460941,
        component := 9 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk104_valid :
    List.Forall StratumCertificate.Valid certificateChunk104 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk105 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2560, zeroMask := 17027583,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 51073471,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 17547711,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 1 (some 2), .killed 0 (some 2), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 50549239,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 51102199,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 21221883,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 55267771,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 21742011,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 1 (some 22), .killed 0 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 54743539,
        component := 45 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2560, zeroMask := 55296499,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 25416189,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 59462077,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 25936317,
        component := 10 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 58937845,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 59490805,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 29610489,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 63656377,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 30130617,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 23 (some 22), .killed 0 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 63132145,
        component := 45 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2560, zeroMask := 63685105,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 17), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 17035742,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 51081630,
        component := 64 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 17555870,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2560, zeroMask := 50557398,
        component := 58 }
    witnesses := [.killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 51110358,
        component := 24 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 21230074,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 55275962,
        component := 64 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 21750202,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 1 (some 22), .killed 1 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 54751730,
        component := 56 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2560, zeroMask := 55304690,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 25424348,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 59470236,
        component := 64 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 25944476,
        component := 13 }
    witnesses := [.killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 58946004,
        component := 56 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 23 (some 4), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2560, zeroMask := 59498964,
        component := 6 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 29618680,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 63664568,
        component := 64 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 30138808,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 23 (some 22), .killed 13 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2560, zeroMask := 63140336,
        component := 56 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2560, zeroMask := 63693296,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk105_valid :
    List.Forall StratumCertificate.Valid certificateChunk105 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk106 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2568, zeroMask := 17027577,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 51073465,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 17547705,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 37, .killed 0 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 50549233,
        component := 45 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2568, zeroMask := 51102193,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 17035768,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 51081656,
        component := 64 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 17555896,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 37, .killed 13 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2568, zeroMask := 50557424,
        component := 56 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2568, zeroMask := 51110384,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk106_valid :
    List.Forall StratumCertificate.Valid certificateChunk106 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk107 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2592, zeroMask := 17027311,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2592, zeroMask := 51073199,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 12), .killed 17 (some 12), .chain 11, .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 17547439,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 11, .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2592, zeroMask := 50548967,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 51101927,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 21221611,
        component := 47 }
    witnesses := [.killed 15 (some 14), .chain 11, .killed 15 (some 14), .killed 6 (some 7), .killed 24 (some 14), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 55267499,
        component := 47 }
    witnesses := [.killed 25 (some 14), .chain 11, .killed 25 (some 14), .killed 19 (some 7), .killed 24 (some 14), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 21741739,
        component := 31 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 11, .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 24 (some 14), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 54743267,
        component := 45 }
    witnesses := [.chain 11, .killed 6 (some 7), .killed 22 (some 7), .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2592, zeroMask := 55296227,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 11, .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 17035470,
        component := 61 }
    witnesses := [.killed 15 (some 14), .chain 11, .killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 3 (some 15), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 51081358,
        component := 56 }
    witnesses := [.chain 11, .killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2592, zeroMask := 17555598,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 11, .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2592, zeroMask := 50557126,
        component := 58 }
    witnesses := [.chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 51110086,
        component := 24 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 21229802,
        component := 59 }
    witnesses := [.killed 15 (some 14), .chain 11, .killed 15 (some 14), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 55275690,
        component := 59 }
    witnesses := [.killed 25 (some 14), .chain 11, .killed 25 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 21749930,
        component := 31 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 11, .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 24 (some 14), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2592, zeroMask := 54751458,
        component := 56 }
    witnesses := [.chain 11, .killed 6 (some 7), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 22 (some 7), .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2592, zeroMask := 55304418,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 11, .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk107_valid :
    List.Forall StratumCertificate.Valid certificateChunk107 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk108 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2596, zeroMask := 59461797,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 19 (some 7), .chain 14, .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 59490469,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 19 (some 7), .chain 14, .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 63656097,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 12), .killed 17 (some 12), .chain 11, .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 63684769,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 11, .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 59469956,
        component := 6 }
    witnesses := [.killed 17 (some 12), .chain 11, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 59498628,
        component := 6 }
    witnesses := [.killed 17 (some 15), .chain 11, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 63664288,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 11, .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2596, zeroMask := 63692960,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 11, .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk108_valid :
    List.Forall StratumCertificate.Valid certificateChunk108 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk109 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2604, zeroMask := 51073185,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 12), .killed 17 (some 12), .chain 11, .chain 45, .chain 36, .chain 37, .killed 0 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2604, zeroMask := 51101857,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 11, .chain 45, .chain 36, .chain 37, .killed 0 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2604, zeroMask := 51081376,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 11, .chain 45, .chain 36, .chain 37, .killed 13 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2604, zeroMask := 51110048,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 11, .chain 45, .chain 36, .chain 37, .killed 13 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk109_valid :
    List.Forall StratumCertificate.Valid certificateChunk109 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk110 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2624, zeroMask := 17023455,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2624, zeroMask := 50577879,
        component := 24 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2624, zeroMask := 25412061,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2624, zeroMask := 58966485,
        component := 3 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk110_valid :
    List.Forall StratumCertificate.Valid certificateChunk110 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk111 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2656, zeroMask := 17023183,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 11, .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2656, zeroMask := 50577607,
        component := 24 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk111_valid :
    List.Forall StratumCertificate.Valid certificateChunk111 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk112 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2688, zeroMask := 17027391,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 50549055,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 17035551,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 50557215,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 21221691,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 54743355,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 25415997,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 58937661,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 25424157,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 58945821,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 29610297,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2688, zeroMask := 63131961,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk112_valid :
    List.Forall StratumCertificate.Valid certificateChunk112 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk113 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2689, zeroMask := 21229850,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2689, zeroMask := 54751514,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2689, zeroMask := 29618456,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2689, zeroMask := 63140120,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk113_valid :
    List.Forall StratumCertificate.Valid certificateChunk113 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk114 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2696, zeroMask := 17027385,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2696, zeroMask := 50549049,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk114_valid :
    List.Forall StratumCertificate.Valid certificateChunk114 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk115 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2697, zeroMask := 17035544,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .chain 5, .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2697, zeroMask := 50557208,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .chain 5, .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk115_valid :
    List.Forall StratumCertificate.Valid certificateChunk115 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk116 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2720, zeroMask := 17027119,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2720, zeroMask := 50548783,
        component := 45 }
    witnesses := [.chain 11, .chain 8, .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2720, zeroMask := 17035279,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .chain 11, .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .chain 8, .killed 13 (some 12), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2720, zeroMask := 50556943,
        component := 56 }
    witnesses := [.chain 11, .chain 8, .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2720, zeroMask := 21221419,
        component := 47 }
    witnesses := [.killed 15 (some 14), .chain 11, .killed 15 (some 14), .chain 8, .killed 24 (some 14), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2720, zeroMask := 54743083,
        component := 47 }
    witnesses := [.killed 25 (some 14), .chain 11, .killed 25 (some 14), .chain 8, .killed 24 (some 14), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk116_valid :
    List.Forall StratumCertificate.Valid certificateChunk116 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk117 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2721, zeroMask := 21229578,
        component := 59 }
    witnesses := [.killed 15 (some 14), .chain 11, .killed 15 (some 14), .chain 8, .chain 5, .killed 24 (some 14), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2721, zeroMask := 54751242,
        component := 59 }
    witnesses := [.killed 25 (some 14), .chain 11, .killed 25 (some 14), .chain 8, .chain 5, .killed 24 (some 14), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk117_valid :
    List.Forall StratumCertificate.Valid certificateChunk117 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk118 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2724, zeroMask := 58937381,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 11, .chain 8, .killed 5 (some 12), .chain 13, .chain 14, .killed 5 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2724, zeroMask := 58945541,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 11, .chain 8, .killed 13 (some 12), .chain 13, .chain 14, .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2724, zeroMask := 63131681,
        component := 45 }
    witnesses := [.chain 11, .chain 8, .killed 22 (some 23), .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .chain 13, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk118_valid :
    List.Forall StratumCertificate.Valid certificateChunk118 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk119 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2725, zeroMask := 63139840,
        component := 56 }
    witnesses := [.chain 11, .chain 8, .killed 23 (some 22), .killed 23 (some 22), .killed 23 (some 22), .chain 5, .killed 22 (some 23), .killed 22 (some 23), .killed 22 (some 23), .killed 23 (some 22), .chain 13, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk119_valid :
    List.Forall StratumCertificate.Valid certificateChunk119 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk120 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2732, zeroMask := 50548769,
        component := 45 }
    witnesses := [.chain 11, .chain 8, .chain 84, .chain 45, .chain 36, .chain 37, .chain 13, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk120_valid :
    List.Forall StratumCertificate.Valid certificateChunk120 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk121 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2733, zeroMask := 50556928,
        component := 56 }
    witnesses := [.chain 11, .chain 8, .chain 64, .chain 66, .chain 74, .chain 5, .chain 84, .chain 45, .chain 36, .chain 37, .chain 13, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk121_valid :
    List.Forall StratumCertificate.Valid certificateChunk121 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk122 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2752, zeroMask := 17023263,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2752, zeroMask := 25411869,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk122_valid :
    List.Forall StratumCertificate.Valid certificateChunk122 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk123 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2784, zeroMask := 17022991,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 11, .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk123_valid :
    List.Forall StratumCertificate.Valid certificateChunk123 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk124 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2788, zeroMask := 58966021,
        component := 3 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 11, .chain 8, .chain 9, .chain 13, .chain 14, .chain 15, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk124_valid :
    List.Forall StratumCertificate.Valid certificateChunk124 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk125 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3072, zeroMask := 60375981,
        component := 9 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60637485,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 5 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60645645,
        component := 3 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 13 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60376037,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60637541,
        component := 4 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60645701,
        component := 4 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64570281,
        component := 39 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 23 (some 22), .killed 0 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64831785,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .chain 4] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64570337,
        component := 25 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64831841,
        component := 23 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 5 (some 0), .killed 19 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 19 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60384140,
        component := 12 }
    witnesses := [.chain 7, .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60645772,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60384196,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 60645828,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64578472,
        component := 39 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 23 (some 22), .killed 13 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64840104,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64578528,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3072, zeroMask := 64840160,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk125_valid :
    List.Forall StratumCertificate.Valid certificateChunk125 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk126 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3073, zeroMask := 64839944,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 14), .killed 13 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 14 (some 18), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .chain 4] },
  { stratum :=
      { activeMask := 3073, zeroMask := 64840000,
        component := 23 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .chain 5, .killed 19 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 19 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk126_valid :
    List.Forall StratumCertificate.Valid certificateChunk126 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk127 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3074, zeroMask := 51987374,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 52249006,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 51987430,
        component := 24 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 52249062,
        component := 24 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 8 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 56181674,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 1 (some 22), .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 56443306,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 56181730,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3074, zeroMask := 56443362,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk127_valid :
    List.Forall StratumCertificate.Valid certificateChunk127 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk128 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3082, zeroMask := 51987368,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3082, zeroMask := 52249000,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .chain 38, .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3082, zeroMask := 51987424,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3082, zeroMask := 52249056,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk128_valid :
    List.Forall StratumCertificate.Valid certificateChunk128 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk129 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3136, zeroMask := 59851717,
        component := 3 }
    witnesses := [.chain 6, .chain 7, .killed 8 (some 9), .killed 6 (some 7), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3136, zeroMask := 60113221,
        component := 4 }
    witnesses := [.chain 6, .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk129_valid :
    List.Forall StratumCertificate.Valid certificateChunk129 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk130 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3138, zeroMask := 51463110,
        component := 24 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 3138, zeroMask := 51724742,
        component := 24 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 8 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk130_valid :
    List.Forall StratumCertificate.Valid certificateChunk130 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk131 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3139, zeroMask := 55918914,
        component := 23 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 5, .chain 39, .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk131_valid :
    List.Forall StratumCertificate.Valid certificateChunk131 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk132 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3147, zeroMask := 51724608,
        component := 23 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 5, .chain 39, .chain 37, .chain 38, .chain 41, .chain 43, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk132_valid :
    List.Forall StratumCertificate.Valid certificateChunk132 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk133 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3264, zeroMask := 59851533,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk133_valid :
    List.Forall StratumCertificate.Valid certificateChunk133 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk134 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3267, zeroMask := 55657226,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk134_valid :
    List.Forall StratumCertificate.Valid certificateChunk134 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk135 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3275, zeroMask := 51462920,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk135_valid :
    List.Forall StratumCertificate.Valid certificateChunk135 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk136 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3584, zeroMask := 59326909,
        component := 10 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 59326965,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 63521209,
        component := 40 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 0 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 23 (some 22), .killed 0 (some 22), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 63521265,
        component := 25 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 59335068,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 4), .killed 4 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 59335124,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 63529400,
        component := 40 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 13 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 23 (some 22), .killed 13 (some 22), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3584, zeroMask := 63529456,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk136_valid :
    List.Forall StratumCertificate.Valid certificateChunk136 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk137 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3586, zeroMask := 50938302,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3586, zeroMask := 50938358,
        component := 24 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 3586, zeroMask := 55132602,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 1 (some 22), .killed 1 (some 22), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3586, zeroMask := 55132658,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk137_valid :
    List.Forall StratumCertificate.Valid certificateChunk137 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk138 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3594, zeroMask := 50938296,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .chain 37, .chain 38, .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 3594, zeroMask := 50938352,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk138_valid :
    List.Forall StratumCertificate.Valid certificateChunk138 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk139 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3616, zeroMask := 59326639,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 59326695,
        component := 24 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 63520939,
        component := 25 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .chain 11, .killed 22 (some 3), .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 63520995,
        component := 25 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .chain 11, .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 59334798,
        component := 6 }
    witnesses := [.chain 7, .chain 11, .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 59334854,
        component := 6 }
    witnesses := [.chain 7, .chain 11, .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 63529130,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .chain 11, .killed 22 (some 3), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3616, zeroMask := 63529186,
        component := 25 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .chain 11, .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk139_valid :
    List.Forall StratumCertificate.Valid certificateChunk139 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk140 : List StratumCertificate := [
  { stratum :=
      { activeMask := 3618, zeroMask := 50938030,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 11, .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3618, zeroMask := 50938086,
        component := 24 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 3618, zeroMask := 55132330,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 11, .killed 22 (some 3), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 3618, zeroMask := 55132386,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 11, .killed 22 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk140_valid :
    List.Forall StratumCertificate.Valid certificateChunk140 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
