import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 52 through 78.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk052 : List StratumCertificate := [
  { stratum :=
      { activeMask := 672, zeroMask := 17030191,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 672, zeroMask := 25287727,
        component := 15 }
    witnesses := [.killed 12 (some 5), .chain 11, .chain 8, .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 50551855,
        component := 45 }
    witnesses := [.chain 11, .chain 8, .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 672, zeroMask := 58809391,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 11, .chain 8, .killed 5 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 17038351,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 11, .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 10), .chain 8, .killed 13 (some 12), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 672, zeroMask := 25295887,
        component := 15 }
    witnesses := [.killed 12 (some 13), .chain 11, .chain 8, .killed 13 (some 12), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 50560015,
        component := 56 }
    witnesses := [.chain 11, .chain 8, .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 672, zeroMask := 58817551,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 11, .chain 8, .killed 13 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 21216271,
        component := 59 }
    witnesses := [.killed 15 (some 10), .chain 11, .killed 15 (some 10), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 29473807,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .chain 11, .chain 8, .killed 13 (some 12), .killed 2 (some 0), .killed 2 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 54737935,
        component := 59 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 62995471,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 23), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 672, zeroMask := 21208107,
        component := 47 }
    witnesses := [.killed 15 (some 10), .chain 11, .killed 15 (some 10), .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 29465643,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .chain 11, .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 12 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 54729771,
        component := 47 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 672, zeroMask := 62987307,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 23), .killed 25 (some 23), .killed 22 (some 3), .killed 22 (some 3), .killed 25 (some 23), .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk052_valid :
    List.Forall StratumCertificate.Valid certificateChunk052 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk053 : List StratumCertificate := [
  { stratum :=
      { activeMask := 673, zeroMask := 21216266,
        component := 59 }
    witnesses := [.killed 15 (some 10), .chain 11, .killed 15 (some 10), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 673, zeroMask := 29473802,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .chain 11, .chain 8, .killed 13 (some 12), .chain 5, .killed 12 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 673, zeroMask := 54737930,
        component := 59 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 673, zeroMask := 62995466,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 25), .killed 23 (some 25), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 23), .killed 25 (some 23), .killed 22 (some 3), .killed 22 (some 3), .killed 25 (some 23), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk053_valid :
    List.Forall StratumCertificate.Valid certificateChunk053 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk054 : List StratumCertificate := [
  { stratum :=
      { activeMask := 676, zeroMask := 58809381,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 11, .chain 8, .killed 5 (some 12), .chain 13, .chain 14, .killed 5 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 676, zeroMask := 58817541,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 11, .chain 8, .killed 13 (some 12), .chain 13, .chain 14, .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 676, zeroMask := 62995461,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 23), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 25 (some 22), .killed 23 (some 0), .killed 23 (some 0), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 22), .killed 25 (some 22), .chain 13, .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 676, zeroMask := 62987297,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 22 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 22), .killed 25 (some 22), .chain 13, .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk054_valid :
    List.Forall StratumCertificate.Valid certificateChunk054 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk055 : List StratumCertificate := [
  { stratum :=
      { activeMask := 677, zeroMask := 62995456,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 25), .killed 23 (some 25), .killed 25 (some 22), .killed 23 (some 22), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 23 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 22 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 22), .killed 25 (some 22), .chain 13, .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk055_valid :
    List.Forall StratumCertificate.Valid certificateChunk055 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk056 : List StratumCertificate := [
  { stratum :=
      { activeMask := 684, zeroMask := 50551841,
        component := 45 }
    witnesses := [.chain 11, .chain 8, .chain 84, .chain 45, .chain 36, .chain 37, .chain 13, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk056_valid :
    List.Forall StratumCertificate.Valid certificateChunk056 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk057 : List StratumCertificate := [
  { stratum :=
      { activeMask := 685, zeroMask := 50560000,
        component := 56 }
    witnesses := [.chain 11, .chain 8, .chain 64, .chain 66, .chain 74, .chain 5, .chain 84, .chain 45, .chain 36, .chain 37, .chain 13, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk057_valid :
    List.Forall StratumCertificate.Valid certificateChunk057 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk058 : List StratumCertificate := [
  { stratum :=
      { activeMask := 704, zeroMask := 17026335,
        component := 35 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 17), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 21204255,
        component := 36 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 27380767,
        component := 15 }
    witnesses := [.chain 6, .killed 21 (some 4), .chain 8, .chain 9, .killed 3 (some 4), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 31558687,
        component := 36 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 19122207,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 704, zeroMask := 23300127,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 0), .killed 21 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 704, zeroMask := 25283869,
        component := 11 }
    witnesses := [.chain 6, .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 29461789,
        component := 11 }
    witnesses := [.chain 6, .chain 8, .chain 9, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 27511069,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 704, zeroMask := 31688989,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 8, .chain 9, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk058_valid :
    List.Forall StratumCertificate.Valid certificateChunk058 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk059 : List StratumCertificate := [
  { stratum :=
      { activeMask := 707, zeroMask := 21073178,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .chain 8, .chain 9, .chain 5, .chain 75, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 707, zeroMask := 23170074,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .chain 8, .chain 9, .chain 5, .chain 75, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk059_valid :
    List.Forall StratumCertificate.Valid certificateChunk059 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk060 : List StratumCertificate := [
  { stratum :=
      { activeMask := 708, zeroMask := 60935189,
        component := 2 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 708, zeroMask := 65113109,
        component := 2 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 708, zeroMask := 61065237,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 708, zeroMask := 65243157,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk060_valid :
    List.Forall StratumCertificate.Valid certificateChunk060 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk061 : List StratumCertificate := [
  { stratum :=
      { activeMask := 715, zeroMask := 16895256,
        component := 35 }
    witnesses := [.chain 32, .chain 6, .chain 8, .chain 9, .chain 5, .chain 75, .chain 37, .chain 38, .chain 41, .chain 87, .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk061_valid :
    List.Forall StratumCertificate.Valid certificateChunk061 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk062 : List StratumCertificate := [
  { stratum :=
      { activeMask := 719, zeroMask := 52546576,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 15 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 10), .killed 14 (some 25), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .chain 66, .killed 21 (some 4), .chain 68, .killed 21 (some 4), .chain 70, .killed 10 (some 4), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk062_valid :
    List.Forall StratumCertificate.Valid certificateChunk062 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk063 : List StratumCertificate := [
  { stratum :=
      { activeMask := 736, zeroMask := 17026063,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 10), .chain 11, .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 10), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 736, zeroMask := 25283599,
        component := 15 }
    witnesses := [.chain 6, .chain 11, .chain 8, .chain 9, .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 736, zeroMask := 21203983,
        component := 36 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 11, .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 736, zeroMask := 29461519,
        component := 36 }
    witnesses := [.killed 23 (some 0), .chain 6, .chain 11, .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk063_valid :
    List.Forall StratumCertificate.Valid certificateChunk063 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk064 : List StratumCertificate := [
  { stratum :=
      { activeMask := 739, zeroMask := 21072906,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .chain 11, .chain 8, .chain 9, .chain 5, .chain 75, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk064_valid :
    List.Forall StratumCertificate.Valid certificateChunk064 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk065 : List StratumCertificate := [
  { stratum :=
      { activeMask := 740, zeroMask := 58838021,
        component := 3 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 11, .chain 8, .chain 9, .chain 13, .chain 14, .chain 15, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 740, zeroMask := 63015941,
        component := 15 }
    witnesses := [.chain 6, .chain 11, .chain 8, .chain 9, .killed 25 (some 22), .killed 25 (some 22), .killed 25 (some 22), .killed 25 (some 22), .chain 13, .chain 14, .chain 15, .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk065_valid :
    List.Forall StratumCertificate.Valid certificateChunk065 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk066 : List StratumCertificate := [
  { stratum :=
      { activeMask := 751, zeroMask := 50449408,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 15 (some 10), .chain 11, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 15 (some 10), .chain 8, .chain 9, .killed 15 (some 10), .killed 14 (some 25), .killed 14 (some 25), .killed 25 (some 14), .chain 64, .chain 66, .chain 26, .chain 68, .chain 28, .chain 70, .killed 10 (some 15), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .chain 84, .chain 45, .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .chain 13, .chain 14, .chain 10, .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk066_valid :
    List.Forall StratumCertificate.Valid certificateChunk066 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk067 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1024, zeroMask := 62474927,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62736431,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744591,
        component := 3 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922511,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 13), .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 21), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62474983,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 1 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62736487,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744647,
        component := 3 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922567,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 13), .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 21), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 23), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66652843,
        component := 30 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66914347,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 25 (some 23), .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66652899,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66914403,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 19 (some 23), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62475181,
        component := 9 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62736685,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 5 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744845,
        component := 3 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 13 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922765,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 13), .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 21), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62475237,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62736741,
        component := 4 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744901,
        component := 4 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922821,
        component := 17 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 22), .killed 13 (some 19), .killed 21 (some 22), .killed 21 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66653097,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66914601,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66653153,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 25 (some 22), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66914657,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 19 (some 23), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 6), .killed 19 (some 22), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62483086,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661006,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744718,
        component := 6 }
    witnesses := [.chain 7, .killed 21 (some 18), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922638,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62483142,
        component := 20 }
    witnesses := [.chain 7, .killed 25 (some 14), .killed 1 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661062,
        component := 20 }
    witnesses := [.chain 7, .killed 25 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744774,
        component := 6 }
    witnesses := [.chain 7, .killed 21 (some 18), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922694,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661034,
        component := 30 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922666,
        component := 31 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661090,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922722,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 23), .chain 7, .killed 19 (some 5), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62483340,
        component := 12 }
    witnesses := [.chain 7, .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661260,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62744972,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922892,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62483396,
        component := 20 }
    witnesses := [.chain 7, .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661316,
        component := 20 }
    witnesses := [.chain 7, .killed 25 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 62745028,
        component := 6 }
    witnesses := [.chain 7, .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922948,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 8), .killed 13 (some 19), .killed 13 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661288,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922920,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 23), .chain 7, .killed 19 (some 5), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66661344,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 25 (some 22), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1024, zeroMask := 66922976,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 23), .chain 7, .killed 19 (some 5), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 8), .killed 5 (some 19), .killed 5 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk067_valid :
    List.Forall StratumCertificate.Valid certificateChunk067 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk068 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1025, zeroMask := 66922506,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 21 (some 18), .killed 23 (some 25), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 25 (some 23), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1025, zeroMask := 66922562,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 6 (some 22), .chain 5, .killed 18 (some 6), .killed 19 (some 23), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1025, zeroMask := 66922760,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 21 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1025, zeroMask := 66922816,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 8), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 8), .killed 13 (some 19), .killed 13 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 21 (some 22), .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .killed 19 (some 23), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 6), .killed 19 (some 22), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk068_valid :
    List.Forall StratumCertificate.Valid certificateChunk068 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk069 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1026, zeroMask := 54086318,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 54347950,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 21 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 54086374,
        component := 24 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 54348006,
        component := 24 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 21 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 58264234,
        component := 30 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 58525866,
        component := 31 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 58264290,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1026, zeroMask := 58525922,
        component := 26 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 19 (some 5), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk069_valid :
    List.Forall StratumCertificate.Valid certificateChunk069 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk070 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1028, zeroMask := 62474917,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 62736421,
        component := 3 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 62744581,
        component := 3 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66922501,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 13), .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 21), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66652833,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66914337,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 62483076,
        component := 20 }
    witnesses := [.chain 7, .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66660996,
        component := 20 }
    witnesses := [.chain 7, .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 62744708,
        component := 6 }
    witnesses := [.chain 7, .killed 21 (some 18), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66922628,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66661024,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1028, zeroMask := 66922656,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 23), .chain 7, .killed 19 (some 5), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk070_valid :
    List.Forall StratumCertificate.Valid certificateChunk070 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk071 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1029, zeroMask := 66922496,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 21 (some 18), .killed 23 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 23 (some 22), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk071_valid :
    List.Forall StratumCertificate.Valid certificateChunk071 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk072 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1034, zeroMask := 54086568,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 1034, zeroMask := 54348200,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .chain 38, .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1034, zeroMask := 54086624,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 14), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 8 (some 6), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1034, zeroMask := 54348256,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk072_valid :
    List.Forall StratumCertificate.Valid certificateChunk072 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk073 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1038, zeroMask := 54086304,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1038, zeroMask := 54347936,
        component := 25 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 21 (some 18), .killed 18 (some 21), .chain 36, .chain 37, .chain 38, .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk073_valid :
    List.Forall StratumCertificate.Valid certificateChunk073 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk074 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1088, zeroMask := 61950663,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 14), .killed 1 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 66128583,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 62212167,
        component := 3 }
    witnesses := [.chain 6, .chain 7, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 66390087,
        component := 26 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 21), .killed 0 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 23), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 61950917,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 66128837,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 62212421,
        component := 4 }
    witnesses := [.chain 6, .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1088, zeroMask := 66390341,
        component := 17 }
    witnesses := [.chain 6, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 22), .killed 21 (some 22), .killed 21 (some 22), .killed 21 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk074_valid :
    List.Forall StratumCertificate.Valid certificateChunk074 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk075 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1090, zeroMask := 53562054,
        component := 24 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1090, zeroMask := 57739974,
        component := 41 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1090, zeroMask := 53823686,
        component := 24 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 21 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1090, zeroMask := 58001606,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk075_valid :
    List.Forall StratumCertificate.Valid certificateChunk075 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk076 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1091, zeroMask := 58001474,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 25), .killed 25 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 6 (some 22), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 25 (some 21), .killed 18 (some 6), .killed 22 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk076_valid :
    List.Forall StratumCertificate.Valid certificateChunk076 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk077 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1099, zeroMask := 53823808,
        component := 23 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 5, .chain 39, .chain 37, .chain 38, .chain 41, .chain 43, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk077_valid :
    List.Forall StratumCertificate.Valid certificateChunk077 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk078 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1216, zeroMask := 61950479,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1216, zeroMask := 66128399,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1216, zeroMask := 61950733,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1216, zeroMask := 66128653,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk078_valid :
    List.Forall StratumCertificate.Valid certificateChunk078 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
