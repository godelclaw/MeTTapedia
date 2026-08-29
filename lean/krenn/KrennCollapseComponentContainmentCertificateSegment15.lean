import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 379 through 394.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk379 : List StratumCertificate := [
  { stratum :=
      { activeMask := 15707, zeroMask := 1311040,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 8), .chain 20, .chain 65, .killed 18 (some 8), .chain 27, .killed 18 (some 8), .chain 29, .killed 18 (some 8), .chain 31, .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .chain 79, .killed 18 (some 6), .chain 83, .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .chain 21, .killed 18 (some 6), .chain 12, .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk379_valid :
    List.Forall StratumCertificate.Valid certificateChunk379 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk380 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16128, zeroMask := 8913341,
        component := 10 }
    witnesses := [.killed 19 (some 5), .chain 7, .chain 16, .chain 18, .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 16128, zeroMask := 8921500,
        component := 13 }
    witnesses := [.chain 7, .chain 16, .chain 18, .chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk380_valid :
    List.Forall StratumCertificate.Valid certificateChunk380 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk381 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16130, zeroMask := 524734,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .killed 1 (some 2), .killed 1 (some 2), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk381_valid :
    List.Forall StratumCertificate.Valid certificateChunk381 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk382 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16138, zeroMask := 524728,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .chain 37, .chain 38, .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk382_valid :
    List.Forall StratumCertificate.Valid certificateChunk382 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk383 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16176, zeroMask := 8913127,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 23), .chain 54, .chain 56, .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .chain 29, .chain 71, .chain 31, .chain 73, .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 16176, zeroMask := 8921286,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 23), .killed 13 (some 23), .chain 16, .chain 18, .chain 11, .killed 19 (some 23), .killed 13 (some 23), .chain 54, .chain 56, .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 23 (some 19), .killed 23 (some 19), .killed 13 (some 19), .killed 13 (some 19), .chain 29, .chain 71, .chain 31, .chain 73, .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk383_valid :
    List.Forall StratumCertificate.Valid certificateChunk383 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk384 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16178, zeroMask := 524518,
        component := 26 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 19 (some 5), .chain 48, .chain 16, .chain 18, .chain 11, .killed 19 (some 5), .chain 52, .chain 54, .chain 56, .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .chain 29, .chain 71, .chain 31, .chain 73, .killed 5 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk384_valid :
    List.Forall StratumCertificate.Valid certificateChunk384 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk385 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16180, zeroMask := 8913061,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 5), .killed 0 (some 23), .chain 54, .chain 56, .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .chain 29, .chain 71, .chain 31, .chain 73, .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 7), .chain 88, .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 16180, zeroMask := 8921220,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 23), .killed 13 (some 23), .chain 16, .chain 18, .chain 11, .killed 19 (some 23), .killed 13 (some 23), .chain 54, .chain 56, .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .chain 20, .killed 23 (some 19), .killed 23 (some 19), .killed 13 (some 19), .killed 13 (some 19), .chain 29, .chain 71, .chain 31, .chain 73, .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .chain 88, .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk385_valid :
    List.Forall StratumCertificate.Valid certificateChunk385 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk386 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16190, zeroMask := 524448,
        component := 26 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 19 (some 5), .chain 48, .chain 16, .chain 18, .chain 11, .killed 19 (some 5), .chain 52, .chain 54, .chain 56, .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .chain 29, .chain 71, .chain 31, .chain 73, .killed 5 (some 7), .killed 5 (some 7), .chain 76, .killed 19 (some 7), .chain 78, .killed 19 (some 7), .chain 82, .killed 19 (some 7), .chain 45, .chain 86, .chain 36, .chain 37, .chain 38, .killed 5 (some 7), .chain 88, .killed 19 (some 7), .chain 90, .killed 19 (some 7), .chain 24, .killed 19 (some 7), .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk386_valid :
    List.Forall StratumCertificate.Valid certificateChunk386 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk387 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16192, zeroMask := 8389085,
        component := 10 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .killed 6 (some 7), .killed 6 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk387_valid :
    List.Forall StratumCertificate.Valid certificateChunk387 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk388 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16194, zeroMask := 478,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk388_valid :
    List.Forall StratumCertificate.Valid certificateChunk388 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk389 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16240, zeroMask := 8388807,
        component := 26 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 23), .killed 0 (some 23), .chain 54, .chain 56, .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .chain 20, .killed 23 (some 0), .killed 23 (some 0), .chain 27, .chain 69, .chain 29, .chain 71, .chain 31, .chain 73, .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk389_valid :
    List.Forall StratumCertificate.Valid certificateChunk389 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk390 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16242, zeroMask := 198,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .chain 11, .chain 50, .chain 52, .chain 54, .chain 56, .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .chain 65, .chain 67, .chain 27, .chain 69, .chain 29, .chain 71, .chain 31, .chain 73, .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk390_valid :
    List.Forall StratumCertificate.Valid certificateChunk390 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk391 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16320, zeroMask := 8388893,
        component := 10 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .chain 8, .chain 9, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk391_valid :
    List.Forall StratumCertificate.Valid certificateChunk391 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk392 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16331, zeroMask := 280,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .chain 61, .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .chain 79, .chain 81, .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .chain 21, .chain 23, .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk392_valid :
    List.Forall StratumCertificate.Valid certificateChunk392 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk393 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16372, zeroMask := 8388613,
        component := 26 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 23), .killed 0 (some 23), .chain 54, .chain 56, .chain 8, .chain 9, .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .chain 20, .killed 23 (some 0), .killed 23 (some 0), .chain 27, .chain 69, .chain 29, .chain 71, .chain 31, .chain 73, .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .chain 42, .chain 88, .chain 44, .chain 90, .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk393_valid :
    List.Forall StratumCertificate.Valid certificateChunk393 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk394 : List StratumCertificate := [
  { stratum :=
      { activeMask := 16383, zeroMask := 0,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 47, .chain 49, .chain 17, .chain 19, .chain 11, .chain 51, .chain 53, .chain 55, .chain 57, .chain 8, .chain 9, .chain 59, .chain 60, .chain 62, .chain 20, .chain 64, .chain 66, .chain 26, .chain 68, .chain 28, .chain 70, .chain 30, .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .chain 80, .chain 82, .chain 84, .chain 45, .chain 86, .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .chain 22, .chain 24, .chain 13, .chain 14, .chain 10, .chain 0, .chain 1, .chain 2, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk394_valid :
    List.Forall StratumCertificate.Valid certificateChunk394 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
