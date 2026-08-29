import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 268 through 314.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk268 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10240, zeroMask := 17978351,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 18240367,
        component := 50 }
    witnesses := [.killed 6 (some 18), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 18502575,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 18764591,
        component := 50 }
    witnesses := [.killed 19 (some 18), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 18248527,
        component := 63 }
    witnesses := [.killed 6 (some 18), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 18772751,
        component := 63 }
    witnesses := [.killed 19 (some 18), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 22172651,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 22434667,
        component := 50 }
    witnesses := [.killed 6 (some 18), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 22696875,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 22958891,
        component := 50 }
    witnesses := [.killed 19 (some 18), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 26366957,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 26628973,
        component := 50 }
    witnesses := [.killed 6 (some 18), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 26891181,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 27153197,
        component := 50 }
    witnesses := [.killed 19 (some 18), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 26637133,
        component := 63 }
    witnesses := [.killed 6 (some 18), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 27161357,
        component := 63 }
    witnesses := [.killed 19 (some 18), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 30561257,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 30823273,
        component := 50 }
    witnesses := [.killed 6 (some 18), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 31085481,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 31347497,
        component := 50 }
    witnesses := [.killed 19 (some 18), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 17986510,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 18510734,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 22180842,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 22705066,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 26375116,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 26899340,
        component := 12 }
    witnesses := [.killed 17 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 30569448,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10240, zeroMask := 31093672,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk268_valid :
    List.Forall StratumCertificate.Valid certificateChunk268 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk269 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10241, zeroMask := 22442826,
        component := 63 }
    witnesses := [.killed 6 (some 18), .chain 5, .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10241, zeroMask := 22967050,
        component := 63 }
    witnesses := [.killed 19 (some 18), .chain 5, .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10241, zeroMask := 30831432,
        component := 63 }
    witnesses := [.killed 6 (some 18), .chain 5, .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10241, zeroMask := 31355656,
        component := 63 }
    witnesses := [.killed 19 (some 18), .chain 5, .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk269_valid :
    List.Forall StratumCertificate.Valid certificateChunk269 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk270 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10248, zeroMask := 17978345,
        component := 50 }
    witnesses := [.killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10248, zeroMask := 18240361,
        component := 50 }
    witnesses := [.killed 6 (some 18), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10248, zeroMask := 18502569,
        component := 50 }
    witnesses := [.killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10248, zeroMask := 18764585,
        component := 50 }
    witnesses := [.killed 19 (some 18), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10248, zeroMask := 17986536,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10248, zeroMask := 18510760,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk270_valid :
    List.Forall StratumCertificate.Valid certificateChunk270 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk271 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10249, zeroMask := 18248520,
        component := 63 }
    witnesses := [.killed 6 (some 18), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10249, zeroMask := 18772744,
        component := 63 }
    witnesses := [.killed 19 (some 18), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk271_valid :
    List.Forall StratumCertificate.Valid certificateChunk271 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk272 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10368, zeroMask := 17978159,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10368, zeroMask := 17986319,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10368, zeroMask := 22172459,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10368, zeroMask := 26366765,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10368, zeroMask := 26374925,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10368, zeroMask := 30561065,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk272_valid :
    List.Forall StratumCertificate.Valid certificateChunk272 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk273 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10369, zeroMask := 22180618,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10369, zeroMask := 30569224,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk273_valid :
    List.Forall StratumCertificate.Valid certificateChunk273 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk274 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10376, zeroMask := 17978153,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk274_valid :
    List.Forall StratumCertificate.Valid certificateChunk274 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk275 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10377, zeroMask := 17986312,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk275_valid :
    List.Forall StratumCertificate.Valid certificateChunk275 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk276 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10496, zeroMask := 22425935,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22950159,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22417771,
        component := 47 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22941995,
        component := 47 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 30814541,
        component := 62 }
    witnesses := [.chain 18, .killed 3 (some 22), .killed 3 (some 22), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 31338765,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .killed 8 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 10496, zeroMask := 30806377,
        component := 49 }
    witnesses := [.chain 18, .killed 3 (some 22), .killed 3 (some 22), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 31330601,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 18, .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 17), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22426062,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22950286,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22426090,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 22950314,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 30814668,
        component := 62 }
    witnesses := [.chain 18, .killed 3 (some 22), .killed 3 (some 22), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 31338892,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 10496, zeroMask := 30814696,
        component := 62 }
    witnesses := [.chain 18, .killed 3 (some 22), .killed 3 (some 22), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10496, zeroMask := 31338920,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .chain 18, .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk276_valid :
    List.Forall StratumCertificate.Valid certificateChunk276 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk277 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10497, zeroMask := 22425930,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10497, zeroMask := 22950154,
        component := 59 }
    witnesses := [.chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 10497, zeroMask := 30814536,
        component := 62 }
    witnesses := [.chain 18, .killed 3 (some 22), .killed 3 (some 22), .chain 5, .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10497, zeroMask := 31338760,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 18), .killed 23 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 17), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk277_valid :
    List.Forall StratumCertificate.Valid certificateChunk277 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk278 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11008, zeroMask := 21107195,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 21631419,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 29495801,
        component := 51 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 30020025,
        component := 51 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 21115358,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 21639582,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 21115386,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 21639610,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 29503964,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 30028188,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 29503992,
        component := 64 }
    witnesses := [.chain 18, .killed 6 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11008, zeroMask := 30028216,
        component := 64 }
    witnesses := [.chain 18, .killed 19 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk278_valid :
    List.Forall StratumCertificate.Valid certificateChunk278 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk279 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11040, zeroMask := 21106923,
        component := 47 }
    witnesses := [.chain 18, .chain 11, .chain 56, .killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 11040, zeroMask := 21631147,
        component := 47 }
    witnesses := [.chain 18, .chain 11, .chain 56, .killed 19 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 11040, zeroMask := 21115086,
        component := 59 }
    witnesses := [.chain 18, .chain 11, .chain 56, .killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 11040, zeroMask := 21639310,
        component := 59 }
    witnesses := [.chain 18, .chain 11, .chain 56, .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 11040, zeroMask := 21115114,
        component := 59 }
    witnesses := [.chain 18, .chain 11, .chain 56, .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 11040, zeroMask := 21639338,
        component := 59 }
    witnesses := [.chain 18, .chain 11, .chain 56, .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk279_valid :
    List.Forall StratumCertificate.Valid certificateChunk279 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk280 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11136, zeroMask := 21115167,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11136, zeroMask := 21107003,
        component := 51 }
    witnesses := [.chain 18, .chain 8, .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11136, zeroMask := 29503773,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11136, zeroMask := 29495609,
        component := 51 }
    witnesses := [.chain 18, .chain 8, .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk280_valid :
    List.Forall StratumCertificate.Valid certificateChunk280 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk281 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11137, zeroMask := 21115162,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11137, zeroMask := 29503768,
        component := 64 }
    witnesses := [.chain 18, .chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk281_valid :
    List.Forall StratumCertificate.Valid certificateChunk281 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk282 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11168, zeroMask := 21114895,
        component := 59 }
    witnesses := [.chain 18, .chain 11, .chain 56, .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 11168, zeroMask := 21106731,
        component := 47 }
    witnesses := [.chain 18, .chain 11, .chain 56, .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk282_valid :
    List.Forall StratumCertificate.Valid certificateChunk282 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk283 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11169, zeroMask := 21114890,
        component := 59 }
    witnesses := [.chain 18, .chain 11, .chain 56, .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk283_valid :
    List.Forall StratumCertificate.Valid certificateChunk283 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk284 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11264, zeroMask := 26756013,
        component := 9 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 11264, zeroMask := 27018029,
        component := 9 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 11264, zeroMask := 27026189,
        component := 9 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 11264, zeroMask := 30950313,
        component := 39 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 23 (some 22), .killed 0 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11264, zeroMask := 31212329,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 11264, zeroMask := 26764172,
        component := 12 }
    witnesses := [.chain 7, .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 11264, zeroMask := 30958504,
        component := 39 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 23 (some 22), .killed 13 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk284_valid :
    List.Forall StratumCertificate.Valid certificateChunk284 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk285 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11265, zeroMask := 31220488,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk285_valid :
    List.Forall StratumCertificate.Valid certificateChunk285 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk286 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11266, zeroMask := 18367406,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 11266, zeroMask := 22561706,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 1 (some 22), .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk286_valid :
    List.Forall StratumCertificate.Valid certificateChunk286 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk287 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11274, zeroMask := 18367400,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk287_valid :
    List.Forall StratumCertificate.Valid certificateChunk287 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk288 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11328, zeroMask := 26231757,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 11328, zeroMask := 26493773,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk288_valid :
    List.Forall StratumCertificate.Valid certificateChunk288 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk289 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11330, zeroMask := 17843150,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk289_valid :
    List.Forall StratumCertificate.Valid certificateChunk289 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk290 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11331, zeroMask := 22299466,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 9), .killed 6 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 9 (some 14), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk290_valid :
    List.Forall StratumCertificate.Valid certificateChunk290 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk291 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11339, zeroMask := 18105160,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 9), .killed 6 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 9 (some 14), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .killed 9 (some 14), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk291_valid :
    List.Forall StratumCertificate.Valid certificateChunk291 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk292 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11456, zeroMask := 26231565,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk292_valid :
    List.Forall StratumCertificate.Valid certificateChunk292 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk293 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11459, zeroMask := 22037258,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk293_valid :
    List.Forall StratumCertificate.Valid certificateChunk293 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk294 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11467, zeroMask := 17842952,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk294_valid :
    List.Forall StratumCertificate.Valid certificateChunk294 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk295 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11520, zeroMask := 31203597,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 13), .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .killed 0 (some 23), .chain 16, .chain 18, .killed 8 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 11520, zeroMask := 31195433,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 23), .chain 16, .chain 18, .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 11520, zeroMask := 31203724,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 23), .killed 13 (some 23), .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 11520, zeroMask := 31203752,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 23), .chain 7, .killed 19 (some 5), .killed 13 (some 23), .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk295_valid :
    List.Forall StratumCertificate.Valid certificateChunk295 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk296 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11521, zeroMask := 31203592,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 23), .killed 13 (some 23), .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 23 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk296_valid :
    List.Forall StratumCertificate.Valid certificateChunk296 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk297 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11522, zeroMask := 22806954,
        component := 31 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk297_valid :
    List.Forall StratumCertificate.Valid certificateChunk297 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk298 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11584, zeroMask := 30671181,
        component := 17 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .chain 3, .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk298_valid :
    List.Forall StratumCertificate.Valid certificateChunk298 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk299 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11586, zeroMask := 22282702,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk299_valid :
    List.Forall StratumCertificate.Valid certificateChunk299 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk300 : List StratumCertificate := [
  { stratum :=
      { activeMask := 11587, zeroMask := 22282570,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 8), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .chain 79, .killed 18 (some 6), .killed 22 (some 3), .killed 18 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk300_valid :
    List.Forall StratumCertificate.Valid certificateChunk300 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk301 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12032, zeroMask := 29884857,
        component := 40 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .chain 16, .chain 18, .killed 23 (some 22), .killed 0 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12032, zeroMask := 29893020,
        component := 13 }
    witnesses := [.chain 7, .chain 16, .chain 18, .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12032, zeroMask := 29893048,
        component := 40 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 13 (some 23), .chain 16, .chain 18, .killed 23 (some 22), .killed 13 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk301_valid :
    List.Forall StratumCertificate.Valid certificateChunk301 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk302 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12034, zeroMask := 21496250,
        component := 40 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .killed 1 (some 22), .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk302_valid :
    List.Forall StratumCertificate.Valid certificateChunk302 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk303 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12064, zeroMask := 29884587,
        component := 31 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 23), .chain 54, .chain 56, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12064, zeroMask := 29892750,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 19 (some 23), .killed 13 (some 23), .chain 16, .chain 18, .chain 11, .killed 19 (some 23), .killed 13 (some 23), .chain 54, .chain 56, .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
  { stratum :=
      { activeMask := 12064, zeroMask := 29892778,
        component := 31 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 13 (some 23), .chain 16, .chain 18, .chain 11, .killed 13 (some 23), .chain 54, .chain 56, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk303_valid :
    List.Forall StratumCertificate.Valid certificateChunk303 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk304 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12066, zeroMask := 21495978,
        component := 31 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 48, .chain 16, .chain 18, .chain 11, .chain 52, .chain 54, .chain 56, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .chain 3, .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk304_valid :
    List.Forall StratumCertificate.Valid certificateChunk304 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk305 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12096, zeroMask := 29360605,
        component := 10 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk305_valid :
    List.Forall StratumCertificate.Valid certificateChunk305 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk306 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12098, zeroMask := 20971998,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk306_valid :
    List.Forall StratumCertificate.Valid certificateChunk306 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk307 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12128, zeroMask := 29360335,
        component := 26 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 23), .killed 0 (some 23), .chain 54, .chain 56, .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk307_valid :
    List.Forall StratumCertificate.Valid certificateChunk307 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk308 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12130, zeroMask := 20971726,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .chain 11, .chain 50, .chain 52, .chain 54, .chain 56, .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk308_valid :
    List.Forall StratumCertificate.Valid certificateChunk308 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk309 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12224, zeroMask := 29360413,
        component := 10 }
    witnesses := [.chain 6, .chain 7, .chain 16, .chain 18, .chain 8, .chain 9, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .chain 3, .chain 4, .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk309_valid :
    List.Forall StratumCertificate.Valid certificateChunk309 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk310 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12227, zeroMask := 20971802,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .chain 61, .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .chain 79, .chain 81, .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk310_valid :
    List.Forall StratumCertificate.Valid certificateChunk310 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk311 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12256, zeroMask := 29360143,
        component := 26 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 0 (some 23), .killed 0 (some 23), .chain 7, .killed 0 (some 23), .killed 0 (some 23), .chain 16, .chain 18, .chain 11, .killed 0 (some 23), .killed 0 (some 23), .chain 54, .chain 56, .chain 8, .chain 9, .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk311_valid :
    List.Forall StratumCertificate.Valid certificateChunk311 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk312 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12259, zeroMask := 20971530,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .chain 46, .chain 48, .chain 16, .chain 18, .chain 11, .chain 50, .chain 52, .chain 54, .chain 56, .chain 8, .chain 9, .chain 59, .chain 61, .chain 63, .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .chain 75, .chain 39, .chain 77, .chain 79, .chain 81, .killed 22 (some 3), .killed 22 (some 3), .chain 85, .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .chain 3, .chain 4] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk312_valid :
    List.Forall StratumCertificate.Valid certificateChunk312 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk313 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12288, zeroMask := 1187839,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 7), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11542271,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 3283711,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1449855,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 18), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11804287,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 18), .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 3545727,
        component := 52 }
    witnesses := [.killed 6 (some 18), .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1712063,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12066495,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 3807935,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1974079,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 18), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12328511,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 18), .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 4069951,
        component := 52 }
    witnesses := [.killed 19 (some 18), .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1458015,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 18), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11812447,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 3553887,
        component := 65 }
    witnesses := [.killed 0 (some 4), .killed 6 (some 18), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1982239,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 18), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12336671,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 4078111,
        component := 65 }
    witnesses := [.killed 0 (some 4), .killed 19 (some 18), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 9445373,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 6 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11672573,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 9707389,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 6 (some 18), .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11934589,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 18), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 9969597,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12196797,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 10231613,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 19 (some 18), .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12458813,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 18), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 9715549,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 6 (some 18), .killed 6 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11942749,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 18), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 10239773,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 19 (some 18), .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12466973,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 18), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1195998,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11550430,
        component := 41 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 3291870,
        component := 66 }
    witnesses := [.killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 1720222,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12074654,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 3816094,
        component := 65 }
    witnesses := [.killed 19 (some 4), .killed 19 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 9453532,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 11680732,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 9977756,
        component := 13 }
    witnesses := [.killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 0, .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 12288, zeroMask := 12204956,
        component := 20 }
    witnesses := [.killed 17 (some 12), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk313_valid :
    List.Forall StratumCertificate.Valid certificateChunk313 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk314 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12290, zeroMask := 1056766,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 12290, zeroMask := 3153662,
        component := 41 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 12290, zeroMask := 1580990,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 1 (some 2), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 12290, zeroMask := 3677886,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk314_valid :
    List.Forall StratumCertificate.Valid certificateChunk314 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
