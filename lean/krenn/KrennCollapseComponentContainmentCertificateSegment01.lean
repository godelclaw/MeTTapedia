import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 1 through 5.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk001 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1, zeroMask := 22527306,
        component := 59 }
    witnesses := [.killed 15 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 6 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 32881738,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 12), .chain 5, .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 24623178,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 18), .killed 15 (some 18), .killed 6 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 56573194,
        component := 59 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 19 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 23047434,
        component := 36 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .chain 5, .killed 18 (some 17), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 66927626,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 10), .killed 21 (some 18), .killed 23 (some 25), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 25 (some 23), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 1, zeroMask := 33401866,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .chain 5, .killed 18 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 58669066,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 19 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 25143306,
        component := 28 }
    witnesses := [.chain 5, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 56048962,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 22), .killed 10 (some 22), .chain 5, .killed 1 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 56601922,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 25 (some 22), .chain 5, .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 17), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 66403394,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 25 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 10), .killed 6 (some 18), .killed 6 (some 25), .killed 25 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 6 (some 22), .chain 5, .killed 12 (some 6), .killed 10 (some 23), .killed 10 (some 6), .killed 25 (some 21), .killed 18 (some 6), .killed 22 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 1, zeroMask := 66956354,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 15 (some 10), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 15 (some 10), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 10), .killed 6 (some 18), .killed 6 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 6 (some 22), .chain 5, .killed 18 (some 6), .killed 10 (some 15), .killed 10 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 1, zeroMask := 58144834,
        component := 54 }
    witnesses := [.chain 5, .killed 25 (none), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 6 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 58697794,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 22), .chain 5, .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1, zeroMask := 30784840,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 3 (some 22), .chain 5, .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 33012040,
        component := 62 }
    witnesses := [.killed 15 (some 21), .killed 3 (some 22), .killed 3 (some 15), .chain 5, .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 64830728,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 1, zeroMask := 31304968,
        component := 8 }
    witnesses := [.chain 5, .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 67057928,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 18), .killed 21 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 17), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1, zeroMask := 33532168,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 21 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 1, zeroMask := 64306496,
        component := 1 }
    witnesses := [.chain 5, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 64859456,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 25 (some 22), .chain 5, .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 66533696,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 22), .killed 21 (some 22), .chain 5, .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 1, zeroMask := 67086656,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 8), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 8), .killed 13 (some 17), .killed 13 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk001_valid :
    List.Forall StratumCertificate.Valid certificateChunk001 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk002 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2, zeroMask := 17948654,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 18210286,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 18), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 20045550,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 20307182,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 18), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 51994542,
        component := 39 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 18468782,
        component := 39 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 52256174,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 8 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 18730414,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 18), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 54091438,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 20565678,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 54353070,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 21 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 20827310,
        component := 33 }
    witnesses := [.chain 32, .killed 21 (some 18), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 51470310,
        component := 24 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 52023270,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 51731942,
        component := 24 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 8 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 52284902,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 18), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 53567206,
        component := 24 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 54120166,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 53828838,
        component := 24 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 21 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 54381798,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 18), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 22126570,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 22388202,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 24223466,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 24485098,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 56172458,
        component := 31 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 22646698,
        component := 32 }
    witnesses := [.chain 32, .killed 8 (some 9), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 56434090,
        component := 31 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 22908330,
        component := 32 }
    witnesses := [.chain 32, .killed 8 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 58269354,
        component := 30 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 24743594,
        component := 32 }
    witnesses := [.chain 32, .killed 21 (some 9), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 58530986,
        component := 31 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 25005226,
        component := 32 }
    witnesses := [.chain 32, .killed 21 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 55648226,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 2, zeroMask := 56201186,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 9), .killed 25 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 55909858,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 8), .killed 5 (some 22), .killed 5 (some 8), .killed 12 (some 22), .killed 12 (some 8), .killed 10 (some 22), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 18 (some 6), .killed 22 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 2, zeroMask := 56462818,
        component := 37 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 25 (some 22), .killed 5 (some 7), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 57745122,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 21 (some 9), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 9), .killed 5 (some 22), .killed 5 (some 9), .killed 5 (some 22), .killed 12 (some 9), .killed 12 (some 22), .killed 10 (some 9), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 2, zeroMask := 58298082,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 2, zeroMask := 58006754,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 18 (some 6), .killed 22 (some 7), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 2, zeroMask := 58559714,
        component := 33 }
    witnesses := [.chain 32, .killed 21 (some 18), .killed 25 (some 22), .killed 18 (some 6), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk002_valid :
    List.Forall StratumCertificate.Valid certificateChunk002 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk003 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4, zeroMask := 62480037,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62508709,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62610085,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62638757,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62741541,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62770213,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62871589,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62900261,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62749701,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66927621,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 19), .killed 13 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62778373,
        component := 3 }
    witnesses := [.killed 19 (some 13), .killed 10 (some 15), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66956293,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62879749,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67057669,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 22), .killed 18 (some 22), .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62908421,
        component := 3 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67086341,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66657953,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66686625,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66788001,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .chain 10, .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66816673,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 17), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66919457,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66948129,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 15 (some 10), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 25 (some 18), .killed 15 (some 10), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67049505,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 17), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67078177,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62488196,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66666116,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62516868,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66694788,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62618244,
        component := 20 }
    witnesses := [.killed 17 (some 12), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66796164,
        component := 20 }
    witnesses := [.killed 17 (some 12), .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62646916,
        component := 20 }
    witnesses := [.killed 17 (some 15), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66824836,
        component := 20 }
    witnesses := [.killed 17 (some 15), .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62749828,
        component := 6 }
    witnesses := [.killed 10 (some 12), .killed 21 (some 18), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66927748,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62778500,
        component := 6 }
    witnesses := [.killed 10 (some 15), .killed 21 (some 18), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66956420,
        component := 19 }
    witnesses := [.killed 21 (some 18), .killed 25 (some 22), .killed 18 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62879876,
        component := 6 }
    witnesses := [.killed 17 (some 12), .killed 21 (some 18), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67057796,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 22), .killed 18 (some 22), .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 62908548,
        component := 6 }
    witnesses := [.killed 17 (some 15), .killed 21 (some 18), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67086468,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66666144,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66694816,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66796192,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66824864,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66927776,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4, zeroMask := 66956448,
        component := 33 }
    witnesses := [.killed 23 (some 13), .killed 21 (some 18), .killed 25 (some 22), .killed 18 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 18 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67057824,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 22), .killed 18 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4, zeroMask := 67086496,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk003_valid :
    List.Forall StratumCertificate.Valid certificateChunk003 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk004 : List StratumCertificate := [
  { stratum :=
      { activeMask := 5, zeroMask := 66927616,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 10), .killed 21 (some 18), .killed 23 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 23 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 5, zeroMask := 66956288,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 25 (some 21), .killed 15 (some 10), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 25 (some 18), .killed 15 (some 10), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 10), .killed 21 (some 18), .killed 23 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 23 (some 22), .chain 5, .killed 18 (some 23), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 5, zeroMask := 67057664,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 18), .killed 21 (some 18), .killed 23 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 22), .killed 18 (some 22), .killed 23 (some 22), .chain 5, .killed 12 (some 17), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 5, zeroMask := 67086336,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 21 (some 18), .killed 23 (some 25), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 23 (some 22), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk004_valid :
    List.Forall StratumCertificate.Valid certificateChunk004 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk005 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8, zeroMask := 18079721,
        component := 50 }
    witnesses := [.killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20175849,
        component := 50 }
    witnesses := [.killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18341225,
        component := 49 }
    witnesses := [.killed 15 (some 10), .killed 3 (some 14), .killed 3 (some 15), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20437353,
        component := 49 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52125609,
        component := 50 }
    witnesses := [.killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18599849,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 10 (some 15), .chain 37, .killed 0 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54221737,
        component := 50 }
    witnesses := [.killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20695977,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 37, .killed 0 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52387113,
        component := 45 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18861353,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 10), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 10), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54483241,
        component := 45 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20957481,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 8, zeroMask := 51601377,
        component := 45 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52154337,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 53697505,
        component := 52 }
    witnesses := [.killed 6 (some 7), .killed 25 (some 14), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54250465,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (some 14), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 8 (some 6), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 51862881,
        component := 46 }
    witnesses := [.chain 37, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52415841,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 25 (some 14), .killed 5 (some 0), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 53959009,
        component := 46 }
    witnesses := [.chain 37, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54511969,
        component := 23 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 5 (some 0), .killed 19 (some 15), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 19 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18087912,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20184040,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18349544,
        component := 62 }
    witnesses := [.killed 15 (some 10), .killed 3 (some 14), .killed 3 (some 15), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20445672,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52133800,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18608040,
        component := 39 }
    witnesses := [.killed 17 (some 13), .killed 10 (some 15), .killed 10 (some 15), .chain 37, .killed 13 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54229928,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20704168,
        component := 39 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 37, .killed 13 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52395432,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 18869672,
        component := 33 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 18), .killed 3 (some 14), .killed 18 (some 14), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 18 (some 14), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54491560,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 20965800,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 8, zeroMask := 51609568,
        component := 56 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52162528,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 53705696,
        component := 65 }
    witnesses := [.killed 8 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54258656,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (some 14), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 8 (some 6), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 51871200,
        component := 57 }
    witnesses := [.killed 5 (some 7), .chain 37, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 52424160,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 25 (some 14), .killed 5 (some 7), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 53967328,
        component := 57 }
    witnesses := [.killed 5 (some 7), .chain 37, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8, zeroMask := 54520288,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk005_valid :
    List.Forall StratumCertificate.Valid certificateChunk005 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
