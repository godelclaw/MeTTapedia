import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 35 through 51.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk035 : List StratumCertificate := [
  { stratum :=
      { activeMask := 544, zeroMask := 17030383,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 25287919,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 51076271,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 12), .killed 10 (some 12), .chain 11, .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 59333807,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 17550511,
        component := 33 }
    witnesses := [.killed 17 (some 0), .chain 11, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 25808047,
        component := 15 }
    witnesses := [.killed 19 (some 5), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 7), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 50552039,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 58809575,
        component := 24 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 51104999,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 59362535,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 21208299,
        component := 47 }
    witnesses := [.killed 15 (some 10), .chain 11, .killed 15 (some 10), .killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 29465835,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .chain 11, .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 55254187,
        component := 47 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .killed 19 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 63511723,
        component := 31 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 21728427,
        component := 32 }
    witnesses := [.killed 17 (some 0), .chain 11, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 29985963,
        component := 32 }
    witnesses := [.killed 23 (some 0), .chain 11, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 54729955,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 22 (some 7), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 62987491,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 22 (some 7), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 55282915,
        component := 33 }
    witnesses := [.killed 17 (some 0), .chain 11, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 63540451,
        component := 33 }
    witnesses := [.killed 23 (some 0), .chain 11, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 17038542,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 25296078,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 21216462,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .chain 11, .killed 3 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 29473998,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .chain 11, .killed 3 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 51084430,
        component := 56 }
    witnesses := [.chain 11, .killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 59341966,
        component := 6 }
    witnesses := [.killed 10 (some 12), .chain 11, .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 55262350,
        component := 59 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 63519886,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 19 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 17558670,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 10), .chain 11, .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 25816206,
        component := 19 }
    witnesses := [.chain 11, .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 21736590,
        component := 36 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .chain 11, .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 29994126,
        component := 19 }
    witnesses := [.chain 11, .killed 3 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 50560198,
        component := 58 }
    witnesses := [.chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 58817734,
        component := 24 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 54738118,
        component := 61 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .killed 25 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 62995654,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 23 (some 22), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 51113158,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 59370694,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 55291078,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .chain 11, .killed 25 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 63548614,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .chain 11, .killed 25 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 21216490,
        component := 59 }
    witnesses := [.killed 15 (some 10), .chain 11, .killed 15 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 29474026,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .chain 11, .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 55262378,
        component := 59 }
    witnesses := [.killed 25 (some 10), .chain 11, .killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 63519914,
        component := 31 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 21736618,
        component := 32 }
    witnesses := [.killed 17 (some 13), .chain 11, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 29994154,
        component := 32 }
    witnesses := [.killed 23 (some 13), .chain 11, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 54738146,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 22 (some 7), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 62995682,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 22 (some 7), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 544, zeroMask := 55291106,
        component := 33 }
    witnesses := [.killed 17 (some 13), .chain 11, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 544, zeroMask := 63548642,
        component := 33 }
    witnesses := [.killed 23 (some 13), .chain 11, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk035_valid :
    List.Forall StratumCertificate.Valid certificateChunk035 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk036 : List StratumCertificate := [
  { stratum :=
      { activeMask := 546, zeroMask := 16899310,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 50945198,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 11, .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 17419438,
        component := 33 }
    witnesses := [.chain 32, .chain 11, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 50420966,
        component := 24 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .chain 11, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 50973926,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 21077226,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .chain 11, .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 55123114,
        component := 31 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 21597354,
        component := 32 }
    witnesses := [.chain 32, .chain 11, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 546, zeroMask := 54598882,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 22 (some 7), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 546, zeroMask := 55151842,
        component := 33 }
    witnesses := [.chain 32, .chain 11, .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk036_valid :
    List.Forall StratumCertificate.Valid certificateChunk036 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk037 : List StratumCertificate := [
  { stratum :=
      { activeMask := 548, zeroMask := 59333797,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 19 (some 7), .chain 14, .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 548, zeroMask := 59362469,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .killed 19 (some 7), .chain 14, .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 548, zeroMask := 63511713,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 19 (some 7), .killed 25 (some 23), .killed 19 (some 7), .killed 22 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 25 (some 22), .killed 19 (some 7), .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 548, zeroMask := 63540385,
        component := 33 }
    witnesses := [.killed 23 (some 0), .chain 11, .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 25 (some 22), .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 548, zeroMask := 59341956,
        component := 6 }
    witnesses := [.killed 10 (some 12), .chain 11, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 548, zeroMask := 63519876,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 19 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 25 (some 22), .killed 23 (some 19), .killed 23 (some 19), .killed 13 (some 19), .killed 13 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 25 (some 22), .killed 19 (some 7), .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 548, zeroMask := 59370628,
        component := 6 }
    witnesses := [.killed 10 (some 15), .chain 11, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 548, zeroMask := 63548548,
        component := 19 }
    witnesses := [.chain 11, .killed 25 (some 22), .killed 25 (some 22), .chain 14, .chain 10, .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 548, zeroMask := 63519904,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 11, .killed 19 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 19), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 19 (some 7), .killed 25 (some 23), .killed 19 (some 7), .killed 22 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 25 (some 22), .killed 19 (some 7), .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 548, zeroMask := 63548576,
        component := 33 }
    witnesses := [.killed 23 (some 13), .chain 11, .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 25 (some 22), .chain 14, .chain 10, .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk037_valid :
    List.Forall StratumCertificate.Valid certificateChunk037 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk038 : List StratumCertificate := [
  { stratum :=
      { activeMask := 556, zeroMask := 51076257,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 12), .killed 10 (some 12), .chain 11, .chain 45, .chain 36, .chain 37, .killed 0 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 556, zeroMask := 51104929,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 10 (some 15), .chain 11, .chain 45, .chain 36, .chain 37, .killed 0 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 556, zeroMask := 51084448,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 10 (some 12), .killed 10 (some 12), .chain 11, .chain 45, .chain 36, .chain 37, .killed 13 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 556, zeroMask := 51113120,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 10 (some 15), .killed 10 (some 15), .chain 11, .chain 45, .chain 36, .chain 37, .killed 13 (some 17), .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk038_valid :
    List.Forall StratumCertificate.Valid certificateChunk038 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk039 : List StratumCertificate := [
  { stratum :=
      { activeMask := 558, zeroMask := 50945184,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 11, .chain 45, .chain 36, .chain 37, .chain 38, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 558, zeroMask := 50973856,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 11, .chain 45, .chain 36, .chain 37, .chain 38, .chain 14, .chain 10, .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk039_valid :
    List.Forall StratumCertificate.Valid certificateChunk039 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk040 : List StratumCertificate := [
  { stratum :=
      { activeMask := 576, zeroMask := 17026527,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 21204447,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 27380959,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 31558879,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 19122399,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 576, zeroMask := 23300319,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 576, zeroMask := 50580951,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 54758871,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 60935383,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 65113303,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 25 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 52676823,
        component := 21 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 56854743,
        component := 21 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 25284061,
        component := 11 }
    witnesses := [.chain 6, .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 29461981,
        component := 11 }
    witnesses := [.chain 6, .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 27511261,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 31689181,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 58838485,
        component := 3 }
    witnesses := [.chain 6, .killed 10 (some 15), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 63016405,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 4), .killed 25 (some 7), .killed 25 (some 6), .killed 25 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 61065685,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 576, zeroMask := 65243605,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk040_valid :
    List.Forall StratumCertificate.Valid certificateChunk040 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk041 : List StratumCertificate := [
  { stratum :=
      { activeMask := 578, zeroMask := 16895454,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 21073374,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 18992350,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 23170270,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 50449878,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 54627798,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 52546774,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 578, zeroMask := 56724694,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 25 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk041_valid :
    List.Forall StratumCertificate.Valid certificateChunk041 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk042 : List StratumCertificate := [
  { stratum :=
      { activeMask := 608, zeroMask := 17026255,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 25283791,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 21204175,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 11, .killed 3 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 29461711,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .chain 11, .killed 3 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 50580679,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 58838215,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 54758599,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 11, .killed 25 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 608, zeroMask := 63016135,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .chain 11, .killed 25 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk042_valid :
    List.Forall StratumCertificate.Valid certificateChunk042 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk043 : List StratumCertificate := [
  { stratum :=
      { activeMask := 610, zeroMask := 16895182,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .chain 11, .killed 3 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 610, zeroMask := 21073102,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .chain 11, .killed 3 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 610, zeroMask := 50449606,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .chain 11, .killed 25 (some 14), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 610, zeroMask := 54627526,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .chain 11, .killed 25 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk043_valid :
    List.Forall StratumCertificate.Valid certificateChunk043 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk044 : List StratumCertificate := [
  { stratum :=
      { activeMask := 640, zeroMask := 17030463,
        component := 51 }
    witnesses := [.killed 15 (some 10), .chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 50552127,
        component := 51 }
    witnesses := [.killed 25 (some 10), .chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 27384895,
        component := 15 }
    witnesses := [.killed 12 (some 5), .killed 21 (some 4), .chain 8, .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 60906559,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 19126335,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 640, zeroMask := 52647999,
        component := 43 }
    witnesses := [.chain 8, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 17038623,
        component := 64 }
    witnesses := [.killed 15 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 50560287,
        component := 64 }
    witnesses := [.killed 25 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 21216543,
        component := 64 }
    witnesses := [.killed 15 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 54738207,
        component := 64 }
    witnesses := [.killed 25 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 27393055,
        component := 15 }
    witnesses := [.killed 12 (some 13), .killed 21 (some 4), .chain 8, .killed 13 (some 12), .killed 3 (some 4), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 60914719,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 31570975,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 21 (some 4), .chain 8, .killed 13 (some 12), .killed 2 (some 0), .killed 2 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 65092639,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 19134495,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .killed 13 (some 12), .killed 15 (some 0), .killed 14 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 640, zeroMask := 52656159,
        component := 53 }
    witnesses := [.chain 8, .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 23312415,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 56834079,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 4), .killed 25 (some 4), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 21208379,
        component := 51 }
    witnesses := [.killed 15 (some 10), .chain 8, .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 54730043,
        component := 51 }
    witnesses := [.killed 25 (some 10), .chain 8, .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 31562811,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 4), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 12 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 65084475,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 25 (some 4), .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 640, zeroMask := 23304251,
        component := 47 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 56825915,
        component := 43 }
    witnesses := [.chain 8, .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 25287997,
        component := 11 }
    witnesses := [.killed 12 (some 5), .chain 8, .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 58809661,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 27515197,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 61036861,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 25296157,
        component := 11 }
    witnesses := [.killed 12 (some 13), .chain 8, .killed 13 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 58817821,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 29474077,
        component := 11 }
    witnesses := [.killed 12 (some 13), .chain 8, .killed 13 (some 12), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 62995741,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 27523357,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 61045021,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 31701277,
        component := 64 }
    witnesses := [.killed 15 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 65222941,
        component := 64 }
    witnesses := [.killed 25 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 29465913,
        component := 35 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 12 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 62987577,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 23), .killed 25 (some 23), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 22), .killed 25 (some 22), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 640, zeroMask := 31693113,
        component := 51 }
    witnesses := [.killed 15 (some 21), .chain 8, .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 640, zeroMask := 65214777,
        component := 51 }
    witnesses := [.killed 25 (some 21), .chain 8, .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk044_valid :
    List.Forall StratumCertificate.Valid certificateChunk044 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk045 : List StratumCertificate := [
  { stratum :=
      { activeMask := 641, zeroMask := 21216538,
        component := 64 }
    witnesses := [.killed 15 (some 10), .chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 54738202,
        component := 64 }
    witnesses := [.killed 25 (some 10), .chain 8, .chain 5, .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 31570970,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 4), .chain 8, .killed 13 (some 12), .chain 5, .killed 12 (some 23), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 65092634,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 13 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 21 (some 25), .killed 4 (some 25), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 25 (some 4), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 641, zeroMask := 23312410,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 56834074,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 4), .killed 25 (some 4), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 29474072,
        component := 35 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .chain 8, .killed 13 (some 12), .chain 5, .killed 12 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 62995736,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 25), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 23), .killed 25 (some 23), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 22), .killed 25 (some 22), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 641, zeroMask := 31701272,
        component := 64 }
    witnesses := [.killed 15 (some 21), .chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 641, zeroMask := 65222936,
        component := 64 }
    witnesses := [.killed 25 (some 21), .chain 8, .chain 5, .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk045_valid :
    List.Forall StratumCertificate.Valid certificateChunk045 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk046 : List StratumCertificate := [
  { stratum :=
      { activeMask := 644, zeroMask := 60906549,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 644, zeroMask := 61036597,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 8, .killed 5 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 644, zeroMask := 60914709,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 644, zeroMask := 65092629,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 644, zeroMask := 61044757,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 644, zeroMask := 65222677,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 644, zeroMask := 65084465,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 22), .killed 12 (some 4), .killed 12 (some 22), .killed 10 (some 4), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 644, zeroMask := 65214513,
        component := 43 }
    witnesses := [.chain 8, .killed 22 (some 23), .killed 23 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk046_valid :
    List.Forall StratumCertificate.Valid certificateChunk046 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk047 : List StratumCertificate := [
  { stratum :=
      { activeMask := 645, zeroMask := 65092624,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 13 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 21 (some 25), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .killed 23 (some 22), .killed 13 (some 4), .killed 13 (some 22), .killed 12 (some 4), .killed 12 (some 22), .killed 10 (some 4), .killed 10 (some 22), .killed 23 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 645, zeroMask := 65222672,
        component := 53 }
    witnesses := [.chain 8, .killed 23 (some 22), .killed 23 (some 22), .chain 5, .killed 22 (some 23), .killed 23 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk047_valid :
    List.Forall StratumCertificate.Valid certificateChunk047 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk048 : List StratumCertificate := [
  { stratum :=
      { activeMask := 648, zeroMask := 17030457,
        component := 51 }
    witnesses := [.killed 15 (some 10), .chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 648, zeroMask := 50552121,
        component := 51 }
    witnesses := [.killed 25 (some 10), .chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 648, zeroMask := 19126585,
        component := 51 }
    witnesses := [.killed 15 (some 14), .chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 648, zeroMask := 52648249,
        component := 51 }
    witnesses := [.killed 25 (some 14), .chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk048_valid :
    List.Forall StratumCertificate.Valid certificateChunk048 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk049 : List StratumCertificate := [
  { stratum :=
      { activeMask := 649, zeroMask := 17038616,
        component := 64 }
    witnesses := [.killed 15 (some 10), .chain 8, .chain 5, .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 649, zeroMask := 50560280,
        component := 64 }
    witnesses := [.killed 25 (some 10), .chain 8, .chain 5, .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 649, zeroMask := 19134744,
        component := 64 }
    witnesses := [.killed 15 (some 14), .chain 8, .chain 5, .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 649, zeroMask := 52656408,
        component := 64 }
    witnesses := [.killed 25 (some 14), .chain 8, .chain 5, .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk049_valid :
    List.Forall StratumCertificate.Valid certificateChunk049 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk050 : List StratumCertificate := [
  { stratum :=
      { activeMask := 652, zeroMask := 52647985,
        component := 43 }
    witnesses := [.chain 8, .chain 36, .chain 37, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk050_valid :
    List.Forall StratumCertificate.Valid certificateChunk050 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk051 : List StratumCertificate := [
  { stratum :=
      { activeMask := 653, zeroMask := 52656144,
        component := 53 }
    witnesses := [.chain 8, .chain 66, .chain 74, .chain 5, .chain 36, .chain 37, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk051_valid :
    List.Forall StratumCertificate.Valid certificateChunk051 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
