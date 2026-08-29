import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 0 through 0.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk000 : List StratumCertificate := [
  { stratum :=
      { activeMask := 0, zeroMask := 18079727,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28434159,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20175599,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18341231,
        component := 49 }
    witnesses := [.killed 15 (some 10), .killed 3 (some 14), .killed 3 (some 15), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28695663,
        component := 15 }
    witnesses := [.killed 12 (some 5), .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20437103,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52125615,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18599855,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 1 (some 2), .killed 0 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62480047,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28954287,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54221487,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20695727,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52387119,
        component := 45 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18861359,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 10), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 10), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62741551,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29215791,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54482991,
        component := 45 }
    witnesses := [.killed 21 (some 18), .killed 19 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20957231,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18349391,
        component := 62 }
    witnesses := [.killed 15 (some 10), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22527311,
        component := 59 }
    witnesses := [.killed 15 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 6 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28703823,
        component := 15 }
    witnesses := [.killed 12 (some 13), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 12), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32881743,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 12), .killed 2 (some 0), .killed 2 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20445263,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 14), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24623183,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52395279,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56573199,
        component := 59 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 19 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18869519,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 10), .killed 8 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 10), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 23047439,
        component := 36 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 2 (some 0), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62749711,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66927631,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29223951,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33401871,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 13), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 2 (some 0), .killed 2 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54491151,
        component := 56 }
    witnesses := [.killed 21 (some 18), .killed 19 (some 18), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58669071,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20965391,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 25143311,
        component := 28 }
    witnesses := [.killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 51601383,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52154343,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 8 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 61955815,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 1 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62508775,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 21 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 53697255,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54250215,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 51862887,
        component := 46 }
    witnesses := [.killed 1 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52415847,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 25 (some 14), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62217319,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 12), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62770279,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 53958759,
        component := 45 }
    witnesses := [.killed 21 (some 18), .killed 6 (some 18), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54511719,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 14), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 51871047,
        component := 57 }
    witnesses := [.killed 2 (some 0), .killed 1 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56048967,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 22), .killed 10 (some 22), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52424007,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 25 (some 14), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56601927,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 25 (some 22), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62225479,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 12), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66403399,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 23), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62778439,
        component := 3 }
    witnesses := [.killed 19 (some 13), .killed 10 (some 15), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66956359,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 25 (some 22), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 53966919,
        component := 56 }
    witnesses := [.killed 21 (some 18), .killed 6 (some 18), .killed 21 (some 0), .killed 18 (some 0), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58144839,
        component := 54 }
    witnesses := [.killed 2 (some 0), .killed 25 (none), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 6 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54519879,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 14), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58697799,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22257643,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32612075,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24353515,
        component := 48 }
    witnesses := [.killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22519147,
        component := 47 }
    witnesses := [.killed 15 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 6 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32873579,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24615019,
        component := 47 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56303531,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22777771,
        component := 32 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 9), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66657963,
        component := 30 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33132203,
        component := 32 }
    witnesses := [.killed 23 (some 0), .killed 21 (some 9), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58399403,
        component := 48 }
    witnesses := [.killed 19 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24873643,
        component := 30 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56565035,
        component := 47 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 19 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 23039275,
        component := 36 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 18 (some 17), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66919467,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 25 (some 23), .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33393707,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 18 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58660907,
        component := 47 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 19 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 25135147,
        component := 27 }
    witnesses := [.killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 55779299,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56332259,
        component := 33 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 9), .killed 25 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66133731,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 21 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 22), .killed 12 (some 9), .killed 12 (some 22), .killed 10 (some 9), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66686691,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 57875171,
        component := 52 }
    witnesses := [.killed 6 (some 7), .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58428131,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56040803,
        component := 49 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 22), .killed 10 (some 22), .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56593763,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 25 (some 22), .killed 5 (some 0), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 17), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66395235,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 23), .killed 10 (some 6), .killed 25 (some 21), .killed 18 (some 6), .killed 22 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66948195,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 25 (some 21), .killed 15 (some 10), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 25 (some 18), .killed 15 (some 10), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 19), .killed 5 (some 19), .killed 21 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 10 (some 15), .killed 10 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58136675,
        component := 44 }
    witnesses := [.killed 25 (none), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 6 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58689635,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26337261,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28564461,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26598765,
        component := 16 }
    witnesses := [.killed 12 (some 5), .killed 3 (some 14), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28825965,
        component := 49 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60383149,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26857389,
        component := 9 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62610349,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29084589,
        component := 9 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60644653,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 19 (some 3), .killed 18 (some 3), .killed 5 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 27118893,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 3 (some 14), .killed 19 (some 14), .killed 18 (some 14), .killed 5 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 5 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62871853,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 19 (some 3), .killed 18 (some 3), .killed 5 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29346093,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26606925,
        component := 16 }
    witnesses := [.killed 12 (some 13), .killed 3 (some 14), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30784845,
        component := 16 }
    witnesses := [.killed 12 (some 13), .killed 3 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28834125,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33012045,
        component := 62 }
    witnesses := [.killed 15 (some 21), .killed 3 (some 22), .killed 3 (some 15), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60652813,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 19 (some 3), .killed 18 (some 3), .killed 13 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64830733,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 27127053,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 14), .killed 19 (some 14), .killed 18 (some 14), .killed 13 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 13 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31304973,
        component := 8 }
    witnesses := [.killed 2 (some 0), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62880013,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 19 (some 3), .killed 18 (some 3), .killed 13 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67057933,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 8 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29354253,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33532173,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 21 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 59858917,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60411877,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62086117,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62639077,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60120421,
        component := 4 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60673381,
        component := 4 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62347621,
        component := 4 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62900581,
        component := 4 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60128581,
        component := 4 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64306501,
        component := 1 }
    witnesses := [.killed 2 (some 0), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60681541,
        component := 4 }
    witnesses := [.killed 19 (some 13), .killed 10 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64859461,
        component := 16 }
    witnesses := [.killed 19 (some 13), .killed 25 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62355781,
        component := 4 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66533701,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 22), .killed 21 (some 22), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62908741,
        component := 4 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67086661,
        component := 17 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 25 (some 22), .killed 13 (some 17), .killed 21 (some 17), .killed 21 (some 15), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30515177,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32742377,
        component := 52 }
    witnesses := [.killed 6 (some 7), .killed 3 (some 22), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30776681,
        component := 37 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 3 (some 22), .killed 5 (some 0), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33003881,
        component := 49 }
    witnesses := [.killed 15 (some 21), .killed 3 (some 22), .killed 3 (some 15), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64561065,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 9 (some 7), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 9 (some 7), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31035305,
        component := 33 }
    witnesses := [.killed 23 (some 0), .killed 8 (some 9), .killed 3 (some 22), .killed 9 (some 23), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66788265,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33262505,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 17), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64822569,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31296809,
        component := 7 }
    witnesses := [.killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67049769,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 17), .killed 19 (some 23), .killed 18 (some 23), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 19 (some 22), .killed 18 (some 22), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33524009,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64036833,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64589793,
        component := 33 }
    witnesses := [.killed 23 (some 0), .killed 8 (some 9), .killed 25 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66264033,
        component := 52 }
    witnesses := [.killed 6 (some 7), .killed 25 (some 22), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66816993,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 17), .killed 8 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64298337,
        component := 0 }
    witnesses := [.killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64851297,
        component := 37 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 25 (some 22), .killed 5 (some 0), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66525537,
        component := 49 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 22), .killed 21 (some 22), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67078497,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18087886,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22265806,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 9), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18349518,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 18), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22527438,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 18), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28442318,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32620238,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 9), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20183758,
        component := 66 }
    witnesses := [.killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24361678,
        component := 60 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28703950,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 18), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32881870,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 18), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20445390,
        component := 61 }
    witnesses := [.killed 15 (some 14), .killed 21 (some 18), .killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 3 (some 15), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24623310,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 18), .killed 15 (some 18), .killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52133774,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56311694,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18608014,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22785934,
        component := 36 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 9), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52395406,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56573326,
        component := 59 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 18869646,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 10), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 23047566,
        component := 36 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62488206,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66666126,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28962446,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33140366,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54229646,
        component := 65 }
    witnesses := [.killed 19 (some 14), .killed 19 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58407566,
        component := 60 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20703886,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 21 (some 9), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 19), .killed 3 (some 9), .killed 3 (some 17), .killed 3 (some 9), .killed 3 (some 17), .killed 3 (some 9), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24881806,
        component := 29 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 9 (none), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62749838,
        component := 6 }
    witnesses := [.killed 10 (some 12), .killed 21 (some 18), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66927758,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 22), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29224078,
        component := 19 }
    witnesses := [.killed 21 (some 18), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33401998,
        component := 19 }
    witnesses := [.killed 21 (some 18), .killed 3 (some 22), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54491278,
        component := 56 }
    witnesses := [.killed 21 (some 18), .killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58669198,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 20965518,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 19), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 25143438,
        component := 28 }
    witnesses := [.killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 51609542,
        component := 58 }
    witnesses := [.killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 55787462,
        component := 61 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 25 (some 22), .killed 10 (some 9), .killed 10 (some 8), .killed 24 (some 22), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52162502,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56340422,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 9), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 51871174,
        component := 57 }
    witnesses := [.killed 2 (some 7), .killed 1 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56049094,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 22), .killed 10 (some 22), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 52424134,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 18), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56602054,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 18), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 61963974,
        component := 24 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66141894,
        component := 41 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62516934,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 25 (some 14), .killed 1 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66694854,
        component := 20 }
    witnesses := [.killed 10 (some 15), .killed 25 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 53705414,
        component := 58 }
    witnesses := [.killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 57883334,
        component := 66 }
    witnesses := [.killed 25 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54258374,
        component := 24 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58436294,
        component := 41 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62225606,
        component := 24 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 21 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66403526,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 21), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 25 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62778566,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 21 (some 18), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66956486,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 21 (some 18), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 53967046,
        component := 58 }
    witnesses := [.killed 21 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58144966,
        component := 54 }
    witnesses := [.killed 2 (some 7), .killed 25 (none), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 6 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 54520006,
        component := 24 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 21 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58697926,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22265834,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22527466,
        component := 59 }
    witnesses := [.killed 15 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32620266,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 21 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24361706,
        component := 60 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32881898,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 21 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24623338,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 18), .killed 15 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56311722,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 22785962,
        component := 32 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 9), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56573354,
        component := 59 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 23047594,
        component := 32 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66666154,
        component := 30 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33140394,
        component := 32 }
    witnesses := [.killed 23 (some 13), .killed 21 (some 9), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58407594,
        component := 60 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 24881834,
        component := 30 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66927786,
        component := 31 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33402026,
        component := 32 }
    witnesses := [.killed 23 (some 13), .killed 21 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58669226,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 18), .killed 25 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 25143466,
        component := 28 }
    witnesses := [.killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 55787490,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56340450,
        component := 33 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 9), .killed 25 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56049122,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 56602082,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 25 (some 22), .killed 5 (some 7), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 7), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66141922,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 21 (some 9), .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 9), .killed 5 (some 22), .killed 5 (some 9), .killed 5 (some 22), .killed 12 (some 9), .killed 12 (some 22), .killed 10 (some 9), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66694882,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 57883362,
        component := 65 }
    witnesses := [.killed 25 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58436322,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66403554,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 18), .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 18 (some 6), .killed 22 (some 7), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66956514,
        component := 33 }
    witnesses := [.killed 23 (some 13), .killed 21 (some 18), .killed 25 (some 22), .killed 18 (some 6), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58144994,
        component := 54 }
    witnesses := [.killed 5 (some 7), .killed 25 (none), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 6 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 58697954,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26345420,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 15), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 14), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30523340,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 15), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28572620,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32750540,
        component := 65 }
    witnesses := [.killed 8 (some 23), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 23 (some 2), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26607052,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 3 (some 14), .killed 2 (some 7), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30784972,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 3 (some 22), .killed 2 (some 7), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 28834252,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33012172,
        component := 62 }
    witnesses := [.killed 15 (some 21), .killed 3 (some 22), .killed 3 (some 15), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60391308,
        component := 12 }
    witnesses := [.killed 10 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64569228,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 9 (some 7), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 26865548,
        component := 12 }
    witnesses := [.killed 10 (some 15), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31043468,
        component := 19 }
    witnesses := [.killed 8 (some 9), .killed 3 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62618508,
        component := 12 }
    witnesses := [.killed 17 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66796428,
        component := 20 }
    witnesses := [.killed 17 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29092748,
        component := 12 }
    witnesses := [.killed 17 (some 15), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33270668,
        component := 20 }
    witnesses := [.killed 17 (some 15), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60652940,
        component := 6 }
    witnesses := [.killed 10 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64830860,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 27127180,
        component := 19 }
    witnesses := [.killed 8 (some 18), .killed 3 (some 14), .killed 18 (some 14), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31305100,
        component := 8 }
    witnesses := [.killed 2 (some 7), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62880140,
        component := 6 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67058060,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 19 (some 23), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 21), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 29354380,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33532300,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 59867076,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 14), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 14), .killed 23 (some 9), .killed 23 (some 8), .killed 13 (some 9), .killed 13 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64044996,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 23 (some 9), .killed 23 (some 8), .killed 13 (some 9), .killed 13 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60420036,
        component := 6 }
    witnesses := [.killed 10 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64597956,
        component := 19 }
    witnesses := [.killed 8 (some 9), .killed 25 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62094276,
        component := 65 }
    witnesses := [.killed 8 (some 14), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 14), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66272196,
        component := 65 }
    witnesses := [.killed 8 (some 23), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62647236,
        component := 20 }
    witnesses := [.killed 17 (some 15), .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66825156,
        component := 20 }
    witnesses := [.killed 17 (some 15), .killed 25 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60128708,
        component := 23 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 2 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 10 (some 7), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64306628,
        component := 1 }
    witnesses := [.killed 2 (some 7), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 60681668,
        component := 6 }
    witnesses := [.killed 10 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64859588,
        component := 19 }
    witnesses := [.killed 8 (some 18), .killed 25 (some 22), .killed 18 (some 6), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62355908,
        component := 57 }
    witnesses := [.killed 2 (some 7), .killed 23 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66533828,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 22), .killed 21 (some 22), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 62908868,
        component := 6 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67086788,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 21 (some 19), .killed 18 (some 8), .killed 13 (some 17), .killed 13 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30523368,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 32750568,
        component := 65 }
    witnesses := [.killed 8 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 30785000,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 3 (some 22), .killed 5 (some 7), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33012200,
        component := 62 }
    witnesses := [.killed 15 (some 21), .killed 3 (some 22), .killed 3 (some 15), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64569256,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 9 (some 7), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 9 (some 7), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31043496,
        component := 33 }
    witnesses := [.killed 23 (some 13), .killed 8 (some 9), .killed 3 (some 22), .killed 9 (some 23), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66796456,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33270696,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64830888,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 31305128,
        component := 8 }
    witnesses := [.killed 5 (some 7), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 18 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67058088,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 19 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 21), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 23), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 17), .killed 19 (some 7), .killed 18 (some 22), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 33532328,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64045024,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64597984,
        component := 33 }
    witnesses := [.killed 23 (some 13), .killed 8 (some 9), .killed 25 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66272224,
        component := 65 }
    witnesses := [.killed 8 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66825184,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 8 (some 6), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64306656,
        component := 1 }
    witnesses := [.killed 5 (some 7), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 22 (none), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 64859616,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 5), .killed 25 (some 22), .killed 5 (some 7), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 66533856,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 22), .killed 21 (some 22), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 0, zeroMask := 67086816,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 22), .killed 5 (some 19), .killed 5 (some 8), .killed 5 (some 17), .killed 5 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk000_valid :
    List.Forall StratumCertificate.Valid certificateChunk000 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
