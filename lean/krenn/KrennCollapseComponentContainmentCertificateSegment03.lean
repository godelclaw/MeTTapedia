import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 28 through 34.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk028 : List StratumCertificate := [
  { stratum :=
      { activeMask := 512, zeroMask := 17030655,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 27385087,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 19126527,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 14), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 512, zeroMask := 51076543,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 17550783,
        component := 34 }
    witnesses := [.killed 17 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61430975,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 27905215,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 21 (some 4), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 7), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 53172415,
        component := 43 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 19646655,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 512, zeroMask := 50552311,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 51105271,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 60906743,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61459703,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 52648183,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 53201143,
        component := 21 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 21208571,
        component := 51 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 31563003,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 23304443,
        component := 47 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 55254459,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 1 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 21728699,
        component := 32 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65608891,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 32083131,
        component := 32 }
    witnesses := [.killed 23 (some 0), .killed 21 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 57350331,
        component := 43 }
    witnesses := [.killed 19 (some 7), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 23824571,
        component := 31 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 54730227,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 55283187,
        component := 33 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65084659,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 22), .killed 12 (some 4), .killed 12 (some 22), .killed 10 (some 4), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 25 (some 4), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65637619,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 56826099,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 57379059,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 25288189,
        component := 11 }
    witnesses := [.killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 27515389,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 59334077,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 25808317,
        component := 11 }
    witnesses := [.killed 19 (some 5), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61561277,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 28035517,
        component := 10 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 58809845,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 59362805,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61037045,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61590005,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 29466105,
        component := 35 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 12 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 31693305,
        component := 51 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 63511993,
        component := 40 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 23 (some 22), .killed 0 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 29986233,
        component := 34 }
    witnesses := [.killed 23 (some 0), .killed 23 (some 22), .killed 0 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65739193,
        component := 51 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 7), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 32213433,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 23 (some 22), .killed 0 (some 17), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 62987761,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 63540721,
        component := 33 }
    witnesses := [.killed 23 (some 0), .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65214961,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 8 (some 6), .killed 23 (some 22), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65767921,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 17), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 17038814,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 21216734,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 27393246,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 31571166,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 19134686,
        component := 61 }
    witnesses := [.killed 15 (some 14), .killed 21 (some 4), .killed 15 (some 4), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 15), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 23312606,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 51084702,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 55262622,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 17558942,
        component := 35 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 21736862,
        component := 36 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61439134,
        component := 5 }
    witnesses := [.killed 10 (some 12), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65617054,
        component := 5 }
    witnesses := [.killed 10 (some 12), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 27913374,
        component := 19 }
    witnesses := [.killed 21 (some 4), .killed 3 (some 4), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 32091294,
        component := 19 }
    witnesses := [.killed 21 (some 4), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 53180574,
        component := 53 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 57358494,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 4), .killed 25 (some 4), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 19654814,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 4), .killed 19 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 19), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 512, zeroMask := 23832734,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 19 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 19), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 512, zeroMask := 50560470,
        component := 58 }
    witnesses := [.killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 54738390,
        component := 61 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 25 (some 4), .killed 10 (some 4), .killed 10 (some 8), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 51113430,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 55291350,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 60914902,
        component := 21 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65092822,
        component := 21 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61467862,
        component := 5 }
    witnesses := [.killed 10 (some 15), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65645782,
        component := 5 }
    witnesses := [.killed 10 (some 15), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 52656342,
        component := 55 }
    witnesses := [.killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 56834262,
        component := 55 }
    witnesses := [.killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 53209302,
        component := 21 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 57387222,
        component := 21 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 21216762,
        component := 64 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 31571194,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 21 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 23312634,
        component := 59 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 55262650,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 21736890,
        component := 32 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65617082,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 32091322,
        component := 32 }
    witnesses := [.killed 23 (some 13), .killed 21 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 57358522,
        component := 59 }
    witnesses := [.killed 25 (some 21), .killed 21 (some 4), .killed 25 (some 4), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 23832762,
        component := 31 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 54738418,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 55291378,
        component := 33 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65092850,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 13 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 22), .killed 5 (some 4), .killed 5 (some 22), .killed 12 (some 4), .killed 12 (some 22), .killed 10 (some 4), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 25 (some 4), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65645810,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 56834290,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 57387250,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 25296348,
        component := 35 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 6 (some 7), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 29474268,
        component := 35 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 6 (some 7), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 27523548,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 31701468,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 59342236,
        component := 6 }
    witnesses := [.killed 10 (some 12), .killed 8 (some 4), .killed 4 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 63520156,
        component := 13 }
    witnesses := [.killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 25816476,
        component := 14 }
    witnesses := [.killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 29994396,
        component := 14 }
    witnesses := [.killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61569436,
        component := 5 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65747356,
        component := 5 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 28043676,
        component := 13 }
    witnesses := [.killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 32221596,
        component := 13 }
    witnesses := [.killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 58818004,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 14), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 23 (some 4), .killed 23 (some 8), .killed 13 (some 4), .killed 13 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 62995924,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 23 (some 4), .killed 23 (some 8), .killed 13 (some 4), .killed 13 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 59370964,
        component := 6 }
    witnesses := [.killed 10 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 63548884,
        component := 19 }
    witnesses := [.killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61045204,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65223124,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 61598164,
        component := 5 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65776084,
        component := 5 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 29474296,
        component := 35 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 31701496,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 63520184,
        component := 40 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 23 (some 22), .killed 13 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 29994424,
        component := 34 }
    witnesses := [.killed 23 (some 13), .killed 23 (some 22), .killed 13 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65747384,
        component := 64 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 22), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 32221624,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 23 (some 22), .killed 13 (some 17), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 62995952,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 512, zeroMask := 63548912,
        component := 33 }
    witnesses := [.killed 23 (some 13), .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65223152,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 23 (some 22), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 512, zeroMask := 65776112,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk028_valid :
    List.Forall StratumCertificate.Valid certificateChunk028 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk029 : List StratumCertificate := [
  { stratum :=
      { activeMask := 514, zeroMask := 16899582,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 18996478,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 50945470,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 17419710,
        component := 34 }
    witnesses := [.chain 32, .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 53042366,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 19516606,
        component := 33 }
    witnesses := [.chain 32, .killed 21 (some 4), .killed 3 (some 4), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 50421238,
        component := 24 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 8 (some 4), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 50974198,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 52518134,
        component := 21 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 53071094,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 21077498,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 23174394,
        component := 36 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 55123386,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 1 (some 22), .killed 1 (some 22), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 21597626,
        component := 32 }
    witnesses := [.chain 32, .killed 8 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 57220282,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 23694522,
        component := 32 }
    witnesses := [.chain 32, .killed 21 (some 4), .killed 24 (some 22), .killed 22 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 54599154,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 514, zeroMask := 55152114,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 514, zeroMask := 56696050,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 22), .killed 5 (some 4), .killed 5 (some 22), .killed 12 (some 4), .killed 12 (some 22), .killed 10 (some 4), .killed 10 (some 22), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 25 (some 4), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 514, zeroMask := 57249010,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk029_valid :
    List.Forall StratumCertificate.Valid certificateChunk029 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk030 : List StratumCertificate := [
  { stratum :=
      { activeMask := 516, zeroMask := 61430965,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61459637,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61561013,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61589685,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65608881,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65637553,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65738929,
        component := 43 }
    witnesses := [.killed 19 (some 7), .killed 22 (some 23), .killed 23 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65767601,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 17), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61439124,
        component := 5 }
    witnesses := [.killed 10 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65617044,
        component := 5 }
    witnesses := [.killed 10 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61467796,
        component := 5 }
    witnesses := [.killed 10 (some 15), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65645716,
        component := 5 }
    witnesses := [.killed 10 (some 15), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61569172,
        component := 5 }
    witnesses := [.killed 17 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65747092,
        component := 5 }
    witnesses := [.killed 17 (some 12), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 61597844,
        component := 5 }
    witnesses := [.killed 17 (some 15), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65775764,
        component := 5 }
    witnesses := [.killed 17 (some 15), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65617072,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65645744,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65747120,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 516, zeroMask := 65775792,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 17), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk030_valid :
    List.Forall StratumCertificate.Valid certificateChunk030 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk031 : List StratumCertificate := [
  { stratum :=
      { activeMask := 520, zeroMask := 17030649,
        component := 51 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 19126777,
        component := 51 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 51076537,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 17550777,
        component := 34 }
    witnesses := [.killed 17 (some 0), .chain 37, .killed 0 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 53172665,
        component := 51 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 19646905,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 37, .killed 0 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 50552305,
        component := 45 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 520, zeroMask := 51105265,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 10 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 52648433,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 53201393,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 17038840,
        component := 64 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 19134968,
        component := 64 }
    witnesses := [.killed 15 (some 14), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 51084728,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 17558968,
        component := 34 }
    witnesses := [.killed 17 (some 13), .chain 37, .killed 13 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 53180856,
        component := 64 }
    witnesses := [.killed 25 (some 14), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 19655096,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 37, .killed 13 (some 17), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 50560496,
        component := 56 }
    witnesses := [.killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 520, zeroMask := 51113456,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 52656624,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 520, zeroMask := 53209584,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk031_valid :
    List.Forall StratumCertificate.Valid certificateChunk031 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk032 : List StratumCertificate := [
  { stratum :=
      { activeMask := 522, zeroMask := 16899576,
        component := 35 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 24 (some 14), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 522, zeroMask := 50945464,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 37, .chain 38, .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 522, zeroMask := 17419704,
        component := 34 }
    witnesses := [.chain 32, .chain 37, .chain 38, .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 522, zeroMask := 50421232,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 522, zeroMask := 50974192,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 8 (some 4), .killed 4 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 4 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk032_valid :
    List.Forall StratumCertificate.Valid certificateChunk032 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk033 : List StratumCertificate := [
  { stratum :=
      { activeMask := 524, zeroMask := 53172401,
        component := 43 }
    witnesses := [.killed 19 (some 7), .chain 36, .chain 37, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 524, zeroMask := 53201073,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 0 (some 17), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 524, zeroMask := 53180592,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 524, zeroMask := 53209264,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk033_valid :
    List.Forall StratumCertificate.Valid certificateChunk033 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk034 : List StratumCertificate := [
  { stratum :=
      { activeMask := 526, zeroMask := 53042352,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 526, zeroMask := 53071024,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk034_valid :
    List.Forall StratumCertificate.Valid certificateChunk034 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
