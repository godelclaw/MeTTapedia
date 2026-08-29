import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 247 through 267.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk247 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8192, zeroMask := 17981423,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28335855,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20077295,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 18243439,
        component := 50 }
    witnesses := [.killed 6 (some 18), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28597871,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 18), .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20339311,
        component := 52 }
    witnesses := [.killed 6 (some 18), .killed 3 (some 14), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 18505647,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28860079,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20601519,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 18767663,
        component := 50 }
    witnesses := [.killed 19 (some 18), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 29122095,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 18), .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20863535,
        component := 52 }
    witnesses := [.killed 19 (some 18), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 18251599,
        component := 63 }
    witnesses := [.killed 6 (some 18), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22429519,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28606031,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32783951,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20347471,
        component := 65 }
    witnesses := [.killed 0 (some 14), .killed 6 (some 18), .killed 6 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24525391,
        component := 60 }
    witnesses := [.killed 6 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 18775823,
        component := 63 }
    witnesses := [.killed 19 (some 18), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22953743,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 29130255,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33308175,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20871695,
        component := 65 }
    witnesses := [.killed 0 (some 14), .killed 19 (some 18), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 25049615,
        component := 60 }
    witnesses := [.killed 19 (some 18), .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22159339,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32513771,
        component := 29 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24255211,
        component := 48 }
    witnesses := [.killed 6 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22421355,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32775787,
        component := 29 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 23), .killed 10 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24517227,
        component := 48 }
    witnesses := [.killed 6 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22683563,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33037995,
        component := 30 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 12), .killed 10 (some 12), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24779435,
        component := 48 }
    witnesses := [.killed 19 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22945579,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33300011,
        component := 29 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 25041451,
        component := 48 }
    witnesses := [.killed 19 (some 18), .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 26238957,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28466157,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 26500973,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 18), .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28728173,
        component := 50 }
    witnesses := [.killed 6 (some 18), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 26763181,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28990381,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 27025197,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 18), .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 29252397,
        component := 50 }
    witnesses := [.killed 19 (some 18), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 26509133,
        component := 9 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30687053,
        component := 17 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 9), .killed 3 (some 9), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .chain 3, .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28736333,
        component := 63 }
    witnesses := [.killed 6 (some 18), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32914253,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 6 (some 18), .killed 6 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 27033357,
        component := 9 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 19 (some 18), .killed 13 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 31211277,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 18), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 29260557,
        component := 63 }
    witnesses := [.killed 19 (some 18), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33438477,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 19 (some 18), .killed 13 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30416873,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32644073,
        component := 52 }
    witnesses := [.killed 6 (some 7), .killed 3 (some 22), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30678889,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 23), .killed 10 (some 6), .killed 9 (some 23), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 6), .killed 10 (some 22), .killed 10 (some 6), .killed 9 (some 22), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32906089,
        component := 49 }
    witnesses := [.killed 9 (some 21), .killed 3 (some 22), .killed 3 (some 9), .killed 23 (some 22), .killed 24 (some 22), .killed 0 (none), .killed 20 (some 9), .killed 18 (none), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30941097,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 9 (some 7), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 9 (some 7), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33168297,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 31203113,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33430313,
        component := 52 }
    witnesses := [.killed 19 (some 18), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 17989582,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22167502,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28344014,
        component := 41 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32521934,
        component := 41 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20085454,
        component := 66 }
    witnesses := [.killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24263374,
        component := 60 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 18513806,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22691726,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28868238,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33046158,
        component := 20 }
    witnesses := [.killed 10 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 20609678,
        component := 65 }
    witnesses := [.killed 19 (some 14), .killed 19 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24787598,
        component := 60 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22167530,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32521962,
        component := 29 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24263402,
        component := 60 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 22691754,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33046186,
        component := 30 }
    witnesses := [.killed 23 (some 13), .killed 10 (some 12), .killed 10 (some 12), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 24787626,
        component := 60 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 26247116,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 14), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30425036,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28474316,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32652236,
        component := 65 }
    witnesses := [.killed 8 (some 23), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 23 (some 2), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 26771340,
        component := 12 }
    witnesses := [.killed 10 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30949260,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 13 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 23 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 7), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 9 (some 7), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 28998540,
        component := 12 }
    witnesses := [.killed 17 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33176460,
        component := 20 }
    witnesses := [.killed 17 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30425064,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 32652264,
        component := 65 }
    witnesses := [.killed 8 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 30949288,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 23), .killed 10 (some 7), .killed 10 (some 23), .killed 9 (some 7), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 5 (some 7), .killed 12 (some 22), .killed 10 (some 7), .killed 10 (some 22), .killed 9 (some 7), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8192, zeroMask := 33176488,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk247_valid :
    List.Forall StratumCertificate.Valid certificateChunk247 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk248 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8193, zeroMask := 22429514,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 6 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 32783946,
        component := 29 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 10), .chain 5, .killed 12 (some 6), .killed 10 (some 23), .killed 10 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 24525386,
        component := 60 }
    witnesses := [.killed 6 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 22953738,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .killed 19 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 33308170,
        component := 29 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 10), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 25049610,
        component := 60 }
    witnesses := [.killed 19 (some 18), .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 30687048,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 10), .killed 6 (some 9), .killed 6 (some 8), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 6), .killed 10 (some 23), .killed 10 (some 6), .killed 9 (some 23), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 6), .killed 10 (some 22), .killed 10 (some 6), .killed 9 (some 22), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 32914248,
        component := 62 }
    witnesses := [.killed 9 (some 21), .killed 3 (some 22), .killed 3 (some 9), .chain 5, .killed 23 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 18 (none), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 31211272,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 18), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 19 (some 18), .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 9), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8193, zeroMask := 33438472,
        component := 65 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk248_valid :
    List.Forall StratumCertificate.Valid certificateChunk248 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk249 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8194, zeroMask := 17850350,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 19947246,
        component := 41 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 18374574,
        component := 39 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 1 (some 2), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 20471470,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 22028266,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 24125162,
        component := 29 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (none), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 22552490,
        component := 31 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8194, zeroMask := 24649386,
        component := 30 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk249_valid :
    List.Forall StratumCertificate.Valid certificateChunk249 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk250 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8200, zeroMask := 17981417,
        component := 50 }
    witnesses := [.killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 20077545,
        component := 50 }
    witnesses := [.killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 18243433,
        component := 50 }
    witnesses := [.killed 6 (some 18), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 20339561,
        component := 50 }
    witnesses := [.killed 6 (some 18), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 18505641,
        component := 50 }
    witnesses := [.killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 20601769,
        component := 50 }
    witnesses := [.killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 18767657,
        component := 50 }
    witnesses := [.killed 19 (some 18), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 20863785,
        component := 50 }
    witnesses := [.killed 19 (some 18), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 17989608,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 20085736,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 18513832,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8200, zeroMask := 20609960,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk250_valid :
    List.Forall StratumCertificate.Valid certificateChunk250 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk251 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8201, zeroMask := 18251592,
        component := 63 }
    witnesses := [.killed 6 (some 18), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8201, zeroMask := 20347720,
        component := 63 }
    witnesses := [.killed 6 (some 18), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8201, zeroMask := 18775816,
        component := 63 }
    witnesses := [.killed 19 (some 18), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8201, zeroMask := 20871944,
        component := 63 }
    witnesses := [.killed 19 (some 18), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk251_valid :
    List.Forall StratumCertificate.Valid certificateChunk251 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk252 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8202, zeroMask := 17850344,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8202, zeroMask := 18374568,
        component := 39 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk252_valid :
    List.Forall StratumCertificate.Valid certificateChunk252 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk253 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8320, zeroMask := 17981231,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 28335663,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 20077103,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 17989391,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 22167311,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 28343823,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 32521743,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 20085263,
        component := 65 }
    witnesses := [.killed 0 (some 14), .chain 8, .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 24263183,
        component := 60 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 22159147,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 32513579,
        component := 29 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 9 (none), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 24255019,
        component := 48 }
    witnesses := [.chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 26238765,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 28465965,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 26246925,
        component := 9 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 30424845,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 23), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 28474125,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 32652045,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 30416681,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8320, zeroMask := 32643881,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk253_valid :
    List.Forall StratumCertificate.Valid certificateChunk253 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk254 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8321, zeroMask := 22167306,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8321, zeroMask := 32521738,
        component := 29 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (none), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8321, zeroMask := 24263178,
        component := 60 }
    witnesses := [.chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 8321, zeroMask := 30424840,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 9), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 8321, zeroMask := 32652040,
        component := 65 }
    witnesses := [.killed 8 (some 23), .chain 8, .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk254_valid :
    List.Forall StratumCertificate.Valid certificateChunk254 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk255 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8328, zeroMask := 17981225,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8328, zeroMask := 20077353,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk255_valid :
    List.Forall StratumCertificate.Valid certificateChunk255 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk256 : List StratumCertificate := [
  { stratum :=
      { activeMask := 8329, zeroMask := 17989384,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 8329, zeroMask := 20085512,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .chain 3, .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk256_valid :
    List.Forall StratumCertificate.Valid certificateChunk256 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk257 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9216, zeroMask := 28854959,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 29116975,
        component := 18 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 29125135,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33303055,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33032875,
        component := 30 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33294891,
        component := 29 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 9 (none), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 28855213,
        component := 9 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 29117229,
        component := 9 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 18), .killed 5 (some 18), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 29125389,
        component := 9 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33303309,
        component := 18 }
    witnesses := [.killed 19 (some 13), .chain 7, .killed 19 (some 18), .killed 13 (some 18), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33033129,
        component := 42 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33295145,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 23), .chain 7, .killed 0 (some 5), .killed 0 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 28863118,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33041038,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33041066,
        component := 30 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 28863372,
        component := 12 }
    witnesses := [.chain 7, .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33041292,
        component := 20 }
    witnesses := [.chain 7, .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9216, zeroMask := 33041320,
        component := 42 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk257_valid :
    List.Forall StratumCertificate.Valid certificateChunk257 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk258 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9217, zeroMask := 33303050,
        component := 29 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 9 (none), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 9217, zeroMask := 33303304,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 19 (some 23), .killed 13 (some 23), .chain 7, .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 8 (some 9), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 23 (some 18), .killed 21 (some 9), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 23), .killed 19 (some 23), .killed 18 (some 23), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 18 (some 22), .killed 19 (some 22), .killed 18 (some 22), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk258_valid :
    List.Forall StratumCertificate.Valid certificateChunk258 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk259 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9218, zeroMask := 20466350,
        component := 42 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 9218, zeroMask := 24644266,
        component := 30 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk259_valid :
    List.Forall StratumCertificate.Valid certificateChunk259 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk260 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9226, zeroMask := 20466600,
        component := 39 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk260_valid :
    List.Forall StratumCertificate.Valid certificateChunk260 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk261 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9280, zeroMask := 28330703,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 32508623,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 28592719,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 32770639,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 28330957,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 32508877,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 28592973,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9280, zeroMask := 32770893,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk261_valid :
    List.Forall StratumCertificate.Valid certificateChunk261 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk262 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9282, zeroMask := 19942094,
        component := 41 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 9282, zeroMask := 24120014,
        component := 41 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 3 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk262_valid :
    List.Forall StratumCertificate.Valid certificateChunk262 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk263 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9283, zeroMask := 24382026,
        component := 29 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (none), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk263_valid :
    List.Forall StratumCertificate.Valid certificateChunk263 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk264 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9291, zeroMask := 20204360,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 9), .killed 6 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 6), .chain 39, .killed 18 (some 6), .killed 9 (some 14), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .killed 18 (some 6), .chain 43, .killed 18 (some 6), .killed 9 (some 14), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk264_valid :
    List.Forall StratumCertificate.Valid certificateChunk264 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk265 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9408, zeroMask := 28330511,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9408, zeroMask := 32508431,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9408, zeroMask := 28330765,
        component := 9 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .chain 3, .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 9408, zeroMask := 32508685,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk265_valid :
    List.Forall StratumCertificate.Valid certificateChunk265 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk266 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9411, zeroMask := 24119818,
        component := 29 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (none), .chain 8, .chain 9, .chain 59, .chain 5, .chain 75, .chain 39, .chain 77, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .chain 3, .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk266_valid :
    List.Forall StratumCertificate.Valid certificateChunk266 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk267 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9419, zeroMask := 19942152,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .chain 3, .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk267_valid :
    List.Forall StratumCertificate.Valid certificateChunk267 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
