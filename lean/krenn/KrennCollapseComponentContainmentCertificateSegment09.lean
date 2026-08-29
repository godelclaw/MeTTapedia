import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 157 through 171.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk157 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4104, zeroMask := 1286137,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 3382265,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 1547641,
        component := 51 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 3643769,
        component := 51 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35332025,
        component := 51 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 1806265,
        component := 34 }
    witnesses := [.killed 17 (some 0), .chain 37, .killed 0 (some 17), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37428153,
        component := 51 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 3902393,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 37, .killed 0 (some 17), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35593529,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 2067769,
        component := 35 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 18 (some 17), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37689657,
        component := 51 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 18), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 4163897,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 34807793,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35360753,
        component := 33 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 4), .killed 25 (some 4), .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 36903921,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37456881,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35069297,
        component := 49 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 4), .killed 10 (some 4), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35622257,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 25 (some 4), .killed 5 (some 0), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37165425,
        component := 43 }
    witnesses := [.killed 6 (some 18), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37718385,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 4 (some 21), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 4 (some 21), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 1294328,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 3390456,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 1555960,
        component := 64 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 3652088,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35340216,
        component := 64 }
    witnesses := [.killed 9 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 1814456,
        component := 34 }
    witnesses := [.killed 17 (some 13), .chain 37, .killed 13 (some 17), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37436344,
        component := 64 }
    witnesses := [.killed 9 (some 21), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 3910584,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 37, .killed 13 (some 17), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35601848,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 2076088,
        component := 34 }
    witnesses := [.killed 17 (some 13), .chain 37, .killed 13 (some 17), .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37697976,
        component := 64 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 4172216,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .chain 37, .killed 13 (some 17), .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 34815984,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35368944,
        component := 33 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 4), .killed 25 (some 4), .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 36912112,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37465072,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35077616,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 4), .killed 10 (some 4), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 35630576,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 25 (some 4), .killed 5 (some 7), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37173744,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 4), .killed 21 (some 4), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4104, zeroMask := 37726704,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk157_valid :
    List.Forall StratumCertificate.Valid certificateChunk157 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk158 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4105, zeroMask := 1555800,
        component := 64 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 3651928,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 35601688,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 2075928,
        component := 35 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 18), .killed 13 (some 18), .chain 5, .killed 18 (some 17), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 37697816,
        component := 64 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 18), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 4172056,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 21 (some 18), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 35077456,
        component := 62 }
    witnesses := [.killed 25 (some 10), .killed 25 (some 4), .killed 10 (some 4), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 35630416,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 25 (some 4), .chain 5, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 37173584,
        component := 62 }
    witnesses := [.killed 25 (some 21), .killed 25 (some 4), .killed 21 (some 4), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4105, zeroMask := 37726544,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 4 (some 8), .killed 25 (some 4), .killed 21 (some 4), .killed 18 (some 8), .killed 13 (some 4), .killed 13 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 21 (some 4), .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 4 (some 21), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 4 (some 21), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk158_valid :
    List.Forall StratumCertificate.Valid certificateChunk158 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk159 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4106, zeroMask := 1155064,
        component := 35 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 1416696,
        component := 37 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 3 (some 4), .killed 5 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 35200952,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 37, .chain 38, .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 1675192,
        component := 34 }
    witnesses := [.chain 32, .chain 37, .chain 38, .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 35462584,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 37, .chain 38, .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 1936824,
        component := 34 }
    witnesses := [.chain 32, .chain 37, .chain 38, .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 34676720,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 35229680,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 4), .killed 25 (some 4), .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .killed 9 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 34938352,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 18 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 18 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4106, zeroMask := 35491312,
        component := 37 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 25 (some 4), .killed 5 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk159_valid :
    List.Forall StratumCertificate.Valid certificateChunk159 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk160 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4108, zeroMask := 37427889,
        component := 43 }
    witnesses := [.killed 19 (some 7), .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37456561,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 0 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37689393,
        component := 43 }
    witnesses := [.killed 19 (some 18), .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37718065,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 17), .killed 21 (some 4), .killed 18 (some 17), .killed 21 (some 4), .killed 18 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37436080,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37464752,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37697712,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4108, zeroMask := 37726384,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk160_valid :
    List.Forall StratumCertificate.Valid certificateChunk160 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk161 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4109, zeroMask := 37697552,
        component := 53 }
    witnesses := [.killed 19 (some 18), .killed 18 (some 19), .chain 74, .chain 5, .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4109, zeroMask := 37726224,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 19 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 21 (some 18), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .killed 18 (some 19), .killed 13 (some 4), .killed 13 (some 17), .killed 21 (some 4), .killed 18 (some 17), .killed 21 (some 4), .killed 18 (some 15), .chain 74, .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk161_valid :
    List.Forall StratumCertificate.Valid certificateChunk161 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk162 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4110, zeroMask := 37297840,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4110, zeroMask := 37326512,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4110, zeroMask := 37559472,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4110, zeroMask := 37588144,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk162_valid :
    List.Forall StratumCertificate.Valid certificateChunk162 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk163 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4112, zeroMask := 1286119,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 1806311,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11640551,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12160743,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3381991,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3902183,
        component := 41 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 1547623,
        component := 49 }
    witnesses := [.killed 15 (some 10), .chain 20, .killed 10 (some 15), .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 2067815,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .chain 20, .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11902055,
        component := 15 }
    witnesses := [.killed 12 (some 5), .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 12), .chain 20, .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12422247,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 21 (some 18), .killed 6 (some 18), .killed 5 (some 18), .chain 20, .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3643495,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 18), .killed 6 (some 18), .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 4163687,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 1555783,
        component := 62 }
    witnesses := [.killed 15 (some 10), .chain 20, .killed 10 (some 15), .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 2075975,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .chain 20, .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11910215,
        component := 15 }
    witnesses := [.killed 12 (some 13), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 12), .chain 20, .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 12), .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12430407,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .chain 20, .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3651655,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 13), .killed 0 (some 15), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 21), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 12), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .chain 20, .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 12 (some 17), .killed 12 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 4171847,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .chain 20, .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 9543653,
        component := 15 }
    witnesses := [.killed 12 (some 5), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 10063845,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11770853,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12291045,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 9805157,
        component := 16 }
    witnesses := [.killed 12 (some 5), .chain 20, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 10325349,
        component := 16 }
    witnesses := [.killed 19 (some 5), .chain 20, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12032357,
        component := 49 }
    witnesses := [.killed 15 (some 21), .chain 20, .killed 21 (some 15), .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12552549,
        component := 17 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 20, .killed 5 (some 17), .killed 21 (some 17), .killed 21 (some 15), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 9813317,
        component := 16 }
    witnesses := [.killed 12 (some 13), .chain 20, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 10333509,
        component := 16 }
    witnesses := [.killed 19 (some 13), .chain 20, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12040517,
        component := 62 }
    witnesses := [.killed 15 (some 21), .chain 20, .killed 21 (some 15), .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12560709,
        component := 17 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 20, .killed 13 (some 17), .killed 21 (some 17), .killed 21 (some 15), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 1294278,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 1814470,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 1555910,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 2076102,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11648710,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12168902,
        component := 20 }
    witnesses := [.killed 10 (some 15), .chain 20, .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3390150,
        component := 66 }
    witnesses := [.chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3910342,
        component := 41 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11910342,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12430534,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .killed 21 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 3651782,
        component := 61 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 18), .killed 15 (some 18), .chain 20, .killed 21 (some 15), .killed 18 (some 15), .chain 0, .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 4171974,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 9551812,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 15), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 23 (some 9), .killed 23 (some 8), .killed 13 (some 9), .killed 13 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 10072004,
        component := 19 }
    witnesses := [.killed 8 (some 9), .chain 20, .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 11779012,
        component := 65 }
    witnesses := [.killed 8 (some 23), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12299204,
        component := 20 }
    witnesses := [.killed 17 (some 15), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 9813444,
        component := 37 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .chain 20, .killed 2 (some 7), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 10333636,
        component := 19 }
    witnesses := [.killed 8 (some 18), .chain 20, .killed 18 (some 6), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12040644,
        component := 62 }
    witnesses := [.killed 15 (some 21), .chain 20, .killed 21 (some 15), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4112, zeroMask := 12560836,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 21 (some 19), .killed 18 (some 8), .killed 13 (some 17), .killed 13 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk163_valid :
    List.Forall StratumCertificate.Valid certificateChunk163 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk164 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4114, zeroMask := 1155046,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 1675238,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 1416678,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 1936870,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 3251942,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 3772134,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 3513574,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4114, zeroMask := 4033766,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk164_valid :
    List.Forall StratumCertificate.Valid certificateChunk164 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk165 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4116, zeroMask := 12160677,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12290725,
        component := 18 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12422181,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 21 (some 18), .killed 19 (some 18), .killed 5 (some 18), .chain 20, .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 5 (some 21), .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12552229,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12430341,
        component := 15 }
    witnesses := [.killed 19 (some 13), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .chain 20, .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .killed 19 (some 21), .killed 18 (some 21), .killed 13 (some 21), .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12560389,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 21 (some 0), .killed 23 (some 0), .chain 20, .killed 21 (some 0), .killed 18 (some 0), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 23 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12168836,
        component := 20 }
    witnesses := [.killed 10 (some 15), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12298884,
        component := 20 }
    witnesses := [.killed 17 (some 15), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12430468,
        component := 19 }
    witnesses := [.killed 21 (some 18), .chain 20, .killed 18 (some 21), .killed 18 (some 21), .chain 10, .chain 0, .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4116, zeroMask := 12560516,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 23 (some 7), .chain 20, .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 23 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 23), .killed 2 (some 23), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk165_valid :
    List.Forall StratumCertificate.Valid certificateChunk165 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk166 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4120, zeroMask := 1286113,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 1806305,
        component := 33 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 9), .chain 20, .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 3382241,
        component := 52 }
    witnesses := [.killed 6 (some 7), .chain 20, .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 3902433,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 20, .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 1547617,
        component := 49 }
    witnesses := [.killed 15 (some 10), .chain 20, .killed 10 (some 15), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 2067809,
        component := 37 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .chain 20, .killed 5 (some 0), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 3643745,
        component := 49 }
    witnesses := [.killed 15 (some 21), .chain 20, .killed 21 (some 15), .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 4163937,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 1294304,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 1814496,
        component := 33 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 9), .chain 20, .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 3390432,
        component := 65 }
    witnesses := [.killed 8 (some 5), .killed 6 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 3910624,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 20, .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 8 (some 6), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 1555936,
        component := 62 }
    witnesses := [.killed 15 (some 10), .chain 20, .killed 10 (some 15), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 2076128,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .chain 20, .killed 5 (some 7), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 3652064,
        component := 62 }
    witnesses := [.killed 15 (some 21), .chain 20, .killed 21 (some 15), .killed 5 (some 7), .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4120, zeroMask := 4172256,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 8), .killed 5 (some 17), .killed 5 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 19 (some 7), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk166_valid :
    List.Forall StratumCertificate.Valid certificateChunk166 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk167 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4121, zeroMask := 1555776,
        component := 62 }
    witnesses := [.killed 15 (some 10), .chain 20, .killed 10 (some 15), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4121, zeroMask := 2075968,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .chain 20, .chain 5, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4121, zeroMask := 3651904,
        component := 62 }
    witnesses := [.killed 15 (some 21), .chain 20, .killed 21 (some 15), .chain 5, .chain 37, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4121, zeroMask := 4172096,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 8), .chain 20, .killed 21 (some 19), .killed 18 (some 8), .killed 13 (some 17), .killed 13 (some 8), .killed 21 (some 17), .killed 18 (some 8), .killed 21 (some 15), .killed 18 (some 8), .killed 6 (some 8), .chain 5, .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 6), .killed 19 (some 15), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 19 (some 21), .killed 18 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk167_valid :
    List.Forall StratumCertificate.Valid certificateChunk167 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk168 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4122, zeroMask := 1155040,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4122, zeroMask := 1675232,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 9), .chain 20, .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 9 (some 6), .killed 9 (some 6), .killed 8 (some 6), .chain 0, .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4122, zeroMask := 1416672,
        component := 37 }
    witnesses := [.chain 32, .killed 12 (some 5), .chain 20, .killed 5 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4122, zeroMask := 1936864,
        component := 37 }
    witnesses := [.chain 32, .killed 19 (some 5), .chain 20, .killed 5 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk168_valid :
    List.Forall StratumCertificate.Valid certificateChunk168 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk169 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4124, zeroMask := 3902113,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 20, .chain 86, .chain 36, .chain 37, .killed 0 (some 17), .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4124, zeroMask := 4163617,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .chain 20, .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 86, .chain 36, .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4124, zeroMask := 3910304,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 20, .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4124, zeroMask := 4171936,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 5), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .chain 20, .killed 5 (some 19), .killed 5 (some 19), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 7), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 21), .killed 19 (some 7), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk169_valid :
    List.Forall StratumCertificate.Valid certificateChunk169 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk170 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4125, zeroMask := 4171776,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 21 (some 18), .chain 62, .chain 20, .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .chain 74, .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 21), .killed 18 (some 21), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk170_valid :
    List.Forall StratumCertificate.Valid certificateChunk170 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk171 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4126, zeroMask := 3772064,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 20, .chain 86, .chain 36, .chain 37, .chain 38, .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4126, zeroMask := 4033696,
        component := 33 }
    witnesses := [.chain 32, .killed 21 (some 18), .chain 20, .killed 18 (some 21), .killed 18 (some 21), .chain 86, .chain 36, .chain 37, .chain 38, .killed 18 (some 21), .killed 18 (some 21), .chain 10, .chain 0, .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk171_valid :
    List.Forall StratumCertificate.Valid certificateChunk171 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
