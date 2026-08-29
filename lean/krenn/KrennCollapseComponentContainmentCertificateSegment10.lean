import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 172 through 204.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk172 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4160, zeroMask := 1282015,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 11636447,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 3377887,
        component := 41 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 3 (some 4), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 1543519,
        component := 37 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 3 (some 4), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 11897951,
        component := 15 }
    witnesses := [.chain 6, .killed 21 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 3639391,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 34836439,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 45190871,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 36932311,
        component := 21 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 35097943,
        component := 37 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 25 (some 4), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 45452375,
        component := 2 }
    witnesses := [.chain 6, .killed 10 (some 15), .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 37193815,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 21 (some 0), .killed 18 (some 0), .killed 21 (some 4), .killed 18 (some 17), .killed 21 (some 4), .killed 18 (some 17), .killed 21 (some 4), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 9539549,
        component := 11 }
    witnesses := [.chain 6, .killed 6 (some 7), .killed 6 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 11766749,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 9801053,
        component := 16 }
    witnesses := [.chain 6, .killed 3 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 12028253,
        component := 10 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 6 (some 18), .killed 6 (some 18), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 43093973,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 4), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 45321173,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 43355477,
        component := 16 }
    witnesses := [.chain 6, .killed 25 (some 4), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4160, zeroMask := 45582677,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 18), .killed 6 (some 18), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk172_valid :
    List.Forall StratumCertificate.Valid certificateChunk172 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk173 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4162, zeroMask := 1150942,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 1412574,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 3247838,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 3509470,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 3 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 34705366,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 34966998,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 36802262,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4162, zeroMask := 37063894,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 4), .killed 25 (some 4), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk173_valid :
    List.Forall StratumCertificate.Valid certificateChunk173 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk174 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4171, zeroMask := 1412440,
        component := 37 }
    witnesses := [.chain 32, .chain 6, .killed 3 (some 4), .chain 5, .chain 37, .chain 38, .chain 41, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4171, zeroMask := 34966864,
        component := 37 }
    witnesses := [.chain 32, .chain 6, .killed 25 (some 4), .chain 5, .chain 37, .chain 38, .chain 41, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk174_valid :
    List.Forall StratumCertificate.Valid certificateChunk174 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk175 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4176, zeroMask := 1281991,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 11636423,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 3377863,
        component := 41 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .chain 20, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 1543495,
        component := 37 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 20, .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 11897927,
        component := 15 }
    witnesses := [.chain 6, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .chain 20, .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 3639367,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .chain 20, .killed 21 (some 0), .killed 18 (some 0), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 9539525,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 9), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 11766725,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .chain 20, .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 9801029,
        component := 16 }
    witnesses := [.chain 6, .chain 20, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4176, zeroMask := 12028229,
        component := 17 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 20, .killed 21 (some 17), .killed 21 (some 17), .killed 21 (some 15), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk175_valid :
    List.Forall StratumCertificate.Valid certificateChunk175 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk176 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4178, zeroMask := 1150918,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4178, zeroMask := 1412550,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4178, zeroMask := 3247814,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 9), .chain 20, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4178, zeroMask := 3509446,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 18), .chain 20, .chain 0, .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk176_valid :
    List.Forall StratumCertificate.Valid certificateChunk176 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk177 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4187, zeroMask := 1412416,
        component := 37 }
    witnesses := [.chain 32, .chain 6, .chain 20, .chain 5, .chain 37, .chain 38, .chain 41, .chain 0, .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk177_valid :
    List.Forall StratumCertificate.Valid certificateChunk177 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk178 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4224, zeroMask := 1285951,
        component := 51 }
    witnesses := [.killed 9 (some 10), .chain 8, .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 34807615,
        component := 51 }
    witnesses := [.killed 9 (some 10), .chain 8, .killed 1 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 11640383,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 45162047,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 3381823,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 4), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 36903487,
        component := 43 }
    witnesses := [.chain 8, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 1294111,
        component := 64 }
    witnesses := [.killed 9 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 34815775,
        component := 64 }
    witnesses := [.killed 9 (some 10), .chain 8, .killed 2 (some 0), .killed 1 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 11648543,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 45170207,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 3389983,
        component := 65 }
    witnesses := [.killed 0 (some 4), .chain 8, .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 36911647,
        component := 53 }
    witnesses := [.chain 8, .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 9543485,
        component := 11 }
    witnesses := [.killed 12 (some 5), .chain 8, .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 43065149,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 8, .killed 5 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 11770685,
        component := 51 }
    witnesses := [.killed 9 (some 21), .chain 8, .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 45292349,
        component := 51 }
    witnesses := [.killed 9 (some 21), .chain 8, .killed 23 (some 2), .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 9551645,
        component := 11 }
    witnesses := [.killed 12 (some 13), .chain 8, .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 43073309,
        component := 10 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .killed 9 (some 12), .killed 9 (some 10), .chain 8, .killed 13 (some 12), .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 11778845,
        component := 64 }
    witnesses := [.killed 9 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4224, zeroMask := 45300509,
        component := 64 }
    witnesses := [.killed 9 (some 21), .chain 8, .killed 2 (some 0), .killed 23 (some 2), .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk178_valid :
    List.Forall StratumCertificate.Valid certificateChunk178 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk179 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4228, zeroMask := 45162037,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4228, zeroMask := 45292085,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 8, .killed 5 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4228, zeroMask := 45170197,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4228, zeroMask := 45300245,
        component := 2 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk179_valid :
    List.Forall StratumCertificate.Valid certificateChunk179 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk180 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4232, zeroMask := 1285945,
        component := 51 }
    witnesses := [.killed 9 (some 10), .chain 8, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4232, zeroMask := 34807609,
        component := 51 }
    witnesses := [.killed 9 (some 10), .chain 8, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4232, zeroMask := 3382073,
        component := 51 }
    witnesses := [.killed 9 (some 21), .chain 8, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4232, zeroMask := 36903737,
        component := 51 }
    witnesses := [.killed 9 (some 21), .chain 8, .chain 37, .chain 0, .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk180_valid :
    List.Forall StratumCertificate.Valid certificateChunk180 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk181 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4233, zeroMask := 1294104,
        component := 64 }
    witnesses := [.killed 9 (some 10), .chain 8, .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4233, zeroMask := 34815768,
        component := 64 }
    witnesses := [.killed 9 (some 10), .chain 8, .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4233, zeroMask := 3390232,
        component := 64 }
    witnesses := [.killed 9 (some 21), .chain 8, .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4233, zeroMask := 36911896,
        component := 64 }
    witnesses := [.killed 9 (some 21), .chain 8, .chain 5, .chain 37, .chain 0, .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk181_valid :
    List.Forall StratumCertificate.Valid certificateChunk181 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk182 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4236, zeroMask := 36903473,
        component := 43 }
    witnesses := [.chain 8, .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk182_valid :
    List.Forall StratumCertificate.Valid certificateChunk182 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk183 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4237, zeroMask := 36911632,
        component := 53 }
    witnesses := [.chain 8, .chain 66, .chain 74, .chain 5, .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk183_valid :
    List.Forall StratumCertificate.Valid certificateChunk183 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk184 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4244, zeroMask := 11640357,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4244, zeroMask := 11770405,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 8, .killed 5 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4244, zeroMask := 11648517,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4244, zeroMask := 11778565,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk184_valid :
    List.Forall StratumCertificate.Valid certificateChunk184 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk185 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4252, zeroMask := 3381793,
        component := 52 }
    witnesses := [.chain 8, .chain 20, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk185_valid :
    List.Forall StratumCertificate.Valid certificateChunk185 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk186 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4253, zeroMask := 3389952,
        component := 65 }
    witnesses := [.chain 51, .chain 8, .chain 62, .chain 20, .chain 66, .chain 74, .chain 5, .chain 86, .chain 36, .chain 37, .chain 10, .chain 0, .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk186_valid :
    List.Forall StratumCertificate.Valid certificateChunk186 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk187 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4288, zeroMask := 1281823,
        component := 35 }
    witnesses := [.killed 17 (some 0), .chain 6, .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 17), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4288, zeroMask := 11636255,
        component := 18 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .killed 3 (some 4), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4288, zeroMask := 3377695,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 0), .killed 21 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 21), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4288, zeroMask := 9539357,
        component := 11 }
    witnesses := [.chain 6, .chain 8, .chain 9, .chain 0, .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4288, zeroMask := 11766557,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .killed 3 (some 4), .killed 8 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk187_valid :
    List.Forall StratumCertificate.Valid certificateChunk187 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk188 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4292, zeroMask := 45190677,
        component := 2 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4292, zeroMask := 45320725,
        component := 2 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk188_valid :
    List.Forall StratumCertificate.Valid certificateChunk188 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk189 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4299, zeroMask := 1150744,
        component := 35 }
    witnesses := [.chain 32, .chain 6, .chain 8, .chain 9, .chain 5, .chain 75, .chain 37, .chain 38, .chain 41, .chain 87, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk189_valid :
    List.Forall StratumCertificate.Valid certificateChunk189 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk190 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4303, zeroMask := 36802064,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 10), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 15 (some 4), .chain 8, .chain 9, .killed 15 (some 10), .killed 21 (some 9), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .chain 66, .killed 21 (some 4), .chain 68, .killed 21 (some 4), .chain 70, .killed 10 (some 4), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk190_valid :
    List.Forall StratumCertificate.Valid certificateChunk190 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk191 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4308, zeroMask := 11636229,
        component := 18 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4308, zeroMask := 11766277,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .chain 20, .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk191_valid :
    List.Forall StratumCertificate.Valid certificateChunk191 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk192 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4319, zeroMask := 3247616,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 10), .killed 21 (some 9), .chain 51, .chain 53, .chain 55, .killed 15 (some 10), .chain 8, .chain 9, .killed 15 (some 10), .killed 21 (some 9), .chain 62, .chain 20, .killed 21 (some 9), .chain 66, .killed 21 (some 9), .chain 68, .killed 21 (some 9), .chain 70, .killed 10 (some 9), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 86, .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 10, .chain 0, .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk192_valid :
    List.Forall StratumCertificate.Valid certificateChunk192 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk193 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4608, zeroMask := 237055,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 10591487,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 2332927,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 34282943,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 1 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 757183,
        component := 34 }
    witnesses := [.killed 17 (some 0), .killed 1 (some 2), .killed 0 (some 2), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44637375,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 11111615,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 21 (some 4), .killed 19 (some 7), .killed 5 (some 7), .killed 3 (some 4), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 7), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 36378815,
        component := 43 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 2853055,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 3 (some 4), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 33758711,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 34311671,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44113143,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44666103,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 35854583,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 36407543,
        component := 21 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 8494589,
        component := 11 }
    witnesses := [.killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 10721789,
        component := 51 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 42540477,
        component := 10 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 9014717,
        component := 11 }
    witnesses := [.killed 19 (some 5), .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44767677,
        component := 51 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 7), .killed 23 (some 2), .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 11241917,
        component := 10 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 19 (some 7), .killed 5 (some 7), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 42016245,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 42569205,
        component := 15 }
    witnesses := [.killed 19 (some 5), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 25 (some 4), .killed 19 (some 7), .killed 25 (some 6), .killed 5 (some 7), .killed 4 (some 7), .killed 4 (some 6), .killed 4 (some 7), .killed 8 (some 6), .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44243445,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44796405,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 245214,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 10599646,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 2341086,
        component := 61 }
    witnesses := [.killed 15 (some 21), .killed 21 (some 4), .killed 15 (some 4), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 15), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 34291102,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 765342,
        component := 35 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 7), .killed 13 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44645534,
        component := 5 }
    witnesses := [.killed 10 (some 12), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 11119774,
        component := 19 }
    witnesses := [.killed 21 (some 4), .killed 3 (some 4), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 36386974,
        component := 53 }
    witnesses := [.killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 2861214,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 21), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 4), .killed 19 (some 4), .killed 13 (some 4), .killed 17 (some 4), .killed 15 (some 4), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 21 (some 7), .killed 4 (some 7), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 19), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 17), .killed 3 (some 4), .killed 3 (some 15), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 33766870,
        component := 61 }
    witnesses := [.killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 25 (some 4), .killed 10 (some 4), .killed 10 (some 8), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 34319830,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44121302,
        component := 21 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44674262,
        component := 5 }
    witnesses := [.killed 10 (some 15), .killed 1 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 35862742,
        component := 55 }
    witnesses := [.killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 36415702,
        component := 21 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 8502748,
        component := 35 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 6 (some 7), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 10729948,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 42548636,
        component := 13 }
    witnesses := [.killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 9022876,
        component := 14 }
    witnesses := [.chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44775836,
        component := 5 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 3), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 11250076,
        component := 13 }
    witnesses := [.killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 42024404,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 23 (some 4), .killed 23 (some 8), .killed 13 (some 4), .killed 13 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 42577364,
        component := 19 }
    witnesses := [.killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44251604,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 23 (some 2), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4608, zeroMask := 44804564,
        component := 5 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk193_valid :
    List.Forall StratumCertificate.Valid certificateChunk193 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk194 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4610, zeroMask := 105982,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 8 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 2202878,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 21 (some 4), .killed 3 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 34151870,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 1 (some 2), .killed 1 (some 2), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 626110,
        component := 34 }
    witnesses := [.chain 32, .killed 1 (some 2), .killed 1 (some 2), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 36248766,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 2723006,
        component := 33 }
    witnesses := [.chain 32, .killed 21 (some 4), .killed 3 (some 4), .killed 2 (some 21), .killed 2 (some 3), .killed 2 (some 4), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 33627638,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 4), .killed 2 (some 6), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 34180598,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 8 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 35724534,
        component := 21 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4610, zeroMask := 36277494,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 21 (some 4), .killed 25 (some 4), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk194_valid :
    List.Forall StratumCertificate.Valid certificateChunk194 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk195 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4612, zeroMask := 44637365,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44666037,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 10 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44767413,
        component := 2 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44796085,
        component := 2 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44645524,
        component := 5 }
    witnesses := [.killed 10 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44674196,
        component := 5 }
    witnesses := [.killed 10 (some 15), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44775572,
        component := 5 }
    witnesses := [.killed 17 (some 12), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4612, zeroMask := 44804244,
        component := 5 }
    witnesses := [.killed 17 (some 15), .chain 10, .killed 25 (none), .chain 0, .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk195_valid :
    List.Forall StratumCertificate.Valid certificateChunk195 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk196 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4616, zeroMask := 237049,
        component := 51 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 2333177,
        component := 51 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 34282937,
        component := 51 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 757177,
        component := 34 }
    witnesses := [.killed 17 (some 0), .chain 37, .killed 0 (some 17), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 36379065,
        component := 51 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 7), .chain 37, .chain 0, .killed 0 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 2853305,
        component := 40 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .chain 37, .killed 0 (some 17), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 33758705,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 0 (some 4), .killed 0 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 0), .killed 5 (some 0), .killed 4 (some 0), .killed 25 (some 4), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 34311665,
        component := 33 }
    witnesses := [.killed 17 (some 0), .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 35854833,
        component := 43 }
    witnesses := [.killed 6 (some 7), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 36407793,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 245240,
        component := 64 }
    witnesses := [.killed 15 (some 10), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 2341368,
        component := 64 }
    witnesses := [.killed 15 (some 21), .killed 6 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 34291128,
        component := 64 }
    witnesses := [.killed 25 (some 10), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 765368,
        component := 34 }
    witnesses := [.killed 17 (some 13), .chain 37, .killed 13 (some 17), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 36387256,
        component := 64 }
    witnesses := [.killed 25 (some 21), .killed 19 (some 7), .killed 5 (some 7), .chain 37, .chain 0, .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 2861496,
        component := 40 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 21), .killed 17 (some 21), .killed 15 (some 21), .chain 37, .killed 13 (some 17), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 33766896,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 34319856,
        component := 33 }
    witnesses := [.killed 17 (some 13), .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 35863024,
        component := 53 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 8 (some 6), .chain 37, .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4616, zeroMask := 36415984,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 8 (some 6), .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk196_valid :
    List.Forall StratumCertificate.Valid certificateChunk196 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk197 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4618, zeroMask := 105976,
        component := 35 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4618, zeroMask := 34151864,
        component := 40 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 37, .chain 38, .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4618, zeroMask := 626104,
        component := 34 }
    witnesses := [.chain 32, .chain 37, .chain 38, .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 4 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 4618, zeroMask := 33627632,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 5), .killed 25 (some 12), .killed 25 (some 12), .killed 25 (some 10), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 4 (some 7), .killed 25 (some 4), .killed 5 (some 4), .killed 5 (some 8), .killed 5 (some 4), .killed 5 (some 8), .killed 12 (some 4), .killed 12 (some 8), .killed 10 (some 4), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 25 (some 7), .killed 25 (some 6), .killed 4 (some 7), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 4618, zeroMask := 34180592,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 4), .killed 25 (some 4), .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 4), .killed 8 (some 6), .chain 37, .chain 38, .killed 25 (some 6), .killed 4 (some 6), .killed 8 (some 6), .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk197_valid :
    List.Forall StratumCertificate.Valid certificateChunk197 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk198 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4620, zeroMask := 36378801,
        component := 43 }
    witnesses := [.killed 19 (some 7), .chain 36, .chain 37, .chain 10, .killed 25 (none), .chain 0, .killed 0 (none), .killed 21 (none), .chain 1, .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 4 (none)] },
  { stratum :=
      { activeMask := 4620, zeroMask := 36407473,
        component := 22 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 0 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4620, zeroMask := 36386992,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4620, zeroMask := 36415664,
        component := 22 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk198_valid :
    List.Forall StratumCertificate.Valid certificateChunk198 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk199 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4622, zeroMask := 36248752,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4622, zeroMask := 36277424,
        component := 22 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .chain 0, .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk199_valid :
    List.Forall StratumCertificate.Valid certificateChunk199 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk200 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4656, zeroMask := 236775,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 8494311,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 756967,
        component := 38 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 9014503,
        component := 38 }
    witnesses := [.killed 23 (some 0), .killed 19 (some 5), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 244934,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 12 (some 13), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 8502470,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 765126,
        component := 38 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4656, zeroMask := 9022662,
        component := 38 }
    witnesses := [.killed 23 (some 13), .killed 19 (some 13), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk200_valid :
    List.Forall StratumCertificate.Valid certificateChunk200 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk201 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4658, zeroMask := 105702,
        component := 38 }
    witnesses := [.chain 32, .killed 12 (some 5), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 4658, zeroMask := 625894,
        component := 38 }
    witnesses := [.chain 32, .killed 19 (some 5), .chain 11, .chain 20, .chain 0, .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk201_valid :
    List.Forall StratumCertificate.Valid certificateChunk201 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk202 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4660, zeroMask := 9014437,
        component := 15 }
    witnesses := [.killed 19 (some 5), .chain 11, .killed 19 (some 7), .killed 5 (some 7), .chain 20, .killed 19 (some 7), .chain 24, .killed 5 (some 7), .killed 19 (some 7), .chain 14, .killed 5 (some 7), .chain 10, .chain 0, .killed 23 (none), .killed 0 (none), .chain 1, .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 4660, zeroMask := 9022596,
        component := 19 }
    witnesses := [.chain 11, .chain 20, .chain 24, .chain 14, .chain 10, .chain 0, .killed 23 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk202_valid :
    List.Forall StratumCertificate.Valid certificateChunk202 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk203 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4668, zeroMask := 756897,
        component := 33 }
    witnesses := [.killed 17 (some 0), .chain 11, .chain 20, .chain 82, .chain 45, .chain 86, .chain 36, .chain 37, .killed 0 (some 17), .chain 24, .chain 14, .chain 10, .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 4668, zeroMask := 765088,
        component := 33 }
    witnesses := [.killed 17 (some 13), .chain 11, .chain 20, .chain 82, .chain 45, .chain 86, .chain 36, .chain 37, .killed 13 (some 17), .chain 24, .chain 14, .chain 10, .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk203_valid :
    List.Forall StratumCertificate.Valid certificateChunk203 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk204 : List StratumCertificate := [
  { stratum :=
      { activeMask := 4670, zeroMask := 625824,
        component := 33 }
    witnesses := [.chain 32, .chain 11, .chain 20, .chain 82, .chain 45, .chain 86, .chain 36, .chain 37, .chain 38, .chain 24, .chain 14, .chain 10, .chain 0, .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk204_valid :
    List.Forall StratumCertificate.Valid certificateChunk204 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
