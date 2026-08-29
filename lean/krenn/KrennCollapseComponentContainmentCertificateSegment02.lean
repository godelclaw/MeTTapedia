import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 6 through 27.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk006 : List StratumCertificate := [
  { stratum :=
      { activeMask := 9, zeroMask := 18349384,
        component := 62 }
    witnesses := [.killed 15 (some 10), .killed 3 (some 14), .killed 3 (some 15), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 9, zeroMask := 20445512,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 9, zeroMask := 52395272,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 9, zeroMask := 18869512,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 10), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 10), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 10), .killed 14 (some 18), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 10 (some 15), .killed 10 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 9, zeroMask := 54491400,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 9, zeroMask := 20965640,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 14 (some 18), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 9, zeroMask := 51871040,
        component := 57 }
    witnesses := [.chain 5, .chain 37, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 9, zeroMask := 52424000,
        component := 37 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 25 (some 14), .chain 5, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 9, zeroMask := 53967168,
        component := 57 }
    witnesses := [.chain 5, .chain 37, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 9, zeroMask := 54520128,
        component := 23 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .chain 5, .killed 19 (some 15), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 19 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk006_valid :
    List.Forall StratumCertificate.Valid certificateChunk006 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk007 : List StratumCertificate := [
  { stratum :=
      { activeMask := 10, zeroMask := 17948648,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 6), .killed 8 (some 3), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 10, zeroMask := 18210280,
        component := 37 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 3 (some 14), .killed 5 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 51994536,
        component := 39 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 18468776,
        component := 39 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .chain 37, .chain 38, .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 52256168,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .chain 38, .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 18730408,
        component := 33 }
    witnesses := [.chain 32, .killed 8 (some 18), .killed 3 (some 14), .killed 18 (some 14), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .chain 38, .killed 18 (some 14), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 51470304,
        component := 26 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 5), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 5), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .killed 6 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 25 (some 14), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 9), .killed 5 (some 8), .killed 12 (some 9), .killed 12 (some 8), .killed 10 (some 9), .killed 10 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 5 (some 7), .killed 12 (some 6), .killed 10 (some 7), .killed 10 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 10, zeroMask := 52023264,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .chain 38, .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 51731936,
        component := 23 }
    witnesses := [.chain 32, .killed 12 (some 5), .killed 10 (some 5), .killed 10 (some 12), .killed 10 (some 12), .killed 5 (some 7), .killed 10 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .killed 10 (some 7), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 10, zeroMask := 52284896,
        component := 37 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 25 (some 14), .killed 5 (some 7), .chain 37, .chain 38, .killed 5 (some 7), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk007_valid :
    List.Forall StratumCertificate.Valid certificateChunk007 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk008 : List StratumCertificate := [
  { stratum :=
      { activeMask := 12, zeroMask := 54221473,
        component := 52 }
    witnesses := [.killed 19 (some 7), .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .chain 10, .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54250145,
        component := 42 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .killed 0 (some 17), .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54482977,
        component := 45 }
    witnesses := [.killed 21 (some 18), .killed 19 (some 18), .killed 19 (some 21), .killed 18 (some 21), .chain 36, .chain 37, .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54511649,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 14), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 17), .killed 5 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 5 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 14), .chain 36, .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54229664,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54258336,
        component := 42 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .killed 13 (some 17), .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54491296,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 21 (some 18), .killed 18 (some 21), .chain 36, .chain 37, .killed 13 (some 17), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
  { stratum :=
      { activeMask := 12, zeroMask := 54519968,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 21 (some 18), .killed 18 (some 21), .chain 36, .chain 37, .killed 13 (some 17), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk008_valid :
    List.Forall StratumCertificate.Valid certificateChunk008 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk009 : List StratumCertificate := [
  { stratum :=
      { activeMask := 13, zeroMask := 54491136,
        component := 56 }
    witnesses := [.killed 21 (some 18), .killed 19 (some 18), .killed 21 (some 19), .killed 18 (some 19), .chain 74, .chain 5, .killed 19 (some 21), .killed 18 (some 21), .chain 36, .chain 37, .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 13, zeroMask := 54519808,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 14 (some 18), .killed 14 (some 25), .killed 25 (some 14), .killed 21 (some 19), .killed 18 (some 19), .killed 13 (some 17), .killed 13 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .chain 74, .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 21), .killed 18 (some 21), .killed 25 (some 14), .chain 36, .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 21), .killed 18 (some 21), .chain 10, .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk009_valid :
    List.Forall StratumCertificate.Valid certificateChunk009 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk010 : List StratumCertificate := [
  { stratum :=
      { activeMask := 14, zeroMask := 54091424,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 14, zeroMask := 54120096,
        component := 42 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 14, zeroMask := 54353056,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 12), .killed 10 (some 12), .killed 21 (some 18), .killed 18 (some 21), .chain 36, .chain 37, .chain 38, .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
  { stratum :=
      { activeMask := 14, zeroMask := 54381728,
        component := 25 }
    witnesses := [.chain 32, .killed 10 (some 15), .killed 10 (some 15), .killed 21 (some 18), .killed 18 (some 21), .chain 36, .chain 37, .chain 38, .killed 18 (some 21), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk010_valid :
    List.Forall StratumCertificate.Valid certificateChunk010 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk011 : List StratumCertificate := [
  { stratum :=
      { activeMask := 64, zeroMask := 18075599,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 22253519,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 9), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 28430031,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 32607951,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 9), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 20171471,
        component := 41 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 3 (some 14), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 24349391,
        component := 41 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 3 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 18337103,
        component := 37 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 3 (some 14), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 22515023,
        component := 36 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 2 (some 0), .killed 2 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 28691535,
        component := 15 }
    witnesses := [.chain 6, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 3 (some 14), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 32869455,
        component := 36 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 2 (some 0), .killed 2 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 20432975,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 64, zeroMask := 24610895,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 64, zeroMask := 51630023,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 55807943,
        component := 38 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 9), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 61984455,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 66162375,
        component := 38 }
    witnesses := [.killed 23 (some 0), .chain 6, .killed 21 (some 9), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 53725895,
        component := 24 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 21 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 57903815,
        component := 41 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 25 (some 22), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 51891527,
        component := 37 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 25 (some 14), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 56069447,
        component := 37 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 25 (some 22), .killed 2 (some 0), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 62245959,
        component := 3 }
    witnesses := [.chain 6, .killed 10 (some 15), .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 66423879,
        component := 15 }
    witnesses := [.chain 6, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 25 (some 22), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 53987399,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 21 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 14), .killed 21 (some 0), .killed 18 (some 0), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 64, zeroMask := 58165319,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 21), .killed 0 (some 21), .killed 17 (some 21), .killed 15 (some 21), .killed 21 (some 18), .killed 0 (some 18), .killed 0 (some 18), .killed 17 (some 18), .killed 15 (some 18), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 25 (some 22), .killed 21 (some 0), .killed 18 (some 0), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 17), .killed 18 (some 17), .killed 21 (some 15), .killed 18 (some 15), .killed 6 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 21), .killed 2 (some 6), .killed 2 (some 6), .killed 2 (some 6), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 64, zeroMask := 26333133,
        component := 9 }
    witnesses := [.chain 6, .killed 10 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 30511053,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 9), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 3), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 28560333,
        component := 9 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 32738253,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 26594637,
        component := 16 }
    witnesses := [.chain 6, .killed 3 (some 14), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 30772557,
        component := 16 }
    witnesses := [.chain 6, .killed 3 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 28821837,
        component := 17 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 32999757,
        component := 17 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 3 (some 22), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 59887557,
        component := 3 }
    witnesses := [.chain 6, .killed 10 (some 15), .killed 8 (some 9), .killed 6 (some 7), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 64065477,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 9), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 62114757,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 14), .killed 8 (some 6), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 66292677,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 25 (some 22), .killed 8 (some 6), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 60149061,
        component := 4 }
    witnesses := [.chain 6, .killed 10 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 64326981,
        component := 16 }
    witnesses := [.chain 6, .killed 25 (some 22), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 62376261,
        component := 4 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 64, zeroMask := 66554181,
        component := 17 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 21), .killed 15 (some 21), .killed 25 (some 22), .killed 21 (some 17), .killed 21 (some 17), .killed 21 (some 15), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 11 (some 21), .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk011_valid :
    List.Forall StratumCertificate.Valid certificateChunk011 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk012 : List StratumCertificate := [
  { stratum :=
      { activeMask := 66, zeroMask := 17944526,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 22122446,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 9), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 18206158,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 18), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 22384078,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 18), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 20041422,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 9), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 24219342,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 9), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 20303054,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 18), .killed 3 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 24480974,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 18), .killed 3 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 51498950,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 55676870,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 9), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 51760582,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 18), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 55938502,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 18), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 53595846,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 9), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 57773766,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 9), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 53857478,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 18), .killed 25 (some 14), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 66, zeroMask := 58035398,
        component := 38 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 18), .killed 25 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk012_valid :
    List.Forall StratumCertificate.Valid certificateChunk012 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk013 : List StratumCertificate := [
  { stratum :=
      { activeMask := 67, zeroMask := 22383946,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 18), .killed 6 (some 18), .killed 6 (some 18), .chain 5, .killed 18 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 67, zeroMask := 24480842,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 18), .killed 6 (some 18), .killed 6 (some 18), .chain 5, .killed 18 (some 6), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 18), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 67, zeroMask := 55938370,
        component := 37 }
    witnesses := [.chain 32, .chain 6, .killed 25 (some 22), .chain 5, .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 24 (some 22), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 67, zeroMask := 58035266,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 15 (some 10), .killed 21 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 25 (some 18), .killed 15 (some 10), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 10), .killed 6 (some 18), .killed 6 (some 25), .killed 25 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 21 (some 22), .killed 18 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 6 (some 22), .chain 5, .killed 18 (some 6), .killed 10 (some 15), .killed 10 (some 6), .killed 25 (some 21), .killed 18 (some 6), .killed 22 (some 21), .killed 18 (some 6), .killed 25 (some 6), .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 21), .killed 1 (some 6), .killed 1 (some 6), .killed 24 (some 22), .killed 20 (some 18), .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk013_valid :
    List.Forall StratumCertificate.Valid certificateChunk013 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk014 : List StratumCertificate := [
  { stratum :=
      { activeMask := 75, zeroMask := 18206024,
        component := 37 }
    witnesses := [.chain 32, .chain 6, .killed 3 (some 14), .chain 5, .chain 37, .chain 38, .chain 41, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 75, zeroMask := 51760448,
        component := 37 }
    witnesses := [.chain 32, .chain 6, .killed 25 (some 14), .chain 5, .chain 37, .chain 38, .chain 41, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk014_valid :
    List.Forall StratumCertificate.Valid certificateChunk014 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk015 : List StratumCertificate := [
  { stratum :=
      { activeMask := 128, zeroMask := 18079535,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 51601199,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 28433967,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 61955631,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 20175407,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 53697071,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 18087695,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 51609359,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 22265615,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 55787279,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 28442127,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 61963791,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 32620047,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 66141711,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 20183567,
        component := 65 }
    witnesses := [.killed 0 (some 14), .chain 8, .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 53705231,
        component := 65 }
    witnesses := [.killed 0 (some 14), .chain 8, .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 24361487,
        component := 60 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 57883151,
        component := 60 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 22257451,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 55779115,
        component := 47 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 32611883,
        component := 36 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 21 (some 9), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 12 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 66133547,
        component := 29 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 9 (none), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 24353323,
        component := 48 }
    witnesses := [.chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 57874987,
        component := 48 }
    witnesses := [.chain 8, .killed 24 (some 22), .killed 22 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 26337069,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 59858733,
        component := 9 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 28564269,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 62085933,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 26345229,
        component := 9 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 59866893,
        component := 9 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 30523149,
        component := 15 }
    witnesses := [.killed 12 (some 13), .killed 8 (some 9), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 12), .killed 9 (some 3), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 64044813,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 13), .killed 0 (some 23), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 23), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 23), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 0), .killed 23 (some 0), .killed 23 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 23), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 23), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 128, zeroMask := 28572429,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 62094093,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 32750349,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 66272013,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 30514985,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 128, zeroMask := 64036649,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 22), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 128, zeroMask := 32742185,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 128, zeroMask := 66263849,
        component := 52 }
    witnesses := [.chain 8, .killed 3 (some 22), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk015_valid :
    List.Forall StratumCertificate.Valid certificateChunk015 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk016 : List StratumCertificate := [
  { stratum :=
      { activeMask := 129, zeroMask := 22265610,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 55787274,
        component := 59 }
    witnesses := [.killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 10), .chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 32620042,
        component := 36 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 21 (some 9), .chain 8, .killed 13 (some 12), .chain 5, .killed 12 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 66141706,
        component := 29 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (none), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 24361482,
        component := 60 }
    witnesses := [.chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 57883146,
        component := 60 }
    witnesses := [.chain 8, .chain 5, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 30523144,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 15), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 13 (some 12), .killed 15 (some 10), .killed 23 (some 9), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 23), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 129, zeroMask := 64044808,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 23), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 23), .killed 8 (some 12), .killed 8 (some 12), .killed 8 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 23 (some 9), .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 23), .killed 9 (some 23), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 129, zeroMask := 32750344,
        component := 65 }
    witnesses := [.killed 8 (some 23), .chain 8, .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
  { stratum :=
      { activeMask := 129, zeroMask := 66272008,
        component := 65 }
    witnesses := [.killed 8 (some 23), .chain 8, .killed 23 (some 8), .killed 3 (some 22), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 8 (some 23), .killed 8 (some 3), .killed 23 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk016_valid :
    List.Forall StratumCertificate.Valid certificateChunk016 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk017 : List StratumCertificate := [
  { stratum :=
      { activeMask := 132, zeroMask := 61955621,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 10 (some 12), .chain 8, .killed 5 (some 12), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 132, zeroMask := 62085669,
        component := 18 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .chain 8, .killed 5 (some 12), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 132, zeroMask := 61963781,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 132, zeroMask := 66141701,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 10 (some 12), .chain 8, .killed 13 (some 12), .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 132, zeroMask := 62093829,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 132, zeroMask := 66271749,
        component := 18 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .chain 8, .killed 13 (some 12), .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 132, zeroMask := 66133537,
        component := 26 }
    witnesses := [.killed 23 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 10 (some 12), .killed 0 (some 5), .killed 0 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 21 (some 9), .killed 0 (some 5), .killed 0 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 5 (some 12), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 25 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 9), .killed 5 (some 22), .killed 12 (some 9), .killed 12 (some 22), .killed 10 (some 9), .killed 10 (some 22), .killed 5 (some 0), .killed 5 (some 0), .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .killed 5 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 132, zeroMask := 66263585,
        component := 52 }
    witnesses := [.chain 8, .killed 25 (some 22), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .chain 10, .killed 24 (some 22), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk017_valid :
    List.Forall StratumCertificate.Valid certificateChunk017 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk018 : List StratumCertificate := [
  { stratum :=
      { activeMask := 133, zeroMask := 66141696,
        component := 26 }
    witnesses := [.killed 23 (some 13), .killed 12 (some 13), .killed 10 (some 23), .killed 10 (some 12), .killed 10 (some 12), .killed 9 (some 21), .killed 9 (some 12), .killed 9 (some 12), .killed 9 (some 10), .killed 21 (some 9), .killed 25 (some 23), .killed 13 (some 12), .killed 25 (some 12), .killed 25 (some 10), .chain 8, .killed 13 (some 12), .killed 23 (some 10), .killed 21 (some 9), .killed 23 (some 25), .killed 25 (some 22), .killed 21 (some 9), .killed 23 (some 22), .killed 13 (some 9), .killed 13 (some 22), .killed 12 (some 9), .killed 12 (some 22), .killed 10 (some 9), .killed 10 (some 22), .killed 23 (some 22), .chain 5, .killed 12 (some 23), .killed 10 (some 23), .killed 10 (some 23), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .killed 13 (some 22), .killed 12 (some 22), .killed 10 (some 22), .killed 10 (some 22), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .killed 9 (some 21), .chain 10, .killed 24 (some 22), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 133, zeroMask := 66271744,
        component := 65 }
    witnesses := [.killed 25 (some 23), .chain 8, .killed 23 (some 25), .killed 25 (some 22), .killed 23 (some 22), .killed 23 (some 22), .chain 5, .killed 25 (some 23), .killed 22 (some 23), .killed 23 (some 22), .chain 10, .killed 24 (some 22), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk018_valid :
    List.Forall StratumCertificate.Valid certificateChunk018 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk019 : List StratumCertificate := [
  { stratum :=
      { activeMask := 136, zeroMask := 18079529,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 136, zeroMask := 51601193,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 136, zeroMask := 20175657,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 136, zeroMask := 53697321,
        component := 50 }
    witnesses := [.chain 8, .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk019_valid :
    List.Forall StratumCertificate.Valid certificateChunk019 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk020 : List StratumCertificate := [
  { stratum :=
      { activeMask := 137, zeroMask := 18087688,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 137, zeroMask := 51609352,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 137, zeroMask := 20183816,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 137, zeroMask := 53705480,
        component := 63 }
    witnesses := [.chain 8, .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk020_valid :
    List.Forall StratumCertificate.Valid certificateChunk020 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk021 : List StratumCertificate := [
  { stratum :=
      { activeMask := 140, zeroMask := 53697057,
        component := 52 }
    witnesses := [.chain 8, .killed 25 (some 14), .killed 25 (some 14), .chain 36, .chain 37, .chain 10, .killed 24 (some 14), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk021_valid :
    List.Forall StratumCertificate.Valid certificateChunk021 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk022 : List StratumCertificate := [
  { stratum :=
      { activeMask := 141, zeroMask := 53705216,
        component := 65 }
    witnesses := [.killed 25 (some 14), .chain 8, .killed 14 (some 25), .killed 25 (some 14), .chain 66, .chain 74, .chain 5, .killed 25 (some 14), .chain 36, .chain 37, .chain 10, .killed 24 (some 14), .killed 21 (none), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .killed 11 (some 21), .killed 9 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk022_valid :
    List.Forall StratumCertificate.Valid certificateChunk022 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk023 : List StratumCertificate := [
  { stratum :=
      { activeMask := 192, zeroMask := 18075407,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 10 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 9 (some 14), .killed 9 (some 10), .killed 8 (some 9), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 10), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
  { stratum :=
      { activeMask := 192, zeroMask := 22253327,
        component := 36 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 8 (some 9), .chain 8, .chain 9, .killed 2 (some 0), .killed 2 (some 17), .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 28429839,
        component := 18 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .killed 3 (some 14), .killed 1 (some 3), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 32607759,
        component := 18 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .killed 3 (some 22), .killed 1 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 20171279,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 21 (some 9), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .chain 8, .chain 9, .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 17), .killed 3 (some 9), .killed 3 (some 17), .killed 3 (some 9), .killed 3 (some 15), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21)] },
  { stratum :=
      { activeMask := 192, zeroMask := 24349199,
        component := 29 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 9 (none), .chain 8, .chain 9, .killed 15 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 26332941,
        component := 9 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 10), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 30510861,
        component := 15 }
    witnesses := [.chain 6, .killed 8 (some 9), .chain 8, .chain 9, .killed 3 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 22), .killed 9 (some 3), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 28560141,
        component := 9 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .killed 11 (some 21), .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 192, zeroMask := 32738061,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .killed 3 (some 22), .killed 8 (some 3), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk023_valid :
    List.Forall StratumCertificate.Valid certificateChunk023 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk024 : List StratumCertificate := [
  { stratum :=
      { activeMask := 195, zeroMask := 22122250,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .killed 8 (some 9), .chain 8, .chain 9, .chain 5, .chain 75, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 195, zeroMask := 24219146,
        component := 36 }
    witnesses := [.chain 32, .chain 6, .killed 21 (some 9), .chain 8, .chain 9, .chain 5, .chain 75, .killed 24 (some 22), .killed 22 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 15 (none), .killed 11 (some 10), .killed 10 (none), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk024_valid :
    List.Forall StratumCertificate.Valid certificateChunk024 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk025 : List StratumCertificate := [
  { stratum :=
      { activeMask := 196, zeroMask := 61984261,
        component := 18 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 196, zeroMask := 66162181,
        component := 18 }
    witnesses := [.chain 6, .killed 10 (some 15), .chain 8, .chain 9, .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 196, zeroMask := 62114309,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 196, zeroMask := 66292229,
        component := 18 }
    witnesses := [.chain 6, .killed 17 (some 15), .chain 8, .chain 9, .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk025_valid :
    List.Forall StratumCertificate.Valid certificateChunk025 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk026 : List StratumCertificate := [
  { stratum :=
      { activeMask := 203, zeroMask := 17944328,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 10), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 10), .chain 8, .chain 9, .killed 15 (some 10), .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk026_valid :
    List.Forall StratumCertificate.Valid certificateChunk026 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk027 : List StratumCertificate := [
  { stratum :=
      { activeMask := 207, zeroMask := 53595648,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .killed 10 (some 15), .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 10), .killed 21 (some 9), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 15 (some 10), .chain 8, .chain 9, .killed 15 (some 10), .killed 14 (some 9), .killed 14 (some 25), .killed 25 (some 14), .killed 21 (some 9), .chain 66, .killed 21 (some 9), .chain 68, .killed 21 (some 9), .chain 70, .killed 10 (some 9), .killed 10 (some 15), .chain 74, .chain 5, .chain 75, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 21), .killed 9 (some 21), .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .killed 10 (some 15), .killed 10 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 21), .killed 9 (some 21), .chain 10, .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 11 (some 10)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk027_valid :
    List.Forall StratumCertificate.Valid certificateChunk027 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
