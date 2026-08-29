import KrennCollapseComponentContainmentCore

/-!
Concrete bottom-up certificate chunks 79 through 100.

Source certificate SHA-256: `00c487db4e253e2e4f02ef9ba136493511010bb961c0dbd40778460e458f3c44`.
-/

namespace Krenn.CollapseComponentContainmentCertificates

open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

set_option maxRecDepth 1000000 in
def certificateChunk079 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1219, zeroMask := 57739786,
        component := 29 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (none), .chain 8, .chain 9, .chain 59, .chain 5, .chain 75, .chain 39, .chain 77, .killed 24 (some 22), .killed 22 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 3 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk079_valid :
    List.Forall StratumCertificate.Valid certificateChunk079 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk080 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1220, zeroMask := 61950469,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 25 (some 14), .chain 10, .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1220, zeroMask := 66128389,
        component := 18 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 25 (some 22), .chain 10, .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21), .killed 9 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk080_valid :
    List.Forall StratumCertificate.Valid certificateChunk080 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk081 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1227, zeroMask := 53562120,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 3), .killed 9 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk081_valid :
    List.Forall StratumCertificate.Valid certificateChunk081 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk082 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1231, zeroMask := 53561856,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 21 (some 9), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .chain 8, .chain 9, .chain 59, .killed 14 (some 9), .killed 14 (some 25), .killed 25 (some 14), .killed 21 (some 9), .chain 66, .killed 21 (some 9), .chain 68, .killed 21 (some 9), .chain 70, .killed 21 (some 9), .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 21), .killed 9 (some 21), .killed 25 (some 14), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 21), .killed 9 (some 21), .chain 10, .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk082_valid :
    List.Forall StratumCertificate.Valid certificateChunk082 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk083 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1536, zeroMask := 61425855,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61425911,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65603771,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 22 (some 3), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65603827,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 22 (some 6), .killed 1 (some 22), .killed 0 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61426109,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61426165,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 6 (some 7), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65604025,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 22), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65604081,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 22), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61434014,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65611934,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61434070,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65611990,
        component := 5 }
    witnesses := [.chain 7, .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65611962,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65612018,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61434268,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65612188,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 61434324,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65612244,
        component := 5 }
    witnesses := [.chain 7, .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65612216,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 22), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1536, zeroMask := 65612272,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 22), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk083_valid :
    List.Forall StratumCertificate.Valid certificateChunk083 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk084 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1538, zeroMask := 53037246,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1538, zeroMask := 53037302,
        component := 21 }
    witnesses := [.chain 32, .killed 19 (some 5), .killed 19 (some 5), .chain 35, .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1538, zeroMask := 57215162,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1538, zeroMask := 57215218,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 22 (some 6), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk084_valid :
    List.Forall StratumCertificate.Valid certificateChunk084 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk085 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1540, zeroMask := 61425845,
        component := 2 }
    witnesses := [.killed 19 (some 5), .chain 7, .killed 19 (some 7), .killed 5 (some 7), .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1540, zeroMask := 65603761,
        component := 22 }
    witnesses := [.killed 23 (some 0), .killed 0 (some 23), .chain 7, .killed 22 (some 23), .killed 23 (some 22), .killed 0 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1540, zeroMask := 61434004,
        component := 5 }
    witnesses := [.chain 7, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1540, zeroMask := 65611924,
        component := 5 }
    witnesses := [.chain 7, .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 21 (none), .chain 1, .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1540, zeroMask := 65611952,
        component := 22 }
    witnesses := [.killed 23 (some 13), .killed 13 (some 23), .chain 7, .killed 22 (some 23), .killed 23 (some 22), .killed 13 (some 22), .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk085_valid :
    List.Forall StratumCertificate.Valid certificateChunk085 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk086 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1546, zeroMask := 53037496,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 3), .chain 37, .chain 38, .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
  { stratum :=
      { activeMask := 1546, zeroMask := 53037552,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .killed 8 (some 6), .chain 37, .chain 38, .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk086_valid :
    List.Forall StratumCertificate.Valid certificateChunk086 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk087 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1550, zeroMask := 53037232,
        component := 22 }
    witnesses := [.chain 32, .chain 35, .chain 7, .chain 36, .chain 37, .chain 38, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk087_valid :
    List.Forall StratumCertificate.Valid certificateChunk087 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk088 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1600, zeroMask := 60901591,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1600, zeroMask := 65079511,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1600, zeroMask := 60901845,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1600, zeroMask := 65079765,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .killed 6 (some 7), .killed 6 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk088_valid :
    List.Forall StratumCertificate.Valid certificateChunk088 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk089 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1602, zeroMask := 52512982,
        component := 21 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (none), .killed 24 (some 14), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 1602, zeroMask := 56690902,
        component := 21 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (none), .killed 24 (some 22), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk089_valid :
    List.Forall StratumCertificate.Valid certificateChunk089 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk090 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1728, zeroMask := 60901407,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1728, zeroMask := 65079327,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 1 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1728, zeroMask := 60901661,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1728, zeroMask := 65079581,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .killed 8 (some 3), .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk090_valid :
    List.Forall StratumCertificate.Valid certificateChunk090 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk091 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1731, zeroMask := 56690714,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 25 (some 21), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .chain 9, .chain 59, .killed 21 (some 25), .killed 4 (some 25), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 4), .killed 3 (some 22), .killed 3 (some 22), .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 21), .killed 25 (some 21), .killed 4 (some 3), .killed 4 (some 3), .killed 25 (some 4), .killed 22 (some 3), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 22), .killed 1 (some 21), .killed 1 (some 21), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 22), .chain 1, .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk091_valid :
    List.Forall StratumCertificate.Valid certificateChunk091 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk092 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1732, zeroMask := 60901397,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .chain 10, .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 1732, zeroMask := 65079317,
        component := 2 }
    witnesses := [.chain 6, .chain 7, .chain 8, .chain 9, .chain 10, .killed 25 (none), .killed 24 (some 22), .killed 23 (none), .killed 0 (none), .killed 21 (none), .chain 1, .killed 16 (some 25), .killed 11 (some 21), .killed 4 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk092_valid :
    List.Forall StratumCertificate.Valid certificateChunk092 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk093 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1739, zeroMask := 52513048,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .killed 8 (some 4), .chain 8, .chain 9, .chain 59, .killed 14 (some 25), .killed 4 (some 8), .killed 3 (some 4), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 4), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 4), .killed 8 (some 3), .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 3), .killed 4 (some 3), .killed 8 (some 3), .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk093_valid :
    List.Forall StratumCertificate.Valid certificateChunk093 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk094 : List StratumCertificate := [
  { stratum :=
      { activeMask := 1743, zeroMask := 52512784,
        component := 26 }
    witnesses := [.chain 32, .chain 6, .chain 33, .chain 35, .chain 7, .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 25 (some 14), .killed 21 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .killed 25 (some 4), .chain 8, .chain 9, .chain 59, .killed 14 (some 25), .killed 4 (some 25), .killed 25 (some 4), .killed 21 (some 4), .chain 66, .killed 21 (some 4), .chain 68, .killed 21 (some 4), .chain 70, .killed 21 (some 4), .chain 72, .chain 74, .chain 5, .chain 75, .chain 39, .chain 77, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 21), .killed 4 (some 21), .killed 25 (some 4), .chain 36, .chain 37, .chain 38, .chain 41, .chain 87, .chain 43, .chain 89, .killed 25 (some 14), .killed 25 (some 14), .killed 4 (some 21), .killed 4 (some 21), .chain 10, .killed 24 (some 14), .chain 1, .killed 16 (some 25), .killed 11 (some 21)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk094_valid :
    List.Forall StratumCertificate.Valid certificateChunk094 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk095 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2048, zeroMask := 18076655,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18338159,
        component := 49 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52122543,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18596783,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 1 (some 2), .killed 0 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52384047,
        component := 45 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18858287,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18346319,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52392207,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18866447,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 51598311,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 12 (some 5), .killed 0 (some 5), .killed 0 (some 12), .killed 17 (some 12), .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52151271,
        component := 24 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 51859815,
        component := 46 }
    witnesses := [.killed 1 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52412775,
        component := 23 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 2 (some 0), .killed 2 (some 15), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 51867975,
        component := 57 }
    witnesses := [.killed 2 (some 0), .killed 1 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52420935,
        component := 23 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 2 (some 0), .killed 2 (some 15), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 22270955,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 22532459,
        component := 47 }
    witnesses := [.killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 6 (some 18), .killed 24 (some 14), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56316843,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 22791083,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 1 (some 22), .killed 0 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56578347,
        component := 47 }
    witnesses := [.killed 25 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 19 (some 18), .killed 24 (some 14), .killed 22 (none), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 23052587,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 55792611,
        component := 45 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56345571,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56054115,
        component := 46 }
    witnesses := [.killed 1 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56607075,
        component := 23 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 5 (some 0), .killed 19 (some 15), .killed 1 (some 22), .killed 0 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26465261,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26726765,
        component := 49 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60511149,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26985389,
        component := 9 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60772653,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 5 (some 12), .killed 19 (some 3), .killed 18 (some 3), .killed 5 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 27246893,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26734925,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60780813,
        component := 3 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 8 (some 18), .killed 19 (some 18), .killed 13 (some 12), .killed 19 (some 3), .killed 18 (some 3), .killed 13 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 27255053,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 13), .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 0), .killed 14 (some 0), .killed 14 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 17), .killed 2 (some 15), .killed 2 (some 15), .killed 2 (some 14), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 23 (some 2), .killed 0 (some 2), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 59986917,
        component := 3 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60539877,
        component := 3 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 5 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60248421,
        component := 4 }
    witnesses := [.killed 12 (some 5), .killed 17 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60801381,
        component := 4 }
    witnesses := [.killed 19 (some 5), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60256581,
        component := 4 }
    witnesses := [.killed 12 (some 13), .killed 17 (some 12), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60809541,
        component := 4 }
    witnesses := [.killed 19 (some 13), .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 30659561,
        component := 50 }
    witnesses := [.killed 6 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 30921065,
        component := 49 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64705449,
        component := 50 }
    witnesses := [.killed 19 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 31179689,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 23 (some 22), .killed 0 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64966953,
        component := 45 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 23 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 31441193,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64181217,
        component := 45 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64734177,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 0 (some 17), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64442721,
        component := 46 }
    witnesses := [.killed 23 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64995681,
        component := 23 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 5 (some 0), .killed 19 (some 15), .killed 23 (some 22), .killed 0 (some 17), .killed 5 (some 17), .killed 19 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18084814,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18346446,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52130702,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 2 (some 7), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18604942,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52392334,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 7), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 18866574,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 1 (some 2), .killed 1 (some 2), .killed 1 (some 7), .killed 1 (some 17), .killed 1 (some 7), .killed 1 (some 15), .killed 1 (some 7), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 51606470,
        component := 58 }
    witnesses := [.killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52159430,
        component := 24 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 51868102,
        component := 57 }
    witnesses := [.killed 2 (some 7), .killed 1 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 52421062,
        component := 24 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 18), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 22279146,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 22540778,
        component := 59 }
    witnesses := [.killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 6 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56325034,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .killed 1 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 22799274,
        component := 39 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 1 (some 22), .killed 1 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56586666,
        component := 59 }
    witnesses := [.killed 25 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 24 (some 14), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 23060906,
        component := 31 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 24 (some 14), .killed 22 (none), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .chain 4, .killed 7 (none), .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 55800802,
        component := 56 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56353762,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56062434,
        component := 57 }
    witnesses := [.killed 5 (some 7), .killed 1 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 56615394,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26473420,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26735052,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 2 (some 7), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60519308,
        component := 12 }
    witnesses := [.killed 17 (some 12), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 26993548,
        component := 12 }
    witnesses := [.killed 17 (some 15), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60780940,
        component := 6 }
    witnesses := [.killed 17 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 27255180,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 13 (some 7), .killed 15 (some 7), .killed 14 (some 7), .killed 14 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 2 (some 7), .killed 2 (some 17), .killed 2 (some 7), .killed 2 (some 15), .killed 2 (some 7), .killed 2 (some 14), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 14), .killed 2 (some 3), .killed 23 (some 2), .killed 13 (some 2), .killed 13 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 59995076,
        component := 56 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 23 (some 9), .killed 23 (some 8), .killed 6 (some 7), .killed 2 (some 7), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 6), .killed 23 (some 2), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60548036,
        component := 6 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 9), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60256708,
        component := 57 }
    witnesses := [.killed 2 (some 7), .killed 23 (some 2), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 60809668,
        component := 6 }
    witnesses := [.killed 17 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 20 (some 18), .killed 19 (none), .killed 13 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 30667752,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 30929384,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64713640,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 31187880,
        component := 39 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 23 (some 22), .killed 13 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64975272,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 31449512,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64189408,
        component := 56 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64742368,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 64451040,
        component := 57 }
    witnesses := [.killed 5 (some 7), .killed 23 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2048, zeroMask := 65004000,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .killed 23 (some 22), .killed 13 (some 17), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk095_valid :
    List.Forall StratumCertificate.Valid certificateChunk095 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk096 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2049, zeroMask := 22540618,
        component := 59 }
    witnesses := [.killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 6 (some 18), .chain 5, .killed 24 (some 14), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2049, zeroMask := 56586506,
        component := 59 }
    witnesses := [.killed 25 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 19 (some 18), .chain 5, .killed 24 (some 14), .killed 22 (none), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 12 (none), .chain 4, .killed 3 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2049, zeroMask := 23060746,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 14 (some 18), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 1 (some 15), .killed 1 (some 14), .killed 1 (some 14), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2049, zeroMask := 56062274,
        component := 57 }
    witnesses := [.chain 5, .killed 1 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2049, zeroMask := 56615234,
        component := 23 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .chain 5, .killed 19 (some 15), .killed 1 (some 22), .killed 1 (some 17), .killed 1 (some 17), .killed 1 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2049, zeroMask := 30929224,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .chain 5, .killed 23 (some 22), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2049, zeroMask := 64975112,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 23 (some 22), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2049, zeroMask := 31449352,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 14 (some 18), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2049, zeroMask := 64450880,
        component := 57 }
    witnesses := [.chain 5, .killed 23 (some 22), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2049, zeroMask := 65003840,
        component := 23 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .chain 5, .killed 19 (some 15), .killed 23 (some 22), .killed 13 (some 17), .killed 13 (some 17), .killed 19 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk096_valid :
    List.Forall StratumCertificate.Valid certificateChunk096 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk097 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2056, zeroMask := 18076649,
        component := 50 }
    witnesses := [.killed 6 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18338153,
        component := 49 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52122537,
        component := 50 }
    witnesses := [.killed 19 (some 7), .chain 37, .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18596777,
        component := 39 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .chain 37, .killed 0 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52384041,
        component := 45 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18858281,
        component := 26 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 5), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 5), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 5 (some 18), .killed 5 (some 0), .killed 5 (some 0), .killed 5 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 5 (some 0), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2056, zeroMask := 51598305,
        component := 45 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52151265,
        component := 25 }
    witnesses := [.killed 17 (some 0), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 0 (some 17), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 51859809,
        component := 46 }
    witnesses := [.chain 37, .killed 25 (none), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52412769,
        component := 23 }
    witnesses := [.killed 17 (some 0), .killed 19 (some 5), .killed 0 (some 5), .killed 0 (some 15), .killed 17 (some 15), .killed 5 (some 0), .killed 19 (some 15), .chain 37, .killed 0 (some 17), .killed 5 (some 17), .killed 19 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18084840,
        component := 63 }
    witnesses := [.killed 6 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18346472,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52130728,
        component := 63 }
    witnesses := [.killed 19 (some 7), .killed 5 (some 7), .chain 37, .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18604968,
        component := 39 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .chain 37, .killed 13 (some 17), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 7 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52392360,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 12), .killed 17 (some 12), .killed 8 (some 18), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 25), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 18866600,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 5), .killed 19 (some 5), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 5), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 5), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 5 (some 7), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 7), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 5 (some 7), .killed 18 (some 17), .killed 19 (some 7), .killed 18 (some 15), .killed 19 (some 7), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2056, zeroMask := 51606496,
        component := 56 }
    witnesses := [.killed 8 (some 9), .killed 6 (some 7), .killed 5 (some 9), .killed 5 (some 8), .killed 5 (some 7), .killed 5 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 9 (some 7), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52159456,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 9 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 9 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 51868128,
        component := 57 }
    witnesses := [.killed 5 (some 7), .chain 37, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2056, zeroMask := 52421088,
        component := 25 }
    witnesses := [.killed 17 (some 13), .killed 13 (some 15), .killed 17 (some 15), .killed 8 (some 18), .killed 18 (some 6), .killed 8 (some 6), .chain 37, .killed 13 (some 17), .killed 18 (some 6), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 19 (none), .killed 5 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk097_valid :
    List.Forall StratumCertificate.Valid certificateChunk097 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk098 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2057, zeroMask := 18346312,
        component := 62 }
    witnesses := [.killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 15), .chain 5, .chain 37, .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2057, zeroMask := 52392200,
        component := 56 }
    witnesses := [.killed 8 (some 18), .killed 19 (some 18), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .chain 37, .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4] },
  { stratum :=
      { activeMask := 2057, zeroMask := 18866440,
        component := 26 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .killed 19 (some 14), .killed 13 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 19 (some 18), .killed 13 (some 18), .killed 15 (some 18), .killed 14 (some 18), .killed 14 (some 8), .killed 3 (some 14), .killed 3 (some 19), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 8), .chain 5, .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 14), .killed 8 (some 3), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 18 (some 17), .killed 19 (some 15), .killed 18 (some 15), .killed 19 (some 14), .killed 18 (some 14), .killed 19 (some 3), .killed 18 (some 3), .killed 8 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2057, zeroMask := 51867968,
        component := 57 }
    witnesses := [.chain 5, .chain 37, .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2057, zeroMask := 52420928,
        component := 23 }
    witnesses := [.killed 17 (some 13), .killed 19 (some 13), .killed 19 (some 15), .killed 13 (some 15), .killed 17 (some 15), .chain 5, .killed 19 (some 15), .chain 37, .killed 13 (some 17), .killed 13 (some 17), .killed 19 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk098_valid :
    List.Forall StratumCertificate.Valid certificateChunk098 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk099 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2112, zeroMask := 18072527,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 9 (some 14), .killed 9 (some 14), .killed 8 (some 9), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 6 (some 7), .killed 6 (some 7), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 9), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 7), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 7), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2112, zeroMask := 18334031,
        component := 26 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 0 (some 14), .killed 0 (some 14), .killed 17 (some 14), .killed 15 (some 14), .killed 8 (some 18), .killed 0 (some 14), .killed 0 (some 14), .killed 8 (some 14), .killed 8 (some 14), .killed 6 (some 18), .killed 6 (some 18), .killed 6 (some 0), .killed 6 (some 0), .killed 6 (some 0), .killed 3 (some 14), .killed 3 (some 0), .killed 3 (some 0), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 17), .killed 3 (some 8), .killed 3 (some 15), .killed 3 (some 8), .killed 3 (some 0), .killed 2 (some 0), .killed 2 (some 6), .killed 2 (some 15), .killed 2 (some 6), .killed 2 (some 14), .killed 2 (some 6), .killed 2 (some 3), .killed 2 (some 3), .killed 2 (some 6), .killed 2 (some 3), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 6), .killed 1 (some 15), .killed 1 (some 6), .killed 1 (some 14), .killed 1 (some 6), .killed 1 (some 3), .killed 1 (some 3), .killed 1 (some 3), .killed 24 (some 14), .killed 20 (some 18), .killed 16 (some 15), .chain 4] },
  { stratum :=
      { activeMask := 2112, zeroMask := 51626951,
        component := 24 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 8 (some 9), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 7 (none), .killed 6 (none), .killed 2 (none), .killed 1 (none)] },
  { stratum :=
      { activeMask := 2112, zeroMask := 51888455,
        component := 23 }
    witnesses := [.killed 17 (some 0), .chain 6, .killed 0 (some 15), .killed 0 (some 15), .killed 17 (some 15), .killed 2 (some 0), .killed 2 (some 15), .killed 1 (some 2), .killed 0 (some 2), .killed 1 (some 17), .killed 1 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none)] },
  { stratum :=
      { activeMask := 2112, zeroMask := 26461133,
        component := 9 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 6 (some 7), .killed 6 (some 7), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2112, zeroMask := 26722637,
        component := 17 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 17 (some 14), .killed 15 (some 14), .killed 3 (some 14), .killed 3 (some 17), .killed 3 (some 17), .killed 3 (some 15), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
  { stratum :=
      { activeMask := 2112, zeroMask := 60015557,
        component := 3 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 8 (some 9), .killed 6 (some 7), .killed 6 (some 7), .killed 9 (some 7), .killed 9 (some 6), .killed 9 (some 7), .killed 8 (some 6), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 9), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 2 (none)] },
  { stratum :=
      { activeMask := 2112, zeroMask := 60277061,
        component := 4 }
    witnesses := [.chain 6, .killed 17 (some 15), .killed 25 (none), .killed 24 (some 14), .killed 23 (none), .killed 0 (none), .killed 20 (some 18), .killed 18 (none), .killed 16 (some 15), .killed 14 (none), .chain 4, .killed 8 (none), .killed 6 (none), .killed 2 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk099_valid :
    List.Forall StratumCertificate.Valid certificateChunk099 := by
  decide

set_option maxRecDepth 1000000 in
def certificateChunk100 : List StratumCertificate := [
  { stratum :=
      { activeMask := 2176, zeroMask := 18076463,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 51598127,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 18084623,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 51606287,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 1 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 22270763,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 55792427,
        component := 50 }
    witnesses := [.chain 8, .killed 1 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 26465069,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 59986733,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 2), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 26473229,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 59994893,
        component := 63 }
    witnesses := [.chain 8, .killed 2 (some 0), .killed 23 (some 2), .killed 24 (some 14), .killed 20 (some 9), .killed 13 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 30659369,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 15), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
  { stratum :=
      { activeMask := 2176, zeroMask := 64181033,
        component := 50 }
    witnesses := [.chain 8, .killed 23 (some 22), .killed 24 (some 14), .killed 0 (none), .killed 20 (some 9), .killed 5 (none), .killed 17 (none), .killed 16 (some 25), .killed 14 (none), .killed 12 (none), .chain 4, .killed 9 (none), .killed 8 (none), .killed 3 (none)] },
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateChunk100_valid :
    List.Forall StratumCertificate.Valid certificateChunk100 := by
  decide

end Krenn.CollapseComponentContainmentCertificates
