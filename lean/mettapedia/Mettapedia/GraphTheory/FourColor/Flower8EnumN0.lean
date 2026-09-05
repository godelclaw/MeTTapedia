import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 0–59. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_0 : StepOkEnum (w 0 0 0 0 0 0 0 0) TaitColorPair.redBlue (cert.knownAt base 0) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_1 : StepOkEnum (w 0 0 0 0 0 0 1 1) TaitColorPair.redPurple (cert.knownAt base 1) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_2 : StepOkEnum (w 0 0 0 0 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 2) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_3 : StepOkEnum (w 0 0 0 0 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 3) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({5, 6} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_4 : StepOkEnum (w 0 0 0 0 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 4) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({2, 3} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_5 : StepOkEnum (w 0 0 0 0 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 5) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({5, 6} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_6 : StepOkEnum (w 0 0 0 0 0 2 2 0) TaitColorPair.redPurple (cert.knownAt base 6) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({2, 3} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_7 : StepOkEnum (w 0 0 0 0 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 7) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_8 : StepOkEnum (w 0 0 0 0 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 8) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({0, 1, 6, 7} : Finset (Fin 8)) | 13 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_9 : StepOkEnum (w 0 0 0 0 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 9) (fun (k : Nat) => match k with | 0 => ({4, 7} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({4, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_10 : StepOkEnum (w 0 0 0 0 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 10) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_11 : StepOkEnum (w 0 0 0 0 2 1 1 2) TaitColorPair.redPurple (cert.knownAt base 11) (fun (k : Nat) => match k with | 0 => ({4, 7} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({4, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_12 : StepOkEnum (w 0 0 0 0 2 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 12) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_13 : StepOkEnum (w 0 0 0 0 2 2 0 0) TaitColorPair.redPurple (cert.knownAt base 13) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({0, 1, 6, 7} : Finset (Fin 8)) | 13 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_14 : StepOkEnum (w 0 0 0 1 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 14) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({0, 2, 3, 7} : Finset (Fin 8)) | 13 => ({1, 2, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_15 : StepOkEnum (w 0 0 0 1 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 15) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 1, 2, 5} : Finset (Fin 8)) | 8 => ({0, 2, 3, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_16 : StepOkEnum (w 0 0 0 1 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 16) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_17 : StepOkEnum (w 0 0 0 1 0 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 17) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_18 : StepOkEnum (w 0 0 0 1 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 18) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_19 : StepOkEnum (w 0 0 0 1 1 2 0 2) TaitColorPair.redPurple (cert.knownAt base 19) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_20 : StepOkEnum (w 0 0 0 1 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 20) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 5} : Finset (Fin 8)) | 4 => ({0, 1, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_21 : StepOkEnum (w 0 0 0 1 2 0 2 1) TaitColorPair.redPurple (cert.knownAt base 21) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_22 : StepOkEnum (w 0 0 0 1 2 1 2 0) TaitColorPair.redPurple (cert.knownAt base 22) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_23 : StepOkEnum (w 0 0 0 1 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 23) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 6} : Finset (Fin 8)) | 4 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_24 : StepOkEnum (w 0 0 0 2 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 24) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_25 : StepOkEnum (w 0 0 0 2 0 0 2 0) TaitColorPair.redPurple (cert.knownAt base 25) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 1, 2, 5} : Finset (Fin 8)) | 8 => ({0, 2, 3, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_26 : StepOkEnum (w 0 0 0 2 0 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 26) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_27 : StepOkEnum (w 0 0 0 2 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 27) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_28 : StepOkEnum (w 0 0 0 2 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 28) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_29 : StepOkEnum (w 0 0 0 2 1 0 2 1) TaitColorPair.redPurple (cert.knownAt base 29) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 5} : Finset (Fin 8)) | 4 => ({0, 1, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_30 : StepOkEnum (w 0 0 0 2 1 1 2 0) TaitColorPair.redPurple (cert.knownAt base 30) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 6} : Finset (Fin 8)) | 4 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_31 : StepOkEnum (w 0 0 0 2 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 31) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_32 : StepOkEnum (w 0 0 0 2 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 32) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_33 : StepOkEnum (w 0 0 0 2 2 2 0 2) TaitColorPair.redPurple (cert.knownAt base 33) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_34 : StepOkEnum (w 0 0 1 0 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 34) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({2, 3} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_35 : StepOkEnum (w 0 0 1 0 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 35) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 1, 4, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_36 : StepOkEnum (w 0 0 1 0 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 36) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_37 : StepOkEnum (w 0 0 1 0 0 2 2 1) TaitColorPair.redPurple (cert.knownAt base 37) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({5, 6} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_38 : StepOkEnum (w 0 0 1 0 2 1 0 2) TaitColorPair.redPurple (cert.knownAt base 38) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({4, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_39 : StepOkEnum (w 0 0 1 0 2 2 0 1) TaitColorPair.redPurple (cert.knownAt base 39) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_40 : StepOkEnum (w 0 0 1 1 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 40) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 5} : Finset (Fin 8)) | 4 => ({0, 1, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_41 : StepOkEnum (w 0 0 1 1 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 41) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 6} : Finset (Fin 8)) | 4 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_42 : StepOkEnum (w 0 0 1 2 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 42) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_43 : StepOkEnum (w 0 0 1 2 1 0 2 0) TaitColorPair.redPurple (cert.knownAt base 43) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 1, 3, 7} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_44 : StepOkEnum (w 0 0 1 2 1 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 44) (fun (k : Nat) => match k with | 0 => ({2, 3, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4, 5, 6} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_45 : StepOkEnum (w 0 0 1 2 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 45) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_46 : StepOkEnum (w 0 0 1 2 2 1 0 0) TaitColorPair.redPurple (cert.knownAt base 46) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_47 : StepOkEnum (w 0 0 1 2 2 2 2 1) TaitColorPair.redPurple (cert.knownAt base 47) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_48 : StepOkEnum (w 0 0 2 0 0 0 0 2) TaitColorPair.redPurple (cert.knownAt base 48) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({2, 3} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_49 : StepOkEnum (w 0 0 2 0 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 49) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({5, 6} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_50 : StepOkEnum (w 0 0 2 0 0 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 50) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_51 : StepOkEnum (w 0 0 2 0 0 2 1 1) TaitColorPair.redPurple (cert.knownAt base 51) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_52 : StepOkEnum (w 0 0 2 0 0 2 2 2) TaitColorPair.redPurple (cert.knownAt base 52) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 1, 4, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_53 : StepOkEnum (w 0 0 2 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 53) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_54 : StepOkEnum (w 0 0 2 0 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 54) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({4, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_55 : StepOkEnum (w 0 0 2 1 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 55) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_56 : StepOkEnum (w 0 0 2 1 1 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 56) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 3, 4, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_57 : StepOkEnum (w 0 0 2 1 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 57) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_58 : StepOkEnum (w 0 0 2 1 2 0 0 1) TaitColorPair.redPurple (cert.knownAt base 58) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_59 : StepOkEnum (w 0 0 2 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 59) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 1, 3, 7} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
