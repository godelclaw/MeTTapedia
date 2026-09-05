import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 60–119. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_60 : StepOkEnum (w 0 0 2 1 2 1 2 2) TaitColorPair.redPurple (cert.knownAt base 60) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_61 : StepOkEnum (w 0 0 2 1 2 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 61) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_62 : StepOkEnum (w 0 0 2 2 1 0 0 1) TaitColorPair.redPurple (cert.knownAt base 62) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 5} : Finset (Fin 8)) | 4 => ({0, 1, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_63 : StepOkEnum (w 0 0 2 2 1 1 2 2) TaitColorPair.redPurple (cert.knownAt base 63) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({3, 6} : Finset (Fin 8)) | 4 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_64 : StepOkEnum (w 0 0 2 2 1 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 64) (fun (k : Nat) => match k with | 0 => ({2, 3, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_65 : StepOkEnum (w 0 0 2 2 2 1 1 2) TaitColorPair.bluePurple (cert.knownAt base 65) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({3, 4} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_66 : StepOkEnum (w 0 0 2 2 2 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 66) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_67 : StepOkEnum (w 0 0 2 2 2 2 0 0) TaitColorPair.bluePurple (cert.knownAt base 67) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_68 : StepOkEnum (w 0 1 0 0 0 2 2 1) TaitColorPair.redBlue (cert.knownAt base 68) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_69 : StepOkEnum (w 0 1 0 0 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 69) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_70 : StepOkEnum (w 0 1 0 0 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 70) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_71 : StepOkEnum (w 0 1 0 0 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 71) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_72 : StepOkEnum (w 0 1 0 0 2 1 0 2) TaitColorPair.redPurple (cert.knownAt base 72) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_73 : StepOkEnum (w 0 1 0 0 2 2 0 1) TaitColorPair.redPurple (cert.knownAt base 73) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 6} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_74 : StepOkEnum (w 0 1 0 1 2 0 0 2) TaitColorPair.bluePurple (cert.knownAt base 74) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_75 : StepOkEnum (w 0 1 0 1 2 2 1 1) TaitColorPair.bluePurple (cert.knownAt base 75) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({1, 3, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_76 : StepOkEnum (w 0 1 0 1 2 2 2 2) TaitColorPair.bluePurple (cert.knownAt base 76) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({1, 3, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_77 : StepOkEnum (w 0 1 0 2 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 77) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_78 : StepOkEnum (w 0 1 0 2 1 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 78) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({1, 3, 4, 7} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_79 : StepOkEnum (w 0 1 0 2 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 79) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_80 : StepOkEnum (w 0 1 0 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 80) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 2, 5, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_81 : StepOkEnum (w 0 1 0 2 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 81) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_82 : StepOkEnum (w 0 1 0 2 2 2 1 2) TaitColorPair.redPurple (cert.knownAt base 82) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({5, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_83 : StepOkEnum (w 0 1 0 2 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 83) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_84 : StepOkEnum (w 0 1 1 0 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 84) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_85 : StepOkEnum (w 0 1 1 0 1 1 1 1) TaitColorPair.redBlue (cert.knownAt base 85) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({2, 3} : Finset (Fin 8)) | 13 => ({1, 2, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_86 : StepOkEnum (w 0 1 1 0 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 86) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_87 : StepOkEnum (w 0 1 1 0 2 0 0 2) TaitColorPair.bluePurple (cert.knownAt base 87) (fun (k : Nat) => match k with | 0 => ({4, 7} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_88 : StepOkEnum (w 0 1 1 0 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 88) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_89 : StepOkEnum (w 0 1 1 0 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 89) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_90 : StepOkEnum (w 0 1 1 0 2 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 90) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_91 : StepOkEnum (w 0 1 1 0 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 91) (fun (k : Nat) => match k with | 0 => ({2, 3, 6, 7} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_92 : StepOkEnum (w 0 1 1 0 2 2 1 1) TaitColorPair.bluePurple (cert.knownAt base 92) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_93 : StepOkEnum (w 0 1 1 0 2 2 2 2) TaitColorPair.redBlue (cert.knownAt base 93) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_94 : StepOkEnum (w 0 1 1 1 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 94) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_95 : StepOkEnum (w 0 1 1 1 0 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 95) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 2, 3, 5} : Finset (Fin 8)) | 3 => ({1, 2, 3, 7} : Finset (Fin 8)) | 4 => ({1, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_96 : StepOkEnum (w 0 1 1 1 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 96) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 2, 3, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_97 : StepOkEnum (w 0 1 1 1 1 2 0 2) TaitColorPair.redPurple (cert.knownAt base 97) (fun (k : Nat) => match k with | 0 => ({0, 5} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_98 : StepOkEnum (w 0 1 1 1 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 98) (fun (k : Nat) => match k with | 0 => ({2, 3, 5, 6} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_99 : StepOkEnum (w 0 1 1 1 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 99) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_100 : StepOkEnum (w 0 1 1 1 2 1 2 0) TaitColorPair.redPurple (cert.knownAt base 100) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_101 : StepOkEnum (w 0 1 1 1 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 101) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_102 : StepOkEnum (w 0 1 1 1 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 102) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_103 : StepOkEnum (w 0 1 1 2 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 103) (fun (k : Nat) => match k with | 0 => ({2, 4, 5, 7} : Finset (Fin 8)) | 1 => ({2, 4, 5, 7} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 2, 4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_104 : StepOkEnum (w 0 1 1 2 0 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 104) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 2, 3, 5} : Finset (Fin 8)) | 3 => ({1, 2, 3, 7} : Finset (Fin 8)) | 4 => ({1, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_105 : StepOkEnum (w 0 1 1 2 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 105) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_106 : StepOkEnum (w 0 1 1 2 1 1 2 0) TaitColorPair.bluePurple (cert.knownAt base 106) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 2, 3, 6} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_107 : StepOkEnum (w 0 1 1 2 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 107) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_108 : StepOkEnum (w 0 1 1 2 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 108) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_109 : StepOkEnum (w 0 1 1 2 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 109) (fun (k : Nat) => match k with | 0 => ({2, 6} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_110 : StepOkEnum (w 0 1 2 0 0 0 2 1) TaitColorPair.redPurple (cert.knownAt base 110) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3, 4, 5} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_111 : StepOkEnum (w 0 1 2 0 0 1 2 0) TaitColorPair.redPurple (cert.knownAt base 111) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3, 4, 6} : Finset (Fin 8)) | 4 => ({2, 3, 4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_112 : StepOkEnum (w 0 1 2 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 112) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_113 : StepOkEnum (w 0 1 2 1 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 113) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_114 : StepOkEnum (w 0 1 2 1 0 2 2 2) TaitColorPair.redBlue (cert.knownAt base 114) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_115 : StepOkEnum (w 0 1 2 1 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 115) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 4, 5, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_116 : StepOkEnum (w 0 1 2 1 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 116) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 4, 5, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_117 : StepOkEnum (w 0 1 2 1 2 2 2 0) TaitColorPair.bluePurple (cert.knownAt base 117) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 4} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_118 : StepOkEnum (w 0 1 2 2 0 0 0 1) TaitColorPair.redPurple (cert.knownAt base 118) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_119 : StepOkEnum (w 0 1 2 2 0 1 1 1) TaitColorPair.redPurple (cert.knownAt base 119) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
