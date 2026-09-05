import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 120–179. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_120 : StepOkEnum (w 0 1 2 2 0 1 2 2) TaitColorPair.redPurple (cert.knownAt base 120) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_121 : StepOkEnum (w 0 1 2 2 1 0 0 0) TaitColorPair.bluePurple (cert.knownAt base 121) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_122 : StepOkEnum (w 0 1 2 2 1 0 2 2) TaitColorPair.bluePurple (cert.knownAt base 122) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_123 : StepOkEnum (w 0 1 2 2 1 1 1 0) TaitColorPair.bluePurple (cert.knownAt base 123) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_124 : StepOkEnum (w 0 1 2 2 1 2 2 0) TaitColorPair.bluePurple (cert.knownAt base 124) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_125 : StepOkEnum (w 0 1 2 2 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 125) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_126 : StepOkEnum (w 0 1 2 2 2 0 2 1) TaitColorPair.redPurple (cert.knownAt base 126) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 3, 4} : Finset (Fin 8)) | 3 => ({2, 3, 4, 5} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_127 : StepOkEnum (w 0 1 2 2 2 1 2 0) TaitColorPair.bluePurple (cert.knownAt base 127) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_128 : StepOkEnum (w 0 1 2 2 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 128) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_129 : StepOkEnum (w 0 2 0 0 0 1 1 2) TaitColorPair.redPurple (cert.knownAt base 129) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_130 : StepOkEnum (w 0 2 0 0 0 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 130) (fun (k : Nat) => match k with | 0 => ({1, 5} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_131 : StepOkEnum (w 0 2 0 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 131) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 6} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_132 : StepOkEnum (w 0 2 0 0 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 132) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_133 : StepOkEnum (w 0 2 0 0 2 0 0 0) TaitColorPair.redPurple (cert.knownAt base 133) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_134 : StepOkEnum (w 0 2 0 0 2 0 1 1) TaitColorPair.redPurple (cert.knownAt base 134) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_135 : StepOkEnum (w 0 2 0 0 2 2 2 0) TaitColorPair.redPurple (cert.knownAt base 135) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_136 : StepOkEnum (w 0 2 0 1 1 0 2 0) TaitColorPair.redPurple (cert.knownAt base 136) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 2, 5, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_137 : StepOkEnum (w 0 2 0 1 1 1 1 2) TaitColorPair.redPurple (cert.knownAt base 137) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_138 : StepOkEnum (w 0 2 0 1 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 138) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({5, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_139 : StepOkEnum (w 0 2 0 1 1 2 0 0) TaitColorPair.redPurple (cert.knownAt base 139) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_140 : StepOkEnum (w 0 2 0 1 2 1 0 0) TaitColorPair.redPurple (cert.knownAt base 140) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_141 : StepOkEnum (w 0 2 0 1 2 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 141) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | 2 => ({1, 3, 4, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_142 : StepOkEnum (w 0 2 0 1 2 2 2 1) TaitColorPair.redPurple (cert.knownAt base 142) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_143 : StepOkEnum (w 0 2 0 2 1 0 0 1) TaitColorPair.bluePurple (cert.knownAt base 143) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_144 : StepOkEnum (w 0 2 0 2 1 1 1 1) TaitColorPair.bluePurple (cert.knownAt base 144) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_145 : StepOkEnum (w 0 2 0 2 1 1 2 2) TaitColorPair.bluePurple (cert.knownAt base 145) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_146 : StepOkEnum (w 0 2 1 0 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 146) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3, 4, 5} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_147 : StepOkEnum (w 0 2 1 0 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 147) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3, 4, 6} : Finset (Fin 8)) | 4 => ({2, 3, 4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_148 : StepOkEnum (w 0 2 1 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 148) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_149 : StepOkEnum (w 0 2 1 1 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 149) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_150 : StepOkEnum (w 0 2 1 1 0 2 2 2) TaitColorPair.redBlue (cert.knownAt base 150) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_151 : StepOkEnum (w 0 2 1 1 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 151) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 3, 4} : Finset (Fin 8)) | 3 => ({2, 3, 4, 5} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_152 : StepOkEnum (w 0 2 1 1 1 0 2 1) TaitColorPair.bluePurple (cert.knownAt base 152) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 2, 3, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_153 : StepOkEnum (w 0 2 1 1 1 1 2 0) TaitColorPair.bluePurple (cert.knownAt base 153) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_154 : StepOkEnum (w 0 2 1 1 1 2 1 0) TaitColorPair.bluePurple (cert.knownAt base 154) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_155 : StepOkEnum (w 0 2 1 1 2 0 0 0) TaitColorPair.bluePurple (cert.knownAt base 155) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_156 : StepOkEnum (w 0 2 1 1 2 0 1 1) TaitColorPair.bluePurple (cert.knownAt base 156) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({1, 2, 3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_157 : StepOkEnum (w 0 2 1 1 2 1 1 0) TaitColorPair.bluePurple (cert.knownAt base 157) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_158 : StepOkEnum (w 0 2 1 1 2 2 2 0) TaitColorPair.bluePurple (cert.knownAt base 158) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_159 : StepOkEnum (w 0 2 1 2 0 0 0 1) TaitColorPair.redPurple (cert.knownAt base 159) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_160 : StepOkEnum (w 0 2 1 2 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 160) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 4} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({0, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_161 : StepOkEnum (w 0 2 1 2 0 1 2 2) TaitColorPair.redPurple (cert.knownAt base 161) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_162 : StepOkEnum (w 0 2 1 2 1 1 1 0) TaitColorPair.bluePurple (cert.knownAt base 162) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_163 : StepOkEnum (w 0 2 1 2 2 0 1 2) TaitColorPair.redPurple (cert.knownAt base 163) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 4, 5, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_164 : StepOkEnum (w 0 2 1 2 2 2 1 0) TaitColorPair.redPurple (cert.knownAt base 164) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 4, 5, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_165 : StepOkEnum (w 0 2 2 0 0 0 2 2) TaitColorPair.bluePurple (cert.knownAt base 165) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_166 : StepOkEnum (w 0 2 2 0 0 1 1 0) TaitColorPair.bluePurple (cert.knownAt base 166) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_167 : StepOkEnum (w 0 2 2 0 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 167) (fun (k : Nat) => match k with | 0 => ({0, 1, 4, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_168 : StepOkEnum (w 0 2 2 0 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 168) (fun (k : Nat) => match k with | 0 => ({4, 5, 6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({3, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_169 : StepOkEnum (w 0 2 2 0 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 169) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_170 : StepOkEnum (w 0 2 2 0 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 170) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_171 : StepOkEnum (w 0 2 2 0 1 1 1 1) TaitColorPair.redBlue (cert.knownAt base 171) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_172 : StepOkEnum (w 0 2 2 0 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 172) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_173 : StepOkEnum (w 0 2 2 0 1 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 173) (fun (k : Nat) => match k with | 0 => ({1, 2, 4, 5} : Finset (Fin 8)) | 1 => ({1, 2, 4, 7} : Finset (Fin 8)) | 2 => ({1, 2, 4, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_174 : StepOkEnum (w 0 2 2 0 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 174) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_175 : StepOkEnum (w 0 2 2 0 2 0 0 2) TaitColorPair.redPurple (cert.knownAt base 175) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_176 : StepOkEnum (w 0 2 2 0 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 176) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 1, 4, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_177 : StepOkEnum (w 0 2 2 0 2 1 1 2) TaitColorPair.redPurple (cert.knownAt base 177) (fun (k : Nat) => match k with | 0 => ({4, 7} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_178 : StepOkEnum (w 0 2 2 0 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 178) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_179 : StepOkEnum (w 0 2 2 0 2 2 0 0) TaitColorPair.redPurple (cert.knownAt base 179) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
