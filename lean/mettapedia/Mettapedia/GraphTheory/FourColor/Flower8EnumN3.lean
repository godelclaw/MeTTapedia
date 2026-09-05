import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 180–239. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_180 : StepOkEnum (w 0 2 2 0 2 2 1 1) TaitColorPair.redPurple (cert.knownAt base 180) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_181 : StepOkEnum (w 0 2 2 0 2 2 2 2) TaitColorPair.redPurple (cert.knownAt base 181) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({2, 3} : Finset (Fin 8)) | 13 => ({1, 2, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_182 : StepOkEnum (w 0 2 2 1 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 182) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({3, 4} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_183 : StepOkEnum (w 0 2 2 1 0 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 183) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 2, 3, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_184 : StepOkEnum (w 0 2 2 1 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 184) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 3, 4, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_185 : StepOkEnum (w 0 2 2 1 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 185) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 8)) | 1 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_186 : StepOkEnum (w 0 2 2 1 2 1 0 2) TaitColorPair.redPurple (cert.knownAt base 186) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_187 : StepOkEnum (w 0 2 2 1 2 2 0 1) TaitColorPair.redPurple (cert.knownAt base 187) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_188 : StepOkEnum (w 0 2 2 1 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 188) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_189 : StepOkEnum (w 0 2 2 2 0 0 2 0) TaitColorPair.redPurple (cert.knownAt base 189) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_190 : StepOkEnum (w 0 2 2 2 0 1 2 1) TaitColorPair.redPurple (cert.knownAt base 190) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 4} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_191 : StepOkEnum (w 0 2 2 2 1 0 2 1) TaitColorPair.redPurple (cert.knownAt base 191) (fun (k : Nat) => match k with | 0 => ({2, 3, 5, 6} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_192 : StepOkEnum (w 0 2 2 2 1 1 0 2) TaitColorPair.redPurple (cert.knownAt base 192) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_193 : StepOkEnum (w 0 2 2 2 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 193) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_194 : StepOkEnum (w 0 2 2 2 1 2 0 1) TaitColorPair.redPurple (cert.knownAt base 194) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_195 : StepOkEnum (w 0 2 2 2 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 195) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_196 : StepOkEnum (w 0 2 2 2 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 196) (fun (k : Nat) => match k with | 0 => ({0, 5} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_197 : StepOkEnum (w 0 2 2 2 2 2 0 2) TaitColorPair.redPurple (cert.knownAt base 197) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 2, 3, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 2, 3, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_198 : StepOkEnum (w 1 0 0 0 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 198) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 4 => ({0, 1, 3, 6} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_199 : StepOkEnum (w 1 0 0 0 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 199) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_200 : StepOkEnum (w 1 0 0 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 200) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_201 : StepOkEnum (w 1 0 0 0 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 201) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 3, 4, 6} : Finset (Fin 8)) | 4 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_202 : StepOkEnum (w 1 0 0 0 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 202) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_203 : StepOkEnum (w 1 0 0 0 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 203) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3, 5, 7} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_204 : StepOkEnum (w 1 0 0 0 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 204) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_205 : StepOkEnum (w 1 0 0 0 2 1 2 0) TaitColorPair.redBlue (cert.knownAt base 205) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_206 : StepOkEnum (w 1 0 0 0 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 206) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_207 : StepOkEnum (w 1 0 0 0 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 207) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_208 : StepOkEnum (w 1 0 0 1 0 0 0 0) TaitColorPair.redBlue (cert.knownAt base 208) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_209 : StepOkEnum (w 1 0 0 1 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 209) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_210 : StepOkEnum (w 1 0 0 1 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 210) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_211 : StepOkEnum (w 1 0 0 1 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 211) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_212 : StepOkEnum (w 1 0 0 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 212) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_213 : StepOkEnum (w 1 0 0 1 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 213) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_214 : StepOkEnum (w 1 0 0 1 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 214) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_215 : StepOkEnum (w 1 0 0 1 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 215) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_216 : StepOkEnum (w 1 0 0 1 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 216) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_217 : StepOkEnum (w 1 0 0 1 2 2 2 2) TaitColorPair.redBlue (cert.knownAt base 217) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_218 : StepOkEnum (w 1 0 0 2 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 218) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_219 : StepOkEnum (w 1 0 0 2 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 219) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 4, 5, 7} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_220 : StepOkEnum (w 1 0 0 2 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 220) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 4} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_221 : StepOkEnum (w 1 0 0 2 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 221) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_222 : StepOkEnum (w 1 0 0 2 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 222) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 4} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_223 : StepOkEnum (w 1 0 0 2 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 223) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_224 : StepOkEnum (w 1 0 0 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 224) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_225 : StepOkEnum (w 1 0 0 2 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 225) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_226 : StepOkEnum (w 1 0 1 0 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 226) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_227 : StepOkEnum (w 1 0 1 0 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 227) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_228 : StepOkEnum (w 1 0 1 0 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 228) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_229 : StepOkEnum (w 1 0 1 0 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 229) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_230 : StepOkEnum (w 1 0 1 0 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 230) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_231 : StepOkEnum (w 1 0 1 0 2 2 2 2) TaitColorPair.redBlue (cert.knownAt base 231) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_232 : StepOkEnum (w 1 0 1 1 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 232) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 1, 4, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_233 : StepOkEnum (w 1 0 1 1 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 233) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({0, 1, 4, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_234 : StepOkEnum (w 1 0 1 1 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 234) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_235 : StepOkEnum (w 1 0 1 1 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 235) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3, 4, 7} : Finset (Fin 8)) | 3 => ({0, 3, 4, 7} : Finset (Fin 8)) | 4 => ({0, 1, 4, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_236 : StepOkEnum (w 1 0 1 1 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 236) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_237 : StepOkEnum (w 1 0 1 1 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 237) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_238 : StepOkEnum (w 1 0 1 1 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 238) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_239 : StepOkEnum (w 1 0 1 1 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 239) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
