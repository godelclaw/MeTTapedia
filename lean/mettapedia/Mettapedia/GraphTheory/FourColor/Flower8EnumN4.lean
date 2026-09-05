import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 240–299. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_240 : StepOkEnum (w 1 0 1 2 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 240) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_241 : StepOkEnum (w 1 0 1 2 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 241) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 4, 5, 7} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_242 : StepOkEnum (w 1 0 1 2 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 242) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 4, 5, 7} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_243 : StepOkEnum (w 1 0 1 2 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 243) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_244 : StepOkEnum (w 1 0 1 2 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 244) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_245 : StepOkEnum (w 1 0 1 2 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 245) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_246 : StepOkEnum (w 1 0 1 2 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 246) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_247 : StepOkEnum (w 1 0 1 2 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 247) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_248 : StepOkEnum (w 1 0 2 0 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 248) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_249 : StepOkEnum (w 1 0 2 0 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 249) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_250 : StepOkEnum (w 1 0 2 0 1 0 0 2) TaitColorPair.bluePurple (cert.knownAt base 250) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({2, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_251 : StepOkEnum (w 1 0 2 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 251) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_252 : StepOkEnum (w 1 0 2 0 1 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 252) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({2, 4, 5, 6} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_253 : StepOkEnum (w 1 0 2 0 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 253) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4, 6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_254 : StepOkEnum (w 1 0 2 0 1 2 1 1) TaitColorPair.bluePurple (cert.knownAt base 254) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 4} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({0, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_255 : StepOkEnum (w 1 0 2 0 1 2 2 2) TaitColorPair.redBlue (cert.knownAt base 255) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_256 : StepOkEnum (w 1 0 2 0 2 1 0 0) TaitColorPair.redPurple (cert.knownAt base 256) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 4} : Finset (Fin 8)) | 1 => ({4, 6} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_257 : StepOkEnum (w 1 0 2 0 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 257) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_258 : StepOkEnum (w 1 0 2 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 258) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 1, 3, 6} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_259 : StepOkEnum (w 1 0 2 1 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 259) (fun (k : Nat) => match k with | 0 => ({3, 4, 5, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4, 5, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_260 : StepOkEnum (w 1 0 2 1 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 260) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_261 : StepOkEnum (w 1 0 2 1 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 261) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 1, 3, 7} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_262 : StepOkEnum (w 1 0 2 1 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 262) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_263 : StepOkEnum (w 1 0 2 1 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 263) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_264 : StepOkEnum (w 1 0 2 1 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 264) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 5, 6, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_265 : StepOkEnum (w 1 0 2 1 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 265) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_266 : StepOkEnum (w 1 0 2 1 2 2 0 2) TaitColorPair.bluePurple (cert.knownAt base 266) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_267 : StepOkEnum (w 1 0 2 1 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 267) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_268 : StepOkEnum (w 1 0 2 2 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 268) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1, 4, 5, 6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_269 : StepOkEnum (w 1 0 2 2 0 1 0 0) TaitColorPair.redPurple (cert.knownAt base 269) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_270 : StepOkEnum (w 1 0 2 2 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 270) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 4} : Finset (Fin 8)) | 4 => ({0, 1, 4, 5, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_271 : StepOkEnum (w 1 0 2 2 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 271) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1, 4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_272 : StepOkEnum (w 1 0 2 2 0 2 2 1) TaitColorPair.redBlue (cert.knownAt base 272) (fun (k : Nat) => match k with | 0 => ({0, 1, 4, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_273 : StepOkEnum (w 1 0 2 2 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 273) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_274 : StepOkEnum (w 1 0 2 2 1 0 1 1) TaitColorPair.redBlue (cert.knownAt base 274) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 5, 6, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 4} : Finset (Fin 8)) | 4 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_275 : StepOkEnum (w 1 0 2 2 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 275) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_276 : StepOkEnum (w 1 0 2 2 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 276) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_277 : StepOkEnum (w 1 0 2 2 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 277) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_278 : StepOkEnum (w 1 0 2 2 1 2 0 2) TaitColorPair.redPurple (cert.knownAt base 278) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_279 : StepOkEnum (w 1 0 2 2 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 279) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_280 : StepOkEnum (w 1 0 2 2 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 280) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_281 : StepOkEnum (w 1 0 2 2 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 281) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_282 : StepOkEnum (w 1 0 2 2 2 1 2 0) TaitColorPair.redBlue (cert.knownAt base 282) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_283 : StepOkEnum (w 1 0 2 2 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 283) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_284 : StepOkEnum (w 1 1 0 0 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 284) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_285 : StepOkEnum (w 1 1 0 0 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 285) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_286 : StepOkEnum (w 1 1 0 0 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 286) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_287 : StepOkEnum (w 1 1 0 1 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 287) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_288 : StepOkEnum (w 1 1 0 1 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 288) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_289 : StepOkEnum (w 1 1 0 1 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 289) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_290 : StepOkEnum (w 1 1 0 1 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 290) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({0, 1, 4, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_291 : StepOkEnum (w 1 1 0 1 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 291) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_292 : StepOkEnum (w 1 1 0 1 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 292) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_293 : StepOkEnum (w 1 1 0 2 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 293) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_294 : StepOkEnum (w 1 1 0 2 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 294) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_295 : StepOkEnum (w 1 1 0 2 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 295) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_296 : StepOkEnum (w 1 1 0 2 0 2 0 0) TaitColorPair.redBlue (cert.knownAt base 296) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_297 : StepOkEnum (w 1 1 0 2 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 297) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_298 : StepOkEnum (w 1 1 0 2 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 298) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_299 : StepOkEnum (w 1 1 0 2 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 299) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
