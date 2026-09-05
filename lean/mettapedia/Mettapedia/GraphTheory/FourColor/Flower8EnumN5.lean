import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 300–359. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_300 : StepOkEnum (w 1 1 0 2 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 300) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_301 : StepOkEnum (w 1 1 1 0 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 301) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_302 : StepOkEnum (w 1 1 1 0 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 302) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_303 : StepOkEnum (w 1 1 1 0 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 303) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_304 : StepOkEnum (w 1 1 1 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 304) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({0, 1, 2, 3, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_305 : StepOkEnum (w 1 1 1 0 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 305) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_306 : StepOkEnum (w 1 1 1 0 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 306) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_307 : StepOkEnum (w 1 1 1 0 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 307) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_308 : StepOkEnum (w 1 1 1 0 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 308) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_309 : StepOkEnum (w 1 1 1 0 2 1 2 0) TaitColorPair.redBlue (cert.knownAt base 309) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_310 : StepOkEnum (w 1 1 1 0 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 310) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_311 : StepOkEnum (w 1 1 1 1 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 311) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 1, 2, 3} : Finset (Fin 8)) | 6 => ({0, 1, 2, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_312 : StepOkEnum (w 1 1 1 1 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 312) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 1, 2, 3} : Finset (Fin 8)) | 6 => ({0, 1, 2, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_313 : StepOkEnum (w 1 1 1 1 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 313) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_314 : StepOkEnum (w 1 1 1 1 0 2 2 0) TaitColorPair.redBlue (cert.knownAt base 314) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_315 : StepOkEnum (w 1 1 1 1 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 315) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_316 : StepOkEnum (w 1 1 1 1 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 316) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 1, 2, 3} : Finset (Fin 8)) | 6 => ({0, 1, 2, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_317 : StepOkEnum (w 1 1 1 1 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 317) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 1, 2, 3} : Finset (Fin 8)) | 6 => ({0, 1, 2, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_318 : StepOkEnum (w 1 1 1 1 1 1 1 1) TaitColorPair.redBlue (cert.knownAt base 318) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_319 : StepOkEnum (w 1 1 1 1 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 319) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_320 : StepOkEnum (w 1 1 1 1 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 320) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({4, 6} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_321 : StepOkEnum (w 1 1 1 1 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 321) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_322 : StepOkEnum (w 1 1 1 1 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 322) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_323 : StepOkEnum (w 1 1 1 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 323) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({2, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_324 : StepOkEnum (w 1 1 1 1 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 324) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_325 : StepOkEnum (w 1 1 1 1 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 325) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_326 : StepOkEnum (w 1 1 1 2 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 326) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_327 : StepOkEnum (w 1 1 1 2 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 327) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_328 : StepOkEnum (w 1 1 1 2 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 328) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_329 : StepOkEnum (w 1 1 1 2 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 329) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_330 : StepOkEnum (w 1 1 1 2 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 330) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_331 : StepOkEnum (w 1 1 1 2 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 331) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_332 : StepOkEnum (w 1 1 1 2 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 332) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_333 : StepOkEnum (w 1 1 1 2 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 333) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_334 : StepOkEnum (w 1 1 1 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 334) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_335 : StepOkEnum (w 1 1 1 2 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 335) (fun (k : Nat) => match k with | 0 => ({2, 6} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_336 : StepOkEnum (w 1 1 2 0 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 336) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_337 : StepOkEnum (w 1 1 2 0 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 337) (fun (k : Nat) => match k with | 0 => ({0, 1, 5, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_338 : StepOkEnum (w 1 1 2 0 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 338) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_339 : StepOkEnum (w 1 1 2 0 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 339) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_340 : StepOkEnum (w 1 1 2 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 340) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_341 : StepOkEnum (w 1 1 2 0 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 341) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_342 : StepOkEnum (w 1 1 2 0 2 0 2 2) TaitColorPair.redBlue (cert.knownAt base 342) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 5} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_343 : StepOkEnum (w 1 1 2 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 343) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_344 : StepOkEnum (w 1 1 2 0 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 344) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_345 : StepOkEnum (w 1 1 2 0 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 345) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 6} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_346 : StepOkEnum (w 1 1 2 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 346) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_347 : StepOkEnum (w 1 1 2 1 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 347) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_348 : StepOkEnum (w 1 1 2 1 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 348) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_349 : StepOkEnum (w 1 1 2 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 349) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_350 : StepOkEnum (w 1 1 2 1 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 350) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_351 : StepOkEnum (w 1 1 2 1 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 351) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 3, 5, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_352 : StepOkEnum (w 1 1 2 1 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 352) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_353 : StepOkEnum (w 1 1 2 1 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 353) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_354 : StepOkEnum (w 1 1 2 1 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 354) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_355 : StepOkEnum (w 1 1 2 1 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 355) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_356 : StepOkEnum (w 1 1 2 1 1 2 2 2) TaitColorPair.redBlue (cert.knownAt base 356) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_357 : StepOkEnum (w 1 1 2 1 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 357) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_358 : StepOkEnum (w 1 1 2 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 358) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 1, 3, 7} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_359 : StepOkEnum (w 1 1 2 1 2 1 2 2) TaitColorPair.redBlue (cert.knownAt base 359) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
