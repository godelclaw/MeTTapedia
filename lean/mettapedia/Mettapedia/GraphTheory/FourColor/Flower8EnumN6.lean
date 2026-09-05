import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 360–419. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_360 : StepOkEnum (w 1 1 2 1 2 2 1 2) TaitColorPair.redPurple (cert.knownAt base 360) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_361 : StepOkEnum (w 1 1 2 2 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 361) (fun (k : Nat) => match k with | 0 => ({0, 1, 4, 5} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_362 : StepOkEnum (w 1 1 2 2 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 362) (fun (k : Nat) => match k with | 0 => ({0, 1, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({1, 4} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_363 : StepOkEnum (w 1 1 2 2 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 363) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_364 : StepOkEnum (w 1 1 2 2 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 364) (fun (k : Nat) => match k with | 0 => ({0, 1, 4, 6} : Finset (Fin 8)) | 1 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_365 : StepOkEnum (w 1 1 2 2 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 365) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_366 : StepOkEnum (w 1 1 2 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 366) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 1, 4, 7} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_367 : StepOkEnum (w 1 1 2 2 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 367) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_368 : StepOkEnum (w 1 1 2 2 1 2 1 2) TaitColorPair.redPurple (cert.knownAt base 368) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_369 : StepOkEnum (w 1 1 2 2 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 369) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_370 : StepOkEnum (w 1 1 2 2 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 370) (fun (k : Nat) => match k with | 0 => ({0, 1, 5, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_371 : StepOkEnum (w 1 1 2 2 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 371) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_372 : StepOkEnum (w 1 1 2 2 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 372) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_373 : StepOkEnum (w 1 2 0 0 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 373) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 3, 4} : Finset (Fin 8)) | 3 => ({0, 2, 3, 4, 5, 7} : Finset (Fin 8)) | 4 => ({0, 2, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_374 : StepOkEnum (w 1 2 0 0 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 374) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_375 : StepOkEnum (w 1 2 0 0 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 375) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 3, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_376 : StepOkEnum (w 1 2 0 0 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 376) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 2, 3, 4, 6, 7} : Finset (Fin 8)) | 4 => ({0, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_377 : StepOkEnum (w 1 2 0 0 1 0 0 2) TaitColorPair.redPurple (cert.knownAt base 377) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_378 : StepOkEnum (w 1 2 0 0 1 0 2 0) TaitColorPair.redPurple (cert.knownAt base 378) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 5} : Finset (Fin 8)) | 1 => ({1, 2, 3, 7} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_379 : StepOkEnum (w 1 2 0 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 379) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_380 : StepOkEnum (w 1 2 0 0 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 380) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 2, 3, 7} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_381 : StepOkEnum (w 1 2 0 0 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 381) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_382 : StepOkEnum (w 1 2 0 0 1 2 1 1) TaitColorPair.redPurple (cert.knownAt base 382) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_383 : StepOkEnum (w 1 2 0 0 1 2 2 2) TaitColorPair.redBlue (cert.knownAt base 383) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_384 : StepOkEnum (w 1 2 0 0 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 384) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 3, 5, 6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_385 : StepOkEnum (w 1 2 0 0 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 385) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({0, 2, 3, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_386 : StepOkEnum (w 1 2 0 0 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 386) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({5, 6} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_387 : StepOkEnum (w 1 2 0 0 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 387) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 2, 3, 7} : Finset (Fin 8)) | 4 => ({0, 2, 3, 5, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_388 : StepOkEnum (w 1 2 0 0 2 1 2 2) TaitColorPair.redPurple (cert.knownAt base 388) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_389 : StepOkEnum (w 1 2 0 0 2 2 1 2) TaitColorPair.redPurple (cert.knownAt base 389) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_390 : StepOkEnum (w 1 2 0 0 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 390) (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_391 : StepOkEnum (w 1 2 0 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 391) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 2, 3, 6} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_392 : StepOkEnum (w 1 2 0 1 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 392) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_393 : StepOkEnum (w 1 2 0 1 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 393) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_394 : StepOkEnum (w 1 2 0 1 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 394) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 2, 3, 7} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_395 : StepOkEnum (w 1 2 0 1 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 395) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_396 : StepOkEnum (w 1 2 0 1 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 396) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_397 : StepOkEnum (w 1 2 0 1 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 397) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 5, 6, 7} : Finset (Fin 8)) | 4 => ({0, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_398 : StepOkEnum (w 1 2 0 1 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 398) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_399 : StepOkEnum (w 1 2 0 1 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 399) (fun (k : Nat) => match k with | 0 => ({3, 6} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_400 : StepOkEnum (w 1 2 0 1 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 400) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_401 : StepOkEnum (w 1 2 0 2 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 401) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 4, 5, 6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_402 : StepOkEnum (w 1 2 0 2 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 402) (fun (k : Nat) => match k with | 0 => ({0, 2, 4, 5} : Finset (Fin 8)) | 1 => ({0, 2, 4, 7} : Finset (Fin 8)) | 2 => ({0, 2, 4, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_403 : StepOkEnum (w 1 2 0 2 0 1 2 2) TaitColorPair.redPurple (cert.knownAt base 403) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_404 : StepOkEnum (w 1 2 0 2 0 2 1 2) TaitColorPair.redPurple (cert.knownAt base 404) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_405 : StepOkEnum (w 1 2 0 2 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 405) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5, 6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_406 : StepOkEnum (w 1 2 0 2 1 0 1 1) TaitColorPair.redPurple (cert.knownAt base 406) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_407 : StepOkEnum (w 1 2 0 2 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 407) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_408 : StepOkEnum (w 1 2 0 2 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 408) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({5, 6} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_409 : StepOkEnum (w 1 2 0 2 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 409) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_410 : StepOkEnum (w 1 2 0 2 1 2 0 2) TaitColorPair.redPurple (cert.knownAt base 410) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_411 : StepOkEnum (w 1 2 0 2 1 2 2 0) TaitColorPair.redPurple (cert.knownAt base 411) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_412 : StepOkEnum (w 1 2 0 2 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 412) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2, 5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_413 : StepOkEnum (w 1 2 0 2 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 413) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_414 : StepOkEnum (w 1 2 1 0 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 414) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_415 : StepOkEnum (w 1 2 1 0 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 415) (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 4} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_416 : StepOkEnum (w 1 2 1 0 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 416) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_417 : StepOkEnum (w 1 2 1 0 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 417) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_418 : StepOkEnum (w 1 2 1 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 418) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_419 : StepOkEnum (w 1 2 1 0 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 419) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
