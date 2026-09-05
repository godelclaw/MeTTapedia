import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 420–479. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_420 : StepOkEnum (w 1 2 1 0 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 420) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_421 : StepOkEnum (w 1 2 1 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 421) (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 5} : Finset (Fin 8)) | 1 => ({0, 2, 3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_422 : StepOkEnum (w 1 2 1 0 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 422) (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 6} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_423 : StepOkEnum (w 1 2 1 0 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 423) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_424 : StepOkEnum (w 1 2 1 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 424) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_425 : StepOkEnum (w 1 2 1 1 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 425) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_426 : StepOkEnum (w 1 2 1 1 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 426) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_427 : StepOkEnum (w 1 2 1 1 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 427) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_428 : StepOkEnum (w 1 2 1 1 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 428) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_429 : StepOkEnum (w 1 2 1 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 429) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_430 : StepOkEnum (w 1 2 1 1 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 430) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_431 : StepOkEnum (w 1 2 1 1 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 431) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_432 : StepOkEnum (w 1 2 1 1 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 432) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_433 : StepOkEnum (w 1 2 1 1 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 433) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_434 : StepOkEnum (w 1 2 1 1 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 434) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_435 : StepOkEnum (w 1 2 1 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 435) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_436 : StepOkEnum (w 1 2 1 1 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 436) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_437 : StepOkEnum (w 1 2 1 1 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 437) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_438 : StepOkEnum (w 1 2 1 1 2 1 2 2) TaitColorPair.redBlue (cert.knownAt base 438) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_439 : StepOkEnum (w 1 2 1 1 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 439) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_440 : StepOkEnum (w 1 2 1 1 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 440) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_441 : StepOkEnum (w 1 2 1 2 0 0 0 0) TaitColorPair.redBlue (cert.knownAt base 441) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_442 : StepOkEnum (w 1 2 1 2 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 442) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_443 : StepOkEnum (w 1 2 1 2 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 443) (fun (k : Nat) => match k with | 0 => ({0, 2, 4, 5} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_444 : StepOkEnum (w 1 2 1 2 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 444) (fun (k : Nat) => match k with | 0 => ({0, 2, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_445 : StepOkEnum (w 1 2 1 2 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 445) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_446 : StepOkEnum (w 1 2 1 2 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 446) (fun (k : Nat) => match k with | 0 => ({1, 3, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_447 : StepOkEnum (w 1 2 1 2 0 2 2 0) TaitColorPair.redBlue (cert.knownAt base 447) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({2, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_448 : StepOkEnum (w 1 2 1 2 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 448) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({2, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_449 : StepOkEnum (w 1 2 1 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 449) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_450 : StepOkEnum (w 1 2 1 2 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 450) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({2, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_451 : StepOkEnum (w 1 2 1 2 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 451) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 8)) | 1 => ({2, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_452 : StepOkEnum (w 1 2 1 2 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 452) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_453 : StepOkEnum (w 1 2 1 2 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 453) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 8)) | 1 => ({1, 3} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_454 : StepOkEnum (w 1 2 1 2 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 454) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_455 : StepOkEnum (w 1 2 1 2 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 455) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_456 : StepOkEnum (w 1 2 2 0 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 456) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_457 : StepOkEnum (w 1 2 2 0 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 457) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_458 : StepOkEnum (w 1 2 2 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 458) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_459 : StepOkEnum (w 1 2 2 0 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 459) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_460 : StepOkEnum (w 1 2 2 0 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 460) (fun (k : Nat) => match k with | 0 => ({0, 3, 5, 6} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_461 : StepOkEnum (w 1 2 2 0 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 461) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_462 : StepOkEnum (w 1 2 2 0 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 462) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_463 : StepOkEnum (w 1 2 2 0 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 463) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_464 : StepOkEnum (w 1 2 2 1 0 0 0 0) TaitColorPair.redBlue (cert.knownAt base 464) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_465 : StepOkEnum (w 1 2 2 1 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 465) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_466 : StepOkEnum (w 1 2 2 1 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 466) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_467 : StepOkEnum (w 1 2 2 1 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 467) (fun (k : Nat) => match k with | 0 => ({0, 3, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_468 : StepOkEnum (w 1 2 2 1 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 468) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_469 : StepOkEnum (w 1 2 2 1 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 469) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_470 : StepOkEnum (w 1 2 2 1 0 2 2 0) TaitColorPair.redBlue (cert.knownAt base 470) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_471 : StepOkEnum (w 1 2 2 1 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 471) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_472 : StepOkEnum (w 1 2 2 1 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 472) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 3} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_473 : StepOkEnum (w 1 2 2 1 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 473) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_474 : StepOkEnum (w 1 2 2 1 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 474) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_475 : StepOkEnum (w 1 2 2 1 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 475) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_476 : StepOkEnum (w 1 2 2 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 476) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_477 : StepOkEnum (w 1 2 2 1 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 477) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_478 : StepOkEnum (w 1 2 2 1 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 478) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_479 : StepOkEnum (w 1 2 2 1 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 479) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
