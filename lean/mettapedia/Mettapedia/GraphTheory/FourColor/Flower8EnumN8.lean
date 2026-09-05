import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 480–539. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_480 : StepOkEnum (w 1 2 2 1 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 480) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_481 : StepOkEnum (w 1 2 2 1 2 2 2 2) TaitColorPair.redBlue (cert.knownAt base 481) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_482 : StepOkEnum (w 1 2 2 2 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 482) (fun (k : Nat) => match k with | 0 => ({0, 4, 5, 6} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_483 : StepOkEnum (w 1 2 2 2 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 483) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_484 : StepOkEnum (w 1 2 2 2 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 484) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_485 : StepOkEnum (w 1 2 2 2 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 485) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_486 : StepOkEnum (w 1 2 2 2 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 486) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_487 : StepOkEnum (w 1 2 2 2 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 487) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_488 : StepOkEnum (w 1 2 2 2 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 488) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_489 : StepOkEnum (w 1 2 2 2 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 489) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_490 : StepOkEnum (w 1 2 2 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 490) (fun (k : Nat) => match k with | 0 => ({0, 5} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_491 : StepOkEnum (w 1 2 2 2 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 491) (fun (k : Nat) => match k with | 0 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_492 : StepOkEnum (w 2 0 0 0 0 0 2 0) TaitColorPair.redPurple (cert.knownAt base 492) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_493 : StepOkEnum (w 2 0 0 0 0 1 2 1) TaitColorPair.redPurple (cert.knownAt base 493) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_494 : StepOkEnum (w 2 0 0 0 1 0 1 2) TaitColorPair.redPurple (cert.knownAt base 494) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3, 5, 7} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_495 : StepOkEnum (w 2 0 0 0 1 0 2 1) TaitColorPair.redPurple (cert.knownAt base 495) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_496 : StepOkEnum (w 2 0 0 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 496) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({5, 6} : Finset (Fin 8)) | 3 => ({1, 2, 3, 6} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_497 : StepOkEnum (w 2 0 0 0 1 1 2 0) TaitColorPair.redPurple (cert.knownAt base 497) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_498 : StepOkEnum (w 2 0 0 0 1 2 0 1) TaitColorPair.redPurple (cert.knownAt base 498) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_499 : StepOkEnum (w 2 0 0 0 1 2 1 0) TaitColorPair.redPurple (cert.knownAt base 499) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 2, 3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_500 : StepOkEnum (w 2 0 0 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 500) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 2, 3, 5} : Finset (Fin 8)) | 3 => ({1, 2, 3, 7} : Finset (Fin 8)) | 4 => ({1, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_501 : StepOkEnum (w 2 0 0 0 2 2 0 2) TaitColorPair.redPurple (cert.knownAt base 501) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_502 : StepOkEnum (w 2 0 0 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 502) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 2, 3, 6} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_503 : StepOkEnum (w 2 0 0 1 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 503) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_504 : StepOkEnum (w 2 0 0 1 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 504) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_505 : StepOkEnum (w 2 0 0 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 505) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 2, 3, 7} : Finset (Fin 8)) | 4 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_506 : StepOkEnum (w 2 0 0 1 1 0 2 0) TaitColorPair.redPurple (cert.knownAt base 506) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_507 : StepOkEnum (w 2 0 0 1 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 507) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({5, 7} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_508 : StepOkEnum (w 2 0 0 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 508) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 2, 3, 5} : Finset (Fin 8)) | 3 => ({1, 2, 3, 7} : Finset (Fin 8)) | 4 => ({1, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_509 : StepOkEnum (w 2 0 0 1 2 2 1 2) TaitColorPair.redPurple (cert.knownAt base 509) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_510 : StepOkEnum (w 2 0 0 2 0 0 0 0) TaitColorPair.redPurple (cert.knownAt base 510) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_511 : StepOkEnum (w 2 0 0 2 0 0 1 1) TaitColorPair.redPurple (cert.knownAt base 511) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_512 : StepOkEnum (w 2 0 0 2 0 0 2 2) TaitColorPair.redPurple (cert.knownAt base 512) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({0, 1, 2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_513 : StepOkEnum (w 2 0 0 2 0 1 0 1) TaitColorPair.redPurple (cert.knownAt base 513) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3, 4, 6} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_514 : StepOkEnum (w 2 0 0 2 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 514) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_515 : StepOkEnum (w 2 0 0 2 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 515) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({0, 1, 2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_516 : StepOkEnum (w 2 0 0 2 0 2 2 0) TaitColorPair.redPurple (cert.knownAt base 516) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_517 : StepOkEnum (w 2 0 0 2 1 0 0 1) TaitColorPair.redPurple (cert.knownAt base 517) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_518 : StepOkEnum (w 2 0 0 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 518) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_519 : StepOkEnum (w 2 0 0 2 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 519) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_520 : StepOkEnum (w 2 0 0 2 1 1 1 1) TaitColorPair.redBlue (cert.knownAt base 520) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({2, 4} : Finset (Fin 8)) | 4 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_521 : StepOkEnum (w 2 0 0 2 1 1 2 2) TaitColorPair.redPurple (cert.knownAt base 521) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_522 : StepOkEnum (w 2 0 0 2 1 2 1 2) TaitColorPair.redPurple (cert.knownAt base 522) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_523 : StepOkEnum (w 2 0 0 2 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 523) (fun (k : Nat) => match k with | 0 => ({4, 7} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_524 : StepOkEnum (w 2 0 0 2 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 524) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_525 : StepOkEnum (w 2 0 0 2 2 1 1 2) TaitColorPair.redPurple (cert.knownAt base 525) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_526 : StepOkEnum (w 2 0 0 2 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 526) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_527 : StepOkEnum (w 2 0 0 2 2 2 0 0) TaitColorPair.redPurple (cert.knownAt base 527) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({0, 1, 2, 7} : Finset (Fin 8)) | 4 => ({0, 1, 2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_528 : StepOkEnum (w 2 0 1 0 0 0 1 2) TaitColorPair.redPurple (cert.knownAt base 528) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_529 : StepOkEnum (w 2 0 1 0 0 2 1 0) TaitColorPair.redPurple (cert.knownAt base 529) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 3} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_530 : StepOkEnum (w 2 0 1 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 530) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 4} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_531 : StepOkEnum (w 2 0 1 0 1 1 2 1) TaitColorPair.bluePurple (cert.knownAt base 531) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 2, 4, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_532 : StepOkEnum (w 2 0 1 0 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 532) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 4} : Finset (Fin 8)) | 1 => ({4, 6} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_533 : StepOkEnum (w 2 0 1 0 2 0 0 1) TaitColorPair.bluePurple (cert.knownAt base 533) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_534 : StepOkEnum (w 2 0 1 0 2 1 0 0) TaitColorPair.redPurple (cert.knownAt base 534) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4, 6, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_535 : StepOkEnum (w 2 0 1 0 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 535) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_536 : StepOkEnum (w 2 0 1 0 2 1 2 2) TaitColorPair.bluePurple (cert.knownAt base 536) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 2, 4, 7} : Finset (Fin 8)) | 4 => ({0, 2, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_537 : StepOkEnum (w 2 0 1 0 2 2 1 2) TaitColorPair.bluePurple (cert.knownAt base 537) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_538 : StepOkEnum (w 2 0 1 0 2 2 2 1) TaitColorPair.redPurple (cert.knownAt base 538) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_539 : StepOkEnum (w 2 0 1 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 539) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
