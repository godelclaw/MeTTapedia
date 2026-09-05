import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 600–659. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_600 : StepOkEnum (w 2 0 2 2 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 600) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_601 : StepOkEnum (w 2 0 2 2 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 601) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_602 : StepOkEnum (w 2 0 2 2 1 2 0 1) TaitColorPair.redPurple (cert.knownAt base 602) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_603 : StepOkEnum (w 2 0 2 2 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 603) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_604 : StepOkEnum (w 2 0 2 2 2 0 2 2) TaitColorPair.redPurple (cert.knownAt base 604) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 4, 7} : Finset (Fin 8)) | 12 => ({0, 1, 6, 7} : Finset (Fin 8)) | 13 => ({0, 1, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_605 : StepOkEnum (w 2 0 2 2 2 1 0 1) TaitColorPair.redPurple (cert.knownAt base 605) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({4, 6} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_606 : StepOkEnum (w 2 0 2 2 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 606) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_607 : StepOkEnum (w 2 0 2 2 2 2 0 2) TaitColorPair.redPurple (cert.knownAt base 607) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_608 : StepOkEnum (w 2 1 0 0 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 608) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_609 : StepOkEnum (w 2 1 0 0 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 609) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_610 : StepOkEnum (w 2 1 0 0 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 610) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_611 : StepOkEnum (w 2 1 0 0 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 611) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_612 : StepOkEnum (w 2 1 0 0 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 612) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_613 : StepOkEnum (w 2 1 0 0 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 613) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_614 : StepOkEnum (w 2 1 0 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 614) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_615 : StepOkEnum (w 2 1 0 0 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 615) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_616 : StepOkEnum (w 2 1 0 0 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 616) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_617 : StepOkEnum (w 2 1 0 0 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 617) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_618 : StepOkEnum (w 2 1 0 0 1 2 2 2) TaitColorPair.redBlue (cert.knownAt base 618) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_619 : StepOkEnum (w 2 1 0 0 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 619) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_620 : StepOkEnum (w 2 1 0 0 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 620) (fun (k : Nat) => match k with | 0 => ({1, 2, 3, 5} : Finset (Fin 8)) | 1 => ({1, 2, 3, 7} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_621 : StepOkEnum (w 2 1 0 0 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 621) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_622 : StepOkEnum (w 2 1 0 0 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 622) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_623 : StepOkEnum (w 2 1 0 0 2 1 2 2) TaitColorPair.redBlue (cert.knownAt base 623) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_624 : StepOkEnum (w 2 1 0 0 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 624) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_625 : StepOkEnum (w 2 1 0 0 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 625) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_626 : StepOkEnum (w 2 1 0 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 626) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_627 : StepOkEnum (w 2 1 0 1 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 627) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_628 : StepOkEnum (w 2 1 0 1 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 628) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_629 : StepOkEnum (w 2 1 0 1 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 629) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_630 : StepOkEnum (w 2 1 0 1 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 630) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_631 : StepOkEnum (w 2 1 0 1 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 631) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_632 : StepOkEnum (w 2 1 0 1 2 0 0 0) TaitColorPair.redBlue (cert.knownAt base 632) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_633 : StepOkEnum (w 2 1 0 1 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 633) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_634 : StepOkEnum (w 2 1 0 1 2 0 2 2) TaitColorPair.redBlue (cert.knownAt base 634) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_635 : StepOkEnum (w 2 1 0 1 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 635) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_636 : StepOkEnum (w 2 1 0 1 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 636) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_637 : StepOkEnum (w 2 1 0 1 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 637) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_638 : StepOkEnum (w 2 1 0 1 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 638) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_639 : StepOkEnum (w 2 1 0 2 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 639) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_640 : StepOkEnum (w 2 1 0 2 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 640) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_641 : StepOkEnum (w 2 1 0 2 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 641) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_642 : StepOkEnum (w 2 1 0 2 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 642) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_643 : StepOkEnum (w 2 1 0 2 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 643) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_644 : StepOkEnum (w 2 1 0 2 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 644) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_645 : StepOkEnum (w 2 1 0 2 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 645) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_646 : StepOkEnum (w 2 1 0 2 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 646) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_647 : StepOkEnum (w 2 1 0 2 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 647) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_648 : StepOkEnum (w 2 1 0 2 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 648) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_649 : StepOkEnum (w 2 1 1 0 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 649) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({2, 3} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_650 : StepOkEnum (w 2 1 1 0 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 650) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_651 : StepOkEnum (w 2 1 1 0 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 651) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({2, 3} : Finset (Fin 8)) | 4 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_652 : StepOkEnum (w 2 1 1 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 652) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_653 : StepOkEnum (w 2 1 1 0 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 653) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_654 : StepOkEnum (w 2 1 1 0 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 654) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_655 : StepOkEnum (w 2 1 1 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 655) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 5} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_656 : StepOkEnum (w 2 1 1 0 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 656) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_657 : StepOkEnum (w 2 1 1 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 657) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_658 : StepOkEnum (w 2 1 1 1 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 658) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 7} : Finset (Fin 8)) | 4 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_659 : StepOkEnum (w 2 1 1 1 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 659) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 8)) | 1 => ({1, 2} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({1, 6} : Finset (Fin 8)) | 4 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
