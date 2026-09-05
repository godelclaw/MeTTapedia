import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 720–779. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_720 : StepOkEnum (w 2 1 2 2 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 720) (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_721 : StepOkEnum (w 2 1 2 2 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 721) (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_722 : StepOkEnum (w 2 1 2 2 1 2 2 2) TaitColorPair.redBlue (cert.knownAt base 722) (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_723 : StepOkEnum (w 2 1 2 2 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 723) (fun (k : Nat) => match k with | 0 => ({1, 5} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_724 : StepOkEnum (w 2 1 2 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 724) (fun (k : Nat) => match k with | 0 => ({1, 5} : Finset (Fin 8)) | 1 => ({1, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_725 : StepOkEnum (w 2 1 2 2 2 1 2 2) TaitColorPair.redBlue (cert.knownAt base 725) (fun (k : Nat) => match k with | 0 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_726 : StepOkEnum (w 2 1 2 2 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 726) (fun (k : Nat) => match k with | 0 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_727 : StepOkEnum (w 2 2 0 0 0 0 2 2) TaitColorPair.redPurple (cert.knownAt base 727) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_728 : StepOkEnum (w 2 2 0 0 0 1 0 1) TaitColorPair.redPurple (cert.knownAt base 728) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_729 : StepOkEnum (w 2 2 0 0 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 729) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({6, 7} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_730 : StepOkEnum (w 2 2 0 0 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 730) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_731 : StepOkEnum (w 2 2 0 0 1 0 1 0) TaitColorPair.redPurple (cert.knownAt base 731) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_732 : StepOkEnum (w 2 2 0 0 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 732) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({5, 6} : Finset (Fin 8)) | 4 => ({2, 3, 6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_733 : StepOkEnum (w 2 2 0 0 1 2 1 2) TaitColorPair.redPurple (cert.knownAt base 733) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 3, 5} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_734 : StepOkEnum (w 2 2 0 0 1 2 2 1) TaitColorPair.redPurple (cert.knownAt base 734) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_735 : StepOkEnum (w 2 2 0 0 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 735) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2, 3, 4} : Finset (Fin 8)) | 10 => ({0, 3, 6, 7} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_736 : StepOkEnum (w 2 2 0 0 2 1 1 2) TaitColorPair.redPurple (cert.knownAt base 736) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_737 : StepOkEnum (w 2 2 0 0 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 737) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_738 : StepOkEnum (w 2 2 0 0 2 2 0 0) TaitColorPair.redPurple (cert.knownAt base 738) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_739 : StepOkEnum (w 2 2 0 1 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 739) (fun (k : Nat) => match k with | 0 => ({2, 3, 4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_740 : StepOkEnum (w 2 2 0 1 0 1 0 0) TaitColorPair.redBlue (cert.knownAt base 740) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_741 : StepOkEnum (w 2 2 0 1 0 2 1 2) TaitColorPair.redPurple (cert.knownAt base 741) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_742 : StepOkEnum (w 2 2 0 1 0 2 2 1) TaitColorPair.redBlue (cert.knownAt base 742) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_743 : StepOkEnum (w 2 2 0 1 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 743) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_744 : StepOkEnum (w 2 2 0 1 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 744) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({3, 4} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_745 : StepOkEnum (w 2 2 0 1 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 745) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({3, 4} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_746 : StepOkEnum (w 2 2 0 1 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 746) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 8)) | 1 => ({3, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_747 : StepOkEnum (w 2 2 0 1 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 747) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_748 : StepOkEnum (w 2 2 0 1 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 748) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_749 : StepOkEnum (w 2 2 0 2 0 0 2 0) TaitColorPair.redPurple (cert.knownAt base 749) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_750 : StepOkEnum (w 2 2 0 2 0 1 1 2) TaitColorPair.redPurple (cert.knownAt base 750) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_751 : StepOkEnum (w 2 2 0 2 0 1 2 1) TaitColorPair.redPurple (cert.knownAt base 751) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_752 : StepOkEnum (w 2 2 0 2 0 2 0 0) TaitColorPair.redPurple (cert.knownAt base 752) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_753 : StepOkEnum (w 2 2 0 2 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 753) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_754 : StepOkEnum (w 2 2 0 2 1 0 2 1) TaitColorPair.redPurple (cert.knownAt base 754) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_755 : StepOkEnum (w 2 2 0 2 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 755) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_756 : StepOkEnum (w 2 2 0 2 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 756) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_757 : StepOkEnum (w 2 2 0 2 2 0 0 0) TaitColorPair.redPurple (cert.knownAt base 757) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_758 : StepOkEnum (w 2 2 0 2 2 0 1 1) TaitColorPair.redPurple (cert.knownAt base 758) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_759 : StepOkEnum (w 2 2 0 2 2 0 2 2) TaitColorPair.redPurple (cert.knownAt base 759) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_760 : StepOkEnum (w 2 2 0 2 2 1 0 1) TaitColorPair.redPurple (cert.knownAt base 760) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_761 : StepOkEnum (w 2 2 0 2 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 761) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_762 : StepOkEnum (w 2 2 0 2 2 2 0 2) TaitColorPair.redPurple (cert.knownAt base 762) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_763 : StepOkEnum (w 2 2 0 2 2 2 2 0) TaitColorPair.redPurple (cert.knownAt base 763) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({1, 2} : Finset (Fin 8)) | 8 => ({1, 4} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_764 : StepOkEnum (w 2 2 1 0 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 764) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_765 : StepOkEnum (w 2 2 1 0 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 765) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_766 : StepOkEnum (w 2 2 1 0 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 766) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_767 : StepOkEnum (w 2 2 1 0 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 767) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_768 : StepOkEnum (w 2 2 1 0 1 0 1 1) TaitColorPair.redBlue (cert.knownAt base 768) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_769 : StepOkEnum (w 2 2 1 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 769) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_770 : StepOkEnum (w 2 2 1 0 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 770) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_771 : StepOkEnum (w 2 2 1 0 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 771) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_772 : StepOkEnum (w 2 2 1 0 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 772) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_773 : StepOkEnum (w 2 2 1 0 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 773) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_774 : StepOkEnum (w 2 2 1 1 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 774) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_775 : StepOkEnum (w 2 2 1 1 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 775) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_776 : StepOkEnum (w 2 2 1 1 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 776) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_777 : StepOkEnum (w 2 2 1 1 0 2 2 0) TaitColorPair.redBlue (cert.knownAt base 777) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_778 : StepOkEnum (w 2 2 1 1 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 778) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_779 : StepOkEnum (w 2 2 1 1 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 779) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
