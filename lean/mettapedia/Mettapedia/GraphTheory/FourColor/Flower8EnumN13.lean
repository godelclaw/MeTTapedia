import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 780–839. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_780 : StepOkEnum (w 2 2 1 1 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 780) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_781 : StepOkEnum (w 2 2 1 1 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 781) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_782 : StepOkEnum (w 2 2 1 1 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 782) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_783 : StepOkEnum (w 2 2 1 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 783) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_784 : StepOkEnum (w 2 2 1 1 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 784) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_785 : StepOkEnum (w 2 2 1 1 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 785) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_786 : StepOkEnum (w 2 2 1 2 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 786) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_787 : StepOkEnum (w 2 2 1 2 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 787) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_788 : StepOkEnum (w 2 2 1 2 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 788) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_789 : StepOkEnum (w 2 2 1 2 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 789) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_790 : StepOkEnum (w 2 2 1 2 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 790) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_791 : StepOkEnum (w 2 2 1 2 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 791) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_792 : StepOkEnum (w 2 2 1 2 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 792) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_793 : StepOkEnum (w 2 2 1 2 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 793) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_794 : StepOkEnum (w 2 2 1 2 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 794) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_795 : StepOkEnum (w 2 2 1 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 795) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_796 : StepOkEnum (w 2 2 1 2 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 796) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_797 : StepOkEnum (w 2 2 1 2 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 797) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_798 : StepOkEnum (w 2 2 1 2 2 1 2 2) TaitColorPair.redBlue (cert.knownAt base 798) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_799 : StepOkEnum (w 2 2 1 2 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 799) (fun (k : Nat) => match k with | 0 => ({2, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_800 : StepOkEnum (w 2 2 1 2 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 800) (fun (k : Nat) => match k with | 0 => ({2, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_801 : StepOkEnum (w 2 2 2 0 0 0 2 0) TaitColorPair.redPurple (cert.knownAt base 801) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_802 : StepOkEnum (w 2 2 2 0 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 802) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_803 : StepOkEnum (w 2 2 2 0 1 0 1 2) TaitColorPair.redPurple (cert.knownAt base 803) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_804 : StepOkEnum (w 2 2 2 0 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 804) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_805 : StepOkEnum (w 2 2 2 0 1 2 0 1) TaitColorPair.redPurple (cert.knownAt base 805) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_806 : StepOkEnum (w 2 2 2 0 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 806) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_807 : StepOkEnum (w 2 2 2 0 2 0 1 1) TaitColorPair.redPurple (cert.knownAt base 807) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 5} : Finset (Fin 8)) | 4 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_808 : StepOkEnum (w 2 2 2 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 808) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_809 : StepOkEnum (w 2 2 2 0 2 2 0 2) TaitColorPair.redPurple (cert.knownAt base 809) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_810 : StepOkEnum (w 2 2 2 0 2 2 2 0) TaitColorPair.redPurple (cert.knownAt base 810) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_811 : StepOkEnum (w 2 2 2 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 811) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_812 : StepOkEnum (w 2 2 2 1 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 812) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_813 : StepOkEnum (w 2 2 2 1 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 813) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_814 : StepOkEnum (w 2 2 2 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 814) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_815 : StepOkEnum (w 2 2 2 1 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 815) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_816 : StepOkEnum (w 2 2 2 1 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 816) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_817 : StepOkEnum (w 2 2 2 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 817) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_818 : StepOkEnum (w 2 2 2 1 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 818) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_819 : StepOkEnum (w 2 2 2 1 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 819) (fun (k : Nat) => match k with | 0 => ({3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_820 : StepOkEnum (w 2 2 2 1 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 820) (fun (k : Nat) => match k with | 0 => ({3, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_821 : StepOkEnum (w 2 2 2 2 0 0 2 2) TaitColorPair.redPurple (cert.knownAt base 821) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_822 : StepOkEnum (w 2 2 2 2 0 1 0 1) TaitColorPair.redPurple (cert.knownAt base 822) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_823 : StepOkEnum (w 2 2 2 2 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 823) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_824 : StepOkEnum (w 2 2 2 2 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 824) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_825 : StepOkEnum (w 2 2 2 2 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 825) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_826 : StepOkEnum (w 2 2 2 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 826) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_827 : StepOkEnum (w 2 2 2 2 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 827) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_828 : StepOkEnum (w 2 2 2 2 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 828) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_829 : StepOkEnum (w 2 2 2 2 2 0 0 2) TaitColorPair.redPurple (cert.knownAt base 829) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_830 : StepOkEnum (w 2 2 2 2 2 0 2 0) TaitColorPair.redPurple (cert.knownAt base 830) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_831 : StepOkEnum (w 2 2 2 2 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 831) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_832 : StepOkEnum (w 2 2 2 2 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 832) (fun (k : Nat) => match k with | 0 => ({5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_833 : StepOkEnum (w 2 2 2 2 2 2 0 0) TaitColorPair.redPurple (cert.knownAt base 833) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_834 : StepOkEnum (w 2 2 2 2 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 834) (fun (k : Nat) => match k with | 0 => ({6, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_835 : StepOkEnum (w 2 2 2 2 2 2 2 2) TaitColorPair.redPurple (cert.knownAt base 835) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_836 : StepOkEnum (w 0 0 0 0 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 836) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 8)) | 1 => ({0, 1, 2, 6} : Finset (Fin 8)) | 2 => ({0, 1, 2, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_837 : StepOkEnum (w 0 0 1 0 0 0 1 0) TaitColorPair.redPurple (cert.knownAt base 837) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1, 3, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_838 : StepOkEnum (w 0 0 1 0 0 1 0 0) TaitColorPair.redBlue (cert.knownAt base 838) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({5, 6} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({5, 6} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_839 : StepOkEnum (w 0 0 1 0 0 2 1 2) TaitColorPair.redPurple (cert.knownAt base 839) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
