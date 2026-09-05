import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 840–899. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_840 : StepOkEnum (w 0 0 1 0 1 0 1 1) TaitColorPair.redPurple (cert.knownAt base 840) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_841 : StepOkEnum (w 0 0 1 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 841) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({5, 6} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({0, 1, 4, 7} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_842 : StepOkEnum (w 0 0 1 0 1 2 0 2) TaitColorPair.redPurple (cert.knownAt base 842) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_843 : StepOkEnum (w 0 0 1 0 1 2 2 0) TaitColorPair.redPurple (cert.knownAt base 843) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_844 : StepOkEnum (w 0 0 1 0 2 0 2 1) TaitColorPair.redPurple (cert.knownAt base 844) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_845 : StepOkEnum (w 0 0 1 0 2 1 2 0) TaitColorPair.redPurple (cert.knownAt base 845) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_846 : StepOkEnum (w 0 0 1 1 0 0 1 1) TaitColorPair.redPurple (cert.knownAt base 846) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_847 : StepOkEnum (w 0 0 1 1 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 847) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({5, 6} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_848 : StepOkEnum (w 0 0 1 1 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 848) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_849 : StepOkEnum (w 0 0 1 1 0 2 2 0) TaitColorPair.redPurple (cert.knownAt base 849) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_850 : StepOkEnum (w 0 0 1 1 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 850) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_851 : StepOkEnum (w 0 0 1 1 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 851) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({4, 5} : Finset (Fin 8)) | 6 => ({4, 7} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({3, 4} : Finset (Fin 8)) | 10 => ({3, 6} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_852 : StepOkEnum (w 0 0 1 1 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 852) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({4, 6} : Finset (Fin 8)) | 3 => ({3, 4} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_853 : StepOkEnum (w 0 0 1 1 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 853) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({4, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_854 : StepOkEnum (w 0 0 1 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 854) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({3, 5} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_855 : StepOkEnum (w 0 0 1 1 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 855) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({5, 7} : Finset (Fin 8)) | 3 => ({3, 5} : Finset (Fin 8)) | 4 => ({0, 1, 5, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_856 : StepOkEnum (w 0 0 1 2 0 0 2 1) TaitColorPair.redPurple (cert.knownAt base 856) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_857 : StepOkEnum (w 0 0 1 2 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 857) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({5, 7} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_858 : StepOkEnum (w 0 0 1 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 858) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_859 : StepOkEnum (w 0 0 1 2 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 859) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_860 : StepOkEnum (w 0 0 2 0 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 860) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1, 3, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_861 : StepOkEnum (w 0 0 2 0 0 2 0 0) TaitColorPair.redBlue (cert.knownAt base 861) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_862 : StepOkEnum (w 0 0 2 0 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 862) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_863 : StepOkEnum (w 0 0 2 0 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 863) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_864 : StepOkEnum (w 0 0 2 0 2 0 2 2) TaitColorPair.redBlue (cert.knownAt base 864) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_865 : StepOkEnum (w 0 0 2 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 865) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_866 : StepOkEnum (w 0 0 2 0 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 866) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_867 : StepOkEnum (w 0 0 2 0 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 867) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1, 3, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_868 : StepOkEnum (w 0 0 2 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 868) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_869 : StepOkEnum (w 0 0 2 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 869) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_870 : StepOkEnum (w 0 0 2 1 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 870) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_871 : StepOkEnum (w 0 0 2 2 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 871) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_872 : StepOkEnum (w 0 0 2 2 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 872) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_873 : StepOkEnum (w 0 0 2 2 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 873) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_874 : StepOkEnum (w 0 0 2 2 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 874) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1, 4, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_875 : StepOkEnum (w 0 0 2 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 875) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_876 : StepOkEnum (w 0 0 2 2 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 876) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_877 : StepOkEnum (w 0 1 0 0 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 877) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_878 : StepOkEnum (w 0 1 0 0 0 1 0 0) TaitColorPair.redBlue (cert.knownAt base 878) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_879 : StepOkEnum (w 0 1 0 0 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 879) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_880 : StepOkEnum (w 0 1 0 0 1 0 1 1) TaitColorPair.redBlue (cert.knownAt base 880) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_881 : StepOkEnum (w 0 1 0 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 881) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 1} : Finset (Fin 8)) | 3 => ({0, 1} : Finset (Fin 8)) | 4 => ({0, 1} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_882 : StepOkEnum (w 0 1 0 0 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 882) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_883 : StepOkEnum (w 0 1 0 0 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 883) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_884 : StepOkEnum (w 0 1 0 0 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 884) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_885 : StepOkEnum (w 0 1 0 0 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 885) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_886 : StepOkEnum (w 0 1 0 0 2 1 2 0) TaitColorPair.redBlue (cert.knownAt base 886) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_887 : StepOkEnum (w 0 1 0 0 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 887) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_888 : StepOkEnum (w 0 1 0 1 0 0 1 1) TaitColorPair.redPurple (cert.knownAt base 888) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_889 : StepOkEnum (w 0 1 0 1 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 889) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({5, 6} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_890 : StepOkEnum (w 0 1 0 1 0 2 0 2) TaitColorPair.redPurple (cert.knownAt base 890) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_891 : StepOkEnum (w 0 1 0 1 0 2 2 0) TaitColorPair.redPurple (cert.knownAt base 891) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_892 : StepOkEnum (w 0 1 0 1 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 892) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_893 : StepOkEnum (w 0 1 0 1 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 893) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({4, 7} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({1, 2} : Finset (Fin 8)) | 6 => ({1, 2} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({1, 2} : Finset (Fin 8)) | 10 => ({1, 2} : Finset (Fin 8)) | 11 => ({1, 4} : Finset (Fin 8)) | 12 => ({1, 6} : Finset (Fin 8)) | 13 => ({1, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_894 : StepOkEnum (w 0 1 0 1 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 894) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 4} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_895 : StepOkEnum (w 0 1 0 1 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 895) (fun (k : Nat) => match k with | 0 => ({4, 7} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_896 : StepOkEnum (w 0 1 0 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 896) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_897 : StepOkEnum (w 0 1 0 1 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 897) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_898 : StepOkEnum (w 0 1 0 1 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 898) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_899 : StepOkEnum (w 0 1 0 1 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 899) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
