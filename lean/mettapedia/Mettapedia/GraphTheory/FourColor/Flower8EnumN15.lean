import Mettapedia.GraphTheory.FourColor.Flower8EnumData

/-! Nodes 900–959. -/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower8Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_900 : StepOkEnum (w 0 1 0 2 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 900) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_901 : StepOkEnum (w 0 1 0 2 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 901) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({1, 2} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_902 : StepOkEnum (w 0 1 0 2 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 902) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({1, 2} : Finset (Fin 8)) | 4 => ({1, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_903 : StepOkEnum (w 0 1 1 0 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 903) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_904 : StepOkEnum (w 0 1 1 0 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 904) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_905 : StepOkEnum (w 0 1 1 0 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 905) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_906 : StepOkEnum (w 0 1 1 0 0 2 2 0) TaitColorPair.redBlue (cert.knownAt base 906) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_907 : StepOkEnum (w 0 1 1 0 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 907) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_908 : StepOkEnum (w 0 1 1 0 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 908) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 3} : Finset (Fin 8)) | 2 => ({2, 5} : Finset (Fin 8)) | 3 => ({2, 7} : Finset (Fin 8)) | 4 => ({2, 7} : Finset (Fin 8)) | 5 => ({0, 3} : Finset (Fin 8)) | 6 => ({0, 3} : Finset (Fin 8)) | 7 => ({0, 5} : Finset (Fin 8)) | 8 => ({0, 5} : Finset (Fin 8)) | 9 => ({0, 7} : Finset (Fin 8)) | 10 => ({0, 7} : Finset (Fin 8)) | 11 => ({0, 7} : Finset (Fin 8)) | 12 => ({0, 7} : Finset (Fin 8)) | 13 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_909 : StepOkEnum (w 0 1 1 0 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 909) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 6} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_910 : StepOkEnum (w 0 1 1 0 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 910) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_911 : StepOkEnum (w 0 1 1 1 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 911) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 3} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_912 : StepOkEnum (w 0 1 1 2 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 912) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 8)) | 1 => ({2, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_913 : StepOkEnum (w 0 1 2 0 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 913) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 8)) | 1 => ({3, 7} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_914 : StepOkEnum (w 0 1 2 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 914) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_915 : StepOkEnum (w 0 1 2 0 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 915) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_916 : StepOkEnum (w 0 1 2 0 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 916) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_917 : StepOkEnum (w 0 1 2 0 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 917) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 8)) | 1 => ({0, 1, 3, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_918 : StepOkEnum (w 0 1 2 0 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 918) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_919 : StepOkEnum (w 0 1 2 0 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 919) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 6} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_920 : StepOkEnum (w 0 1 2 0 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 920) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_921 : StepOkEnum (w 0 1 2 1 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 921) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_922 : StepOkEnum (w 0 1 2 1 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 922) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_923 : StepOkEnum (w 0 1 2 1 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 923) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_924 : StepOkEnum (w 0 1 2 1 0 2 0 0) TaitColorPair.redBlue (cert.knownAt base 924) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_925 : StepOkEnum (w 0 1 2 1 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 925) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_926 : StepOkEnum (w 0 1 2 1 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 926) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_927 : StepOkEnum (w 0 1 2 1 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 927) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_928 : StepOkEnum (w 0 1 2 2 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 928) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 8)) | 1 => ({0, 1, 4, 7} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_929 : StepOkEnum (w 0 1 2 2 0 1 0 0) TaitColorPair.redBlue (cert.knownAt base 929) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_930 : StepOkEnum (w 0 1 2 2 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 930) (fun (k : Nat) => match k with | 0 => ({0, 1, 4, 6} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_931 : StepOkEnum (w 0 1 2 2 0 2 2 1) TaitColorPair.redBlue (cert.knownAt base 931) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_932 : StepOkEnum (w 0 1 2 2 1 0 1 1) TaitColorPair.redBlue (cert.knownAt base 932) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_933 : StepOkEnum (w 0 1 2 2 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 933) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 1} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_934 : StepOkEnum (w 0 1 2 2 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 934) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_935 : StepOkEnum (w 0 2 0 0 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 935) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_936 : StepOkEnum (w 0 2 0 0 0 2 0 0) TaitColorPair.redBlue (cert.knownAt base 936) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_937 : StepOkEnum (w 0 2 0 0 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 937) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_938 : StepOkEnum (w 0 2 0 0 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 938) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_939 : StepOkEnum (w 0 2 0 0 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 939) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_940 : StepOkEnum (w 0 2 0 0 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 940) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_941 : StepOkEnum (w 0 2 0 0 2 0 2 2) TaitColorPair.redBlue (cert.knownAt base 941) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_942 : StepOkEnum (w 0 2 0 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 942) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_943 : StepOkEnum (w 0 2 0 0 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 943) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_944 : StepOkEnum (w 0 2 0 0 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 944) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_945 : StepOkEnum (w 0 2 0 1 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 945) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 6} : Finset (Fin 8)) | 4 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_946 : StepOkEnum (w 0 2 0 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 946) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 4} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_947 : StepOkEnum (w 0 2 0 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 947) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_948 : StepOkEnum (w 0 2 0 2 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 948) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 5} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_949 : StepOkEnum (w 0 2 0 2 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 949) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_950 : StepOkEnum (w 0 2 0 2 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 950) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_951 : StepOkEnum (w 0 2 0 2 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 951) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_952 : StepOkEnum (w 0 2 0 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 952) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_953 : StepOkEnum (w 0 2 0 2 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 953) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 2} : Finset (Fin 8)) | 2 => ({0, 5} : Finset (Fin 8)) | 3 => ({0, 7} : Finset (Fin 8)) | 4 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_954 : StepOkEnum (w 0 2 0 2 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 954) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_955 : StepOkEnum (w 0 2 0 2 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 955) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_956 : StepOkEnum (w 0 2 0 2 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 956) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_957 : StepOkEnum (w 0 2 0 2 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 957) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 6} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_958 : StepOkEnum (w 0 2 0 2 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 958) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_959 : StepOkEnum (w 0 2 0 2 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 959) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 8)) | 1 => ({0, 7} : Finset (Fin 8)) | _ => (∅ : Finset (Fin 8))) := by
  decide +kernel

end Flower8Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
