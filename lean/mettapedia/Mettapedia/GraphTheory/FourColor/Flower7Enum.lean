import Mettapedia.GraphTheory.FourColor.KempeCertificateEnum

/-!
# Enumerated derivation certificate: `flower7_tangle.json` (ring 7)

Support words of the tangle (base) and 234 derivation nodes, each with a switch set per
listed noncrossing matching.  `ok` is decided in the kernel; `derivable` follows by
`CertificateEnum.derivable_of_ok`.
-/

namespace Mettapedia.GraphTheory.FourColor.KempeDerivation
namespace Flower7Enum

open GoertzelV24HexagonPairingTargetAwareBoundary

/-- a word from its digits -/
def w (d0 d1 d2 d3 d4 d5 d6 : Fin 3) : Word 7 :=
  ![tc d0, tc d1, tc d2, tc d3, tc d4, tc d5, tc d6]

def base : List (Word 7) := [
  w 0 0 0 0 1 0 2,
  w 0 0 0 0 1 2 0,
  w 0 0 0 0 2 0 1,
  w 0 0 0 0 2 1 0,
  w 0 0 0 1 0 2 0,
  w 0 0 0 1 1 2 1,
  w 0 0 0 1 2 0 0,
  w 0 0 0 1 2 1 1,
  w 0 0 0 2 0 1 0,
  w 0 0 0 2 1 0 0,
  w 0 0 0 2 1 2 2,
  w 0 0 0 2 2 1 2,
  w 0 0 1 0 1 2 1,
  w 0 0 1 0 2 0 0,
  w 0 0 1 0 2 1 1,
  w 0 0 1 0 2 2 2,
  w 0 0 1 1 0 1 2,
  w 0 0 1 1 0 2 1,
  w 0 0 1 1 1 0 2,
  w 0 0 1 1 2 0 1,
  w 0 0 1 1 2 1 0,
  w 0 0 1 2 0 1 1,
  w 0 0 1 2 0 2 2,
  w 0 0 1 2 1 0 1,
  w 0 0 1 2 1 1 0,
  w 0 0 2 0 1 0 0,
  w 0 0 2 0 1 1 1,
  w 0 0 2 0 1 2 2,
  w 0 0 2 0 2 1 2,
  w 0 0 2 1 0 1 1,
  w 0 0 2 1 0 2 2,
  w 0 0 2 1 2 0 2,
  w 0 0 2 1 2 2 0,
  w 0 0 2 2 0 1 2,
  w 0 0 2 2 0 2 1,
  w 0 0 2 2 1 0 2,
  w 0 0 2 2 1 2 0,
  w 0 0 2 2 2 0 1,
  w 0 1 0 0 0 0 2,
  w 0 1 0 0 2 1 1,
  w 0 1 0 0 2 2 2,
  w 0 1 0 1 0 1 2,
  w 0 1 0 1 1 0 2,
  w 0 1 0 1 2 0 1,
  w 0 1 0 2 0 0 0,
  w 0 1 0 2 0 2 2,
  w 0 1 1 0 0 1 2,
  w 0 1 1 1 0 0 2,
  w 0 1 1 1 0 2 0,
  w 0 1 1 1 1 1 2,
  w 0 1 1 1 1 2 1,
  w 0 1 1 2 1 0 0,
  w 0 1 1 2 1 2 2,
  w 0 1 1 2 2 1 2,
  w 0 1 2 0 0 0 0,
  w 0 1 2 0 0 2 2,
  w 0 1 2 0 1 0 1,
  w 0 1 2 0 1 1 0,
  w 0 1 2 0 2 0 2,
  w 0 1 2 0 2 2 0,
  w 0 1 2 1 0 0 1,
  w 0 1 2 1 1 0 0,
  w 0 1 2 1 1 1 1,
  w 0 1 2 1 1 2 2,
  w 0 1 2 1 2 1 2,
  w 0 1 2 2 0 0 2,
  w 0 1 2 2 0 2 0,
  w 0 1 2 2 1 1 2,
  w 0 1 2 2 1 2 1,
  w 0 1 2 2 2 1 1,
  w 0 1 2 2 2 2 2,
  w 0 2 0 0 0 0 1,
  w 0 2 0 0 1 1 1,
  w 0 2 0 0 1 2 2,
  w 0 2 0 1 0 0 0,
  w 0 2 0 1 0 1 1,
  w 0 2 0 2 0 2 1,
  w 0 2 0 2 1 0 2,
  w 0 2 0 2 2 0 1,
  w 0 2 1 0 0 0 0,
  w 0 2 1 0 0 1 1,
  w 0 2 1 0 1 0 1,
  w 0 2 1 0 1 1 0,
  w 0 2 1 0 2 0 2,
  w 0 2 1 0 2 2 0,
  w 0 2 1 1 0 0 1,
  w 0 2 1 1 0 1 0,
  w 0 2 1 1 1 1 1,
  w 0 2 1 1 1 2 2,
  w 0 2 1 1 2 1 2,
  w 0 2 1 1 2 2 1,
  w 0 2 1 2 0 0 2,
  w 0 2 1 2 1 2 1,
  w 0 2 1 2 2 0 0,
  w 0 2 1 2 2 1 1,
  w 0 2 1 2 2 2 2,
  w 0 2 2 0 0 2 1,
  w 0 2 2 1 1 2 1,
  w 0 2 2 1 2 0 0,
  w 0 2 2 1 2 1 1,
  w 0 2 2 2 0 0 1,
  w 0 2 2 2 0 1 0,
  w 0 2 2 2 2 1 2,
  w 0 2 2 2 2 2 1,
  w 1 0 0 0 0 0 2,
  w 1 0 0 0 0 2 0,
  w 1 0 0 0 1 1 2,
  w 1 0 0 0 1 2 1,
  w 1 0 0 1 1 0 2,
  w 1 0 0 2 0 1 1,
  w 1 0 0 2 0 2 2,
  w 1 0 0 2 2 0 2,
  w 1 0 1 0 0 1 2,
  w 1 0 1 0 1 0 2,
  w 1 0 1 0 2 1 0,
  w 1 0 1 1 1 1 2,
  w 1 0 1 1 2 0 0,
  w 1 0 1 1 2 2 2,
  w 1 0 1 2 1 1 1,
  w 1 0 1 2 1 2 2,
  w 1 0 2 0 0 0 0,
  w 1 0 2 0 0 1 1,
  w 1 0 2 0 0 2 2,
  w 1 0 2 0 1 1 0,
  w 1 0 2 0 2 0 2,
  w 1 0 2 1 0 0 1,
  w 1 0 2 1 0 1 0,
  w 1 0 2 1 1 1 1,
  w 1 0 2 1 1 2 2,
  w 1 0 2 1 2 1 2,
  w 1 0 2 1 2 2 1,
  w 1 0 2 2 0 0 2,
  w 1 0 2 2 0 2 0,
  w 1 0 2 2 1 1 2,
  w 1 0 2 2 1 2 1,
  w 1 0 2 2 2 0 0,
  w 1 0 2 2 2 2 2,
  w 1 1 0 0 0 1 2,
  w 1 1 0 0 1 0 2,
  w 1 1 0 0 1 2 0,
  w 1 1 0 0 2 0 1,
  w 1 1 0 0 2 1 0,
  w 1 1 0 1 0 2 0,
  w 1 1 0 1 2 0 0,
  w 1 1 0 1 2 1 1,
  w 1 1 0 1 2 2 2,
  w 1 1 0 2 0 0 1,
  w 1 1 0 2 0 1 0,
  w 1 1 0 2 1 0 0,
  w 1 1 0 2 1 2 2,
  w 1 1 1 0 0 2 0,
  w 1 1 1 0 1 2 1,
  w 1 1 1 0 2 0 0,
  w 1 1 1 0 2 1 1,
  w 1 1 1 1 0 1 2,
  w 1 1 1 1 0 2 1,
  w 1 1 1 1 2 0 1,
  w 1 1 1 1 2 1 0,
  w 1 1 1 2 0 1 1,
  w 1 1 1 2 0 2 2,
  w 1 1 1 2 1 0 1,
  w 1 1 1 2 2 0 2,
  w 1 1 2 0 1 0 0,
  w 1 1 2 0 1 2 2,
  w 1 1 2 0 2 1 2,
  w 1 1 2 0 2 2 1,
  w 1 1 2 1 0 0 0,
  w 1 1 2 1 0 1 1,
  w 1 1 2 1 0 2 2,
  w 1 1 2 1 2 0 2,
  w 1 1 2 2 0 1 2,
  w 1 1 2 2 0 2 1,
  w 1 1 2 2 1 0 2,
  w 1 1 2 2 1 2 0,
  w 1 1 2 2 2 1 0,
  w 1 2 0 0 0 0 0,
  w 1 2 0 0 0 2 2,
  w 1 2 0 0 1 0 1,
  w 1 2 0 0 1 1 0,
  w 1 2 0 0 2 0 2,
  w 1 2 0 0 2 2 0,
  w 1 2 0 1 0 0 1,
  w 1 2 0 1 0 1 0,
  w 1 2 0 1 1 0 0,
  w 1 2 0 1 1 1 1,
  w 1 2 0 1 2 1 2,
  w 1 2 0 1 2 2 1,
  w 1 2 0 2 0 2 0,
  w 1 2 0 2 1 1 2,
  w 1 2 0 2 2 0 0,
  w 1 2 0 2 2 1 1,
  w 1 2 0 2 2 2 2,
  w 1 2 1 0 1 0 0,
  w 1 2 1 0 1 1 1,
  w 1 2 1 1 0 0 0,
  w 1 2 1 1 0 2 2,
  w 1 2 1 1 1 1 0,
  w 1 2 1 2 0 1 2,
  w 1 2 1 2 1 2 0,
  w 1 2 1 2 2 1 0,
  w 1 2 2 0 0 2 0,
  w 1 2 2 0 2 0 0,
  w 1 2 2 0 2 1 1,
  w 1 2 2 1 1 2 0,
  w 1 2 2 2 1 0 1,
  w 1 2 2 2 1 1 0,
  w 1 2 2 2 2 0 2,
  w 1 2 2 2 2 2 0,
  w 2 0 0 0 0 0 1,
  w 2 0 0 0 0 1 0,
  w 2 0 0 0 2 1 2,
  w 2 0 0 0 2 2 1,
  w 2 0 0 1 0 1 1,
  w 2 0 0 1 0 2 2,
  w 2 0 0 1 1 0 1,
  w 2 0 0 2 2 0 1,
  w 2 0 1 0 0 0 0,
  w 2 0 1 0 0 1 1,
  w 2 0 1 0 0 2 2,
  w 2 0 1 0 1 0 1,
  w 2 0 1 0 2 2 0,
  w 2 0 1 1 0 0 1,
  w 2 0 1 1 0 1 0,
  w 2 0 1 1 1 0 0,
  w 2 0 1 1 1 1 1,
  w 2 0 1 1 2 1 2,
  w 2 0 1 1 2 2 1,
  w 2 0 1 2 0 0 2,
  w 2 0 1 2 0 2 0,
  w 2 0 1 2 1 1 2,
  w 2 0 1 2 1 2 1,
  w 2 0 1 2 2 1 1,
  w 2 0 1 2 2 2 2,
  w 2 0 2 0 0 2 1,
  w 2 0 2 0 1 2 0,
  w 2 0 2 0 2 0 1,
  w 2 0 2 1 2 1 1,
  w 2 0 2 1 2 2 2,
  w 2 0 2 2 1 0 0,
  w 2 0 2 2 1 1 1,
  w 2 0 2 2 2 2 1,
  w 2 1 0 0 0 0 0,
  w 2 1 0 0 0 1 1,
  w 2 1 0 0 1 0 1,
  w 2 1 0 0 1 1 0,
  w 2 1 0 0 2 0 2,
  w 2 1 0 0 2 2 0,
  w 2 1 0 1 0 1 0,
  w 2 1 0 1 1 0 0,
  w 2 1 0 1 1 1 1,
  w 2 1 0 1 1 2 2,
  w 2 1 0 1 2 2 1,
  w 2 1 0 2 0 0 2,
  w 2 1 0 2 0 2 0,
  w 2 1 0 2 1 1 2,
  w 2 1 0 2 1 2 1,
  w 2 1 0 2 2 0 0,
  w 2 1 0 2 2 2 2,
  w 2 1 1 0 0 1 0,
  w 2 1 1 0 1 0 0,
  w 2 1 1 0 1 2 2,
  w 2 1 1 1 1 0 1,
  w 2 1 1 1 1 1 0,
  w 2 1 1 1 2 0 2,
  w 2 1 1 1 2 2 0,
  w 2 1 1 2 2 1 0,
  w 2 1 2 0 2 0 0,
  w 2 1 2 0 2 2 2,
  w 2 1 2 1 0 2 1,
  w 2 1 2 1 1 2 0,
  w 2 1 2 1 2 1 0,
  w 2 1 2 2 0 0 0,
  w 2 1 2 2 0 1 1,
  w 2 1 2 2 2 2 0,
  w 2 2 0 0 0 2 1,
  w 2 2 0 0 1 0 2,
  w 2 2 0 0 1 2 0,
  w 2 2 0 0 2 0 1,
  w 2 2 0 0 2 1 0,
  w 2 2 0 1 0 0 2,
  w 2 2 0 1 0 2 0,
  w 2 2 0 1 2 0 0,
  w 2 2 0 1 2 1 1,
  w 2 2 0 2 0 1 0,
  w 2 2 0 2 1 0 0,
  w 2 2 0 2 1 1 1,
  w 2 2 0 2 1 2 2,
  w 2 2 1 0 1 1 2,
  w 2 2 1 0 1 2 1,
  w 2 2 1 0 2 0 0,
  w 2 2 1 0 2 1 1,
  w 2 2 1 1 0 1 2,
  w 2 2 1 1 0 2 1,
  w 2 2 1 1 1 2 0,
  w 2 2 1 1 2 0 1,
  w 2 2 1 1 2 1 0,
  w 2 2 1 2 0 0 0,
  w 2 2 1 2 0 1 1,
  w 2 2 1 2 0 2 2,
  w 2 2 1 2 1 0 1,
  w 2 2 2 0 0 1 0,
  w 2 2 2 0 1 0 0,
  w 2 2 2 0 1 2 2,
  w 2 2 2 0 2 1 2,
  w 2 2 2 1 0 1 1,
  w 2 2 2 1 0 2 2,
  w 2 2 2 1 1 0 1,
  w 2 2 2 1 2 0 2,
  w 2 2 2 2 0 1 2,
  w 2 2 2 2 0 2 1,
  w 2 2 2 2 1 0 2,
  w 2 2 2 2 1 2 0]

def nodes : List (Word 7 × TaitColorPair × (Nat → Finset (Fin 7))) := [
  (w 0 0 0 0 0 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 0 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 1, 2, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 0 1 1 2, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 2 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 5, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 2 2 0 2, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 2 2 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 0 2 2 1, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 1 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 1 1 0 1, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 1 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 2 2 1 0, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 0 0 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 0 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 0 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 0 2 0 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 1 1 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 1 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({3, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 2 0 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 2 1 0 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 2 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 2 2 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 2 2 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 0 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3, 4, 6} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 0 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 0 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 0 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 0 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 1 2 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 1 2 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 1 2 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 2 0 0 1, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 2 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 2 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({4, 5} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 1 2 2 2 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 2 0 0 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 3} : Finset (Fin 7)) | 3 => ({1, 3} : Finset (Fin 7)) | 4 => ({0, 1, 5, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 2 1 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 3, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 2 1 2 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({1, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 2 2 2 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 0 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 0 1 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 0 2 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 0 2 2 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 1 0 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 1 1 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 1 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 1 2 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 1 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 2 0 1 2, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 2 1 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({3, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 0 2 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 1 0 0 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 1 1 1 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 1 2 0 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({2, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 1 2 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({2, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 0 0 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 0 1 0 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 0 1 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 0 2 0 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 0 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 1 0 0 2, TaitColorPair.bluePurple, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 1 0 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 1 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 1 2 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({4, 5} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 2 1 0 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 2 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 2 2 2 1 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 0 2 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 0 2 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 0 2 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1, 2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 1 0 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 1 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 1 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 1 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 1 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 2 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 2 1 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 2 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 0 2 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 0 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 0 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 0 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 1 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 2, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 1 0 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 1 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 1 2 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 2 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 2 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 2 1 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 2 2 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 1 2 2 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 2 0 1 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 3, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 2 0 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 2 1 1 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 0 2 2 2 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 0 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 1 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 1 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 1 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 2 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 2 2 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 0 2 2 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 0 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 0 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 0 2 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 1 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 1 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 2 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 2 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 1 2 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 0 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 0 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 0 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 1 1 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 1 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 1 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 1 2 2 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 0 0 0 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 0 1 1 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 0 2 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 0 2 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 0 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 0 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 0 1 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 0 2 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 0 2 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 1 0 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 1 1 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 1 2 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 1 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 2 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 2 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 1 2 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 0 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 0 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 0 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 0 2 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 1 0 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 1 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 1 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 1 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 1 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 2 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 2 0 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 1 2 2 2 0 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 0 1 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 0 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({1, 2, 3, 6} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 0 1 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 1 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 1 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 1 2 0 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 1 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 2 0 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 2 0 2 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 2 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 2 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 0 2 2 1 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 1 0 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 1 0 2 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 1 1 1 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 1 2 2 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 0 0 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 0 1 0 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 0 2 1 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 1 0 0 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 1 0 2 0, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 1 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 1 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 1 2 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({3, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 2 0 0 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 2, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 2 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 2 1 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 0 2 2 2 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 0 0 0 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 0 1 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 0 1 2 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 0 2 2 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 0 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 0 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 0 2 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 0 2 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 1 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 1 0 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 1 0 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 2 0 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 2 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 2 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 2 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 1 2 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 0 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 0 0 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 0 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 0 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 0 2 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 1 0 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 1 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 1 2 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 2 0 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 2 1 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 2 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 1 2 2 2 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 0 0 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 1 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 1 1 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 1 2 2 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 2 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 2 2 1 2, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 0 2 2 2 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 0 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 0 0 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 0 2 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 1 1 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 2 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 2 2 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 1 2 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 0 0 0 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 0 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 0 2 2 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 1 0 0 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 1 1 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 1 2 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({3, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 2 2 0 1, TaitColorPair.redPurple, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 2 2 2 2 2 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 1 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 1 1 1 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 1 2 2 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 2 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 2 1 1 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 0 2 2 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 0 0 0 2, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 0 0 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 1 1 1 2 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 0 0 0 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 0 2 0 0 1 0, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7)))),
  (w 0 1 0 1 0 2 1, TaitColorPair.redBlue, (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))))]

def cert : CertificateEnum 7 := ⟨nodes⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_0 : StepOkEnum (w 0 0 0 0 0 1 2) TaitColorPair.redBlue (cert.knownAt base 0) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_1 : StepOkEnum (w 0 0 0 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 1) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 1, 2, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_2 : StepOkEnum (w 0 0 1 0 1 1 2) TaitColorPair.bluePurple (cert.knownAt base 2) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_3 : StepOkEnum (w 0 0 1 2 0 0 0) TaitColorPair.redBlue (cert.knownAt base 3) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 5, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_4 : StepOkEnum (w 0 0 1 2 2 0 2) TaitColorPair.bluePurple (cert.knownAt base 4) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_5 : StepOkEnum (w 0 0 1 2 2 2 0) TaitColorPair.redPurple (cert.knownAt base 5) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_6 : StepOkEnum (w 0 0 2 0 2 2 1) TaitColorPair.bluePurple (cert.knownAt base 6) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_7 : StepOkEnum (w 0 0 2 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 7) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_8 : StepOkEnum (w 0 0 2 1 1 0 1) TaitColorPair.bluePurple (cert.knownAt base 8) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_9 : StepOkEnum (w 0 0 2 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 9) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_10 : StepOkEnum (w 0 0 2 2 2 1 0) TaitColorPair.bluePurple (cert.knownAt base 10) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_11 : StepOkEnum (w 0 1 0 0 0 2 0) TaitColorPair.redPurple (cert.knownAt base 11) (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_12 : StepOkEnum (w 0 1 0 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 12) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_13 : StepOkEnum (w 0 1 0 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 13) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_14 : StepOkEnum (w 0 1 0 0 2 0 0) TaitColorPair.redPurple (cert.knownAt base 14) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_15 : StepOkEnum (w 0 1 0 1 1 2 0) TaitColorPair.redPurple (cert.knownAt base 15) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_16 : StepOkEnum (w 0 1 0 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 16) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({3, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_17 : StepOkEnum (w 0 1 0 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 17) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_18 : StepOkEnum (w 0 1 0 2 1 0 1) TaitColorPair.redPurple (cert.knownAt base 18) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_19 : StepOkEnum (w 0 1 0 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 19) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_20 : StepOkEnum (w 0 1 0 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 20) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_21 : StepOkEnum (w 0 1 0 2 2 2 0) TaitColorPair.redPurple (cert.knownAt base 21) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_22 : StepOkEnum (w 0 1 1 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 22) (fun (k : Nat) => match k with | 0 => ({2, 3, 4, 6} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_23 : StepOkEnum (w 0 1 1 0 1 0 2) TaitColorPair.redBlue (cert.knownAt base 23) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_24 : StepOkEnum (w 0 1 1 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 24) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_25 : StepOkEnum (w 0 1 1 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 25) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_26 : StepOkEnum (w 0 1 1 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 26) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_27 : StepOkEnum (w 0 1 1 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 27) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_28 : StepOkEnum (w 0 1 1 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 28) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_29 : StepOkEnum (w 0 1 1 1 2 2 2) TaitColorPair.redPurple (cert.knownAt base 29) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_30 : StepOkEnum (w 0 1 1 2 0 0 1) TaitColorPair.bluePurple (cert.knownAt base 30) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_31 : StepOkEnum (w 0 1 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 31) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_32 : StepOkEnum (w 0 1 1 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 32) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({4, 5} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_33 : StepOkEnum (w 0 1 1 2 2 2 1) TaitColorPair.redPurple (cert.knownAt base 33) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_34 : StepOkEnum (w 0 1 2 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 34) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 3} : Finset (Fin 7)) | 3 => ({1, 3} : Finset (Fin 7)) | 4 => ({0, 1, 5, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_35 : StepOkEnum (w 0 1 2 1 0 1 0) TaitColorPair.redBlue (cert.knownAt base 35) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 3, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_36 : StepOkEnum (w 0 1 2 1 2 2 1) TaitColorPair.redBlue (cert.knownAt base 36) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({1, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_37 : StepOkEnum (w 0 1 2 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 37) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_38 : StepOkEnum (w 0 2 0 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 38) (fun (k : Nat) => match k with | 0 => ({0, 2, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_39 : StepOkEnum (w 0 2 0 0 1 0 0) TaitColorPair.redBlue (cert.knownAt base 39) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_40 : StepOkEnum (w 0 2 0 0 2 1 2) TaitColorPair.redPurple (cert.knownAt base 40) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_41 : StepOkEnum (w 0 2 0 0 2 2 1) TaitColorPair.redPurple (cert.knownAt base 41) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_42 : StepOkEnum (w 0 2 0 1 0 2 2) TaitColorPair.redPurple (cert.knownAt base 42) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_43 : StepOkEnum (w 0 2 0 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 43) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_44 : StepOkEnum (w 0 2 0 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 44) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_45 : StepOkEnum (w 0 2 0 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 45) (fun (k : Nat) => match k with | 0 => ({3, 5} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_46 : StepOkEnum (w 0 2 0 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 46) (fun (k : Nat) => match k with | 0 => ({3, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_47 : StepOkEnum (w 0 2 0 2 0 1 2) TaitColorPair.bluePurple (cert.knownAt base 47) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_48 : StepOkEnum (w 0 2 0 2 1 2 0) TaitColorPair.redPurple (cert.knownAt base 48) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({3, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_49 : StepOkEnum (w 0 2 0 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 49) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_50 : StepOkEnum (w 0 2 1 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 50) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_51 : StepOkEnum (w 0 2 1 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 51) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_52 : StepOkEnum (w 0 2 1 2 0 2 0) TaitColorPair.redBlue (cert.knownAt base 52) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({2, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_53 : StepOkEnum (w 0 2 1 2 1 1 2) TaitColorPair.redBlue (cert.knownAt base 53) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({2, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_54 : StepOkEnum (w 0 2 2 0 0 1 2) TaitColorPair.redPurple (cert.knownAt base 54) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_55 : StepOkEnum (w 0 2 2 0 1 0 2) TaitColorPair.redPurple (cert.knownAt base 55) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_56 : StepOkEnum (w 0 2 2 0 1 2 0) TaitColorPair.redPurple (cert.knownAt base 56) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_57 : StepOkEnum (w 0 2 2 0 2 0 1) TaitColorPair.redPurple (cert.knownAt base 57) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_58 : StepOkEnum (w 0 2 2 0 2 1 0) TaitColorPair.redBlue (cert.knownAt base 58) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_59 : StepOkEnum (w 0 2 2 1 0 0 2) TaitColorPair.bluePurple (cert.knownAt base 59) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_60 : StepOkEnum (w 0 2 2 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 60) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_61 : StepOkEnum (w 0 2 2 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 61) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_62 : StepOkEnum (w 0 2 2 1 2 2 2) TaitColorPair.redPurple (cert.knownAt base 62) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({4, 5} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_63 : StepOkEnum (w 0 2 2 2 1 0 0) TaitColorPair.redPurple (cert.knownAt base 63) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_64 : StepOkEnum (w 0 2 2 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 64) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_65 : StepOkEnum (w 0 2 2 2 1 2 2) TaitColorPair.redPurple (cert.knownAt base 65) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_66 : StepOkEnum (w 1 0 0 0 2 0 0) TaitColorPair.redBlue (cert.knownAt base 66) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_67 : StepOkEnum (w 1 0 0 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 67) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_68 : StepOkEnum (w 1 0 0 0 2 2 2) TaitColorPair.redBlue (cert.knownAt base 68) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1, 2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_69 : StepOkEnum (w 1 0 0 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 69) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_70 : StepOkEnum (w 1 0 0 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 70) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_71 : StepOkEnum (w 1 0 0 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 71) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_72 : StepOkEnum (w 1 0 0 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 72) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_73 : StepOkEnum (w 1 0 0 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 73) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_74 : StepOkEnum (w 1 0 0 2 0 0 0) TaitColorPair.redBlue (cert.knownAt base 74) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_75 : StepOkEnum (w 1 0 0 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 75) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_76 : StepOkEnum (w 1 0 0 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 76) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_77 : StepOkEnum (w 1 0 0 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 77) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_78 : StepOkEnum (w 1 0 1 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 78) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_79 : StepOkEnum (w 1 0 1 0 1 2 0) TaitColorPair.redBlue (cert.knownAt base 79) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_80 : StepOkEnum (w 1 0 1 0 2 0 1) TaitColorPair.redBlue (cert.knownAt base 80) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_81 : StepOkEnum (w 1 0 1 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 81) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 2, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_82 : StepOkEnum (w 1 0 1 1 0 2 0) TaitColorPair.redBlue (cert.knownAt base 82) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_83 : StepOkEnum (w 1 0 1 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 83) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_84 : StepOkEnum (w 1 0 1 1 2 1 1) TaitColorPair.redBlue (cert.knownAt base 84) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_85 : StepOkEnum (w 1 0 1 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 85) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_86 : StepOkEnum (w 1 0 1 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 86) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_87 : StepOkEnum (w 1 0 1 2 1 0 0) TaitColorPair.redBlue (cert.knownAt base 87) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_88 : StepOkEnum (w 1 0 1 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 88) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_89 : StepOkEnum (w 1 0 1 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 89) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_90 : StepOkEnum (w 1 0 2 0 1 0 1) TaitColorPair.redBlue (cert.knownAt base 90) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 3, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_91 : StepOkEnum (w 1 0 2 0 2 2 0) TaitColorPair.redBlue (cert.knownAt base 91) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_92 : StepOkEnum (w 1 0 2 1 1 0 0) TaitColorPair.redBlue (cert.knownAt base 92) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_93 : StepOkEnum (w 1 0 2 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 93) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_94 : StepOkEnum (w 1 1 0 0 0 2 1) TaitColorPair.redBlue (cert.knownAt base 94) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_95 : StepOkEnum (w 1 1 0 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 95) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_96 : StepOkEnum (w 1 1 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 96) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_97 : StepOkEnum (w 1 1 0 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 97) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_98 : StepOkEnum (w 1 1 0 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 98) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_99 : StepOkEnum (w 1 1 0 2 2 1 2) TaitColorPair.redBlue (cert.knownAt base 99) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_100 : StepOkEnum (w 1 1 0 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 100) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 6} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_101 : StepOkEnum (w 1 1 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 101) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_102 : StepOkEnum (w 1 1 1 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 102) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_103 : StepOkEnum (w 1 1 1 0 2 2 2) TaitColorPair.redBlue (cert.knownAt base 103) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_104 : StepOkEnum (w 1 1 1 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 104) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_105 : StepOkEnum (w 1 1 1 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 105) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_106 : StepOkEnum (w 1 1 1 2 0 0 0) TaitColorPair.redBlue (cert.knownAt base 106) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_107 : StepOkEnum (w 1 1 1 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 107) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_108 : StepOkEnum (w 1 1 1 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 108) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_109 : StepOkEnum (w 1 1 2 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 109) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_110 : StepOkEnum (w 1 1 2 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 110) (fun (k : Nat) => match k with | 0 => ({0, 1, 3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_111 : StepOkEnum (w 1 1 2 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 111) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_112 : StepOkEnum (w 1 1 2 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 112) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_113 : StepOkEnum (w 1 1 2 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 113) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_114 : StepOkEnum (w 1 1 2 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 114) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_115 : StepOkEnum (w 1 1 2 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 115) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_116 : StepOkEnum (w 1 2 0 0 0 1 1) TaitColorPair.redBlue (cert.knownAt base 116) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_117 : StepOkEnum (w 1 2 0 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 117) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_118 : StepOkEnum (w 1 2 0 2 0 0 2) TaitColorPair.redBlue (cert.knownAt base 118) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_119 : StepOkEnum (w 1 2 0 2 1 2 1) TaitColorPair.redBlue (cert.knownAt base 119) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_120 : StepOkEnum (w 1 2 1 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 120) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_121 : StepOkEnum (w 1 2 1 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 121) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_122 : StepOkEnum (w 1 2 1 0 1 2 2) TaitColorPair.redBlue (cert.knownAt base 122) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_123 : StepOkEnum (w 1 2 1 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 123) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_124 : StepOkEnum (w 1 2 1 0 2 2 1) TaitColorPair.redBlue (cert.knownAt base 124) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_125 : StepOkEnum (w 1 2 1 1 0 1 1) TaitColorPair.redBlue (cert.knownAt base 125) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_126 : StepOkEnum (w 1 2 1 1 1 0 1) TaitColorPair.redBlue (cert.knownAt base 126) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 2} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_127 : StepOkEnum (w 1 2 1 1 2 0 2) TaitColorPair.redBlue (cert.knownAt base 127) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_128 : StepOkEnum (w 1 2 1 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 128) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_129 : StepOkEnum (w 1 2 1 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 129) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_130 : StepOkEnum (w 1 2 1 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 130) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_131 : StepOkEnum (w 1 2 1 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 131) (fun (k : Nat) => match k with | 0 => ({0, 2} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_132 : StepOkEnum (w 1 2 2 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 132) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_133 : StepOkEnum (w 1 2 2 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 133) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_134 : StepOkEnum (w 1 2 2 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 134) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_135 : StepOkEnum (w 1 2 2 0 2 2 2) TaitColorPair.redBlue (cert.knownAt base 135) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_136 : StepOkEnum (w 1 2 2 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 136) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_137 : StepOkEnum (w 1 2 2 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 137) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_138 : StepOkEnum (w 1 2 2 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 138) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_139 : StepOkEnum (w 1 2 2 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 139) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_140 : StepOkEnum (w 1 2 2 1 2 1 0) TaitColorPair.redBlue (cert.knownAt base 140) (fun (k : Nat) => match k with | 0 => ({0, 3} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_141 : StepOkEnum (w 1 2 2 2 0 0 0) TaitColorPair.redBlue (cert.knownAt base 141) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_142 : StepOkEnum (w 1 2 2 2 0 1 1) TaitColorPair.redBlue (cert.knownAt base 142) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_143 : StepOkEnum (w 1 2 2 2 0 2 2) TaitColorPair.redBlue (cert.knownAt base 143) (fun (k : Nat) => match k with | 0 => ({0, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_144 : StepOkEnum (w 2 0 0 0 1 0 0) TaitColorPair.redBlue (cert.knownAt base 144) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_145 : StepOkEnum (w 2 0 0 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 145) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({1, 2, 3, 6} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_146 : StepOkEnum (w 2 0 0 0 1 2 2) TaitColorPair.redPurple (cert.knownAt base 146) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_147 : StepOkEnum (w 2 0 0 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 147) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_148 : StepOkEnum (w 2 0 0 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 148) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_149 : StepOkEnum (w 2 0 0 1 2 0 2) TaitColorPair.redPurple (cert.knownAt base 149) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({1, 2} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_150 : StepOkEnum (w 2 0 0 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 150) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_151 : StepOkEnum (w 2 0 0 2 0 1 2) TaitColorPair.redPurple (cert.knownAt base 151) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_152 : StepOkEnum (w 2 0 0 2 0 2 1) TaitColorPair.redPurple (cert.knownAt base 152) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({1, 2} : Finset (Fin 7)) | 4 => ({0, 1, 4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_153 : StepOkEnum (w 2 0 0 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 153) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_154 : StepOkEnum (w 2 0 0 2 1 2 0) TaitColorPair.redBlue (cert.knownAt base 154) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_155 : StepOkEnum (w 2 0 0 2 2 1 0) TaitColorPair.redPurple (cert.knownAt base 155) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_156 : StepOkEnum (w 2 0 1 0 1 1 0) TaitColorPair.redBlue (cert.knownAt base 156) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({2, 3} : Finset (Fin 7)) | 4 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_157 : StepOkEnum (w 2 0 1 0 2 0 2) TaitColorPair.redBlue (cert.knownAt base 157) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_158 : StepOkEnum (w 2 0 1 1 1 2 2) TaitColorPair.redBlue (cert.knownAt base 158) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_159 : StepOkEnum (w 2 0 1 2 2 0 0) TaitColorPair.redBlue (cert.knownAt base 159) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_160 : StepOkEnum (w 2 0 2 0 0 1 2) TaitColorPair.redPurple (cert.knownAt base 160) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 1, 2, 6} : Finset (Fin 7)) | 4 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_161 : StepOkEnum (w 2 0 2 0 1 0 2) TaitColorPair.redPurple (cert.knownAt base 161) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_162 : StepOkEnum (w 2 0 2 0 2 1 0) TaitColorPair.redPurple (cert.knownAt base 162) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_163 : StepOkEnum (w 2 0 2 1 0 0 2) TaitColorPair.redPurple (cert.knownAt base 163) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_164 : StepOkEnum (w 2 0 2 1 0 2 0) TaitColorPair.redPurple (cert.knownAt base 164) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_165 : StepOkEnum (w 2 0 2 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 165) (fun (k : Nat) => match k with | 0 => ({4, 5} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_166 : StepOkEnum (w 2 0 2 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 166) (fun (k : Nat) => match k with | 0 => ({4, 6} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_167 : StepOkEnum (w 2 0 2 1 2 0 0) TaitColorPair.redBlue (cert.knownAt base 167) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({3, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_168 : StepOkEnum (w 2 0 2 2 0 0 1) TaitColorPair.redPurple (cert.knownAt base 168) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 1, 2, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_169 : StepOkEnum (w 2 0 2 2 0 1 0) TaitColorPair.redBlue (cert.knownAt base 169) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_170 : StepOkEnum (w 2 0 2 2 1 2 2) TaitColorPair.redPurple (cert.knownAt base 170) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_171 : StepOkEnum (w 2 0 2 2 2 1 2) TaitColorPair.redPurple (cert.knownAt base 171) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_172 : StepOkEnum (w 2 1 0 0 0 2 2) TaitColorPair.redBlue (cert.knownAt base 172) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_173 : StepOkEnum (w 2 1 0 1 0 0 1) TaitColorPair.redBlue (cert.knownAt base 173) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_174 : StepOkEnum (w 2 1 0 1 2 1 2) TaitColorPair.redBlue (cert.knownAt base 174) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_175 : StepOkEnum (w 2 1 0 2 2 1 1) TaitColorPair.redBlue (cert.knownAt base 175) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_176 : StepOkEnum (w 2 1 1 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 176) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_177 : StepOkEnum (w 2 1 1 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 177) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_178 : StepOkEnum (w 2 1 1 0 2 1 2) TaitColorPair.redBlue (cert.knownAt base 178) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_179 : StepOkEnum (w 2 1 1 0 2 2 1) TaitColorPair.redBlue (cert.knownAt base 179) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_180 : StepOkEnum (w 2 1 1 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 180) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_181 : StepOkEnum (w 2 1 1 1 0 1 1) TaitColorPair.redBlue (cert.knownAt base 181) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 2} : Finset (Fin 7)) | 2 => ({1, 4} : Finset (Fin 7)) | 3 => ({1, 6} : Finset (Fin 7)) | 4 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_182 : StepOkEnum (w 2 1 1 1 0 2 2) TaitColorPair.redBlue (cert.knownAt base 182) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_183 : StepOkEnum (w 2 1 1 2 0 1 2) TaitColorPair.redBlue (cert.knownAt base 183) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_184 : StepOkEnum (w 2 1 1 2 0 2 1) TaitColorPair.redBlue (cert.knownAt base 184) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_185 : StepOkEnum (w 2 1 1 2 1 0 2) TaitColorPair.redBlue (cert.knownAt base 185) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_186 : StepOkEnum (w 2 1 1 2 1 2 0) TaitColorPair.redBlue (cert.knownAt base 186) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_187 : StepOkEnum (w 2 1 1 2 2 0 1) TaitColorPair.redBlue (cert.knownAt base 187) (fun (k : Nat) => match k with | 0 => ({1, 2} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_188 : StepOkEnum (w 2 1 2 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 188) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_189 : StepOkEnum (w 2 1 2 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 189) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_190 : StepOkEnum (w 2 1 2 0 1 1 2) TaitColorPair.redBlue (cert.knownAt base 190) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_191 : StepOkEnum (w 2 1 2 0 1 2 1) TaitColorPair.redBlue (cert.knownAt base 191) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_192 : StepOkEnum (w 2 1 2 0 2 1 1) TaitColorPair.redBlue (cert.knownAt base 192) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_193 : StepOkEnum (w 2 1 2 1 0 1 2) TaitColorPair.redBlue (cert.knownAt base 193) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_194 : StepOkEnum (w 2 1 2 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 194) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_195 : StepOkEnum (w 2 1 2 1 2 0 1) TaitColorPair.redBlue (cert.knownAt base 195) (fun (k : Nat) => match k with | 0 => ({1, 3} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_196 : StepOkEnum (w 2 1 2 2 0 2 2) TaitColorPair.redBlue (cert.knownAt base 196) (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_197 : StepOkEnum (w 2 1 2 2 1 0 1) TaitColorPair.redBlue (cert.knownAt base 197) (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_198 : StepOkEnum (w 2 1 2 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 198) (fun (k : Nat) => match k with | 0 => ({1, 4} : Finset (Fin 7)) | 1 => ({1, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_199 : StepOkEnum (w 2 1 2 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 199) (fun (k : Nat) => match k with | 0 => ({1, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_200 : StepOkEnum (w 2 2 0 0 0 1 2) TaitColorPair.redPurple (cert.knownAt base 200) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_201 : StepOkEnum (w 2 2 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 201) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({3, 4} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_202 : StepOkEnum (w 2 2 0 1 1 2 1) TaitColorPair.redBlue (cert.knownAt base 202) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_203 : StepOkEnum (w 2 2 0 1 2 2 2) TaitColorPair.redPurple (cert.knownAt base 203) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({0, 1, 2, 6} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_204 : StepOkEnum (w 2 2 0 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 204) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_205 : StepOkEnum (w 2 2 0 2 2 1 2) TaitColorPair.redPurple (cert.knownAt base 205) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_206 : StepOkEnum (w 2 2 0 2 2 2 1) TaitColorPair.redPurple (cert.knownAt base 206) (fun (k : Nat) => match k with | 0 => ({0, 1, 2, 3} : Finset (Fin 7)) | 1 => ({0, 1, 2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_207 : StepOkEnum (w 2 2 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 207) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_208 : StepOkEnum (w 2 2 1 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 208) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_209 : StepOkEnum (w 2 2 1 0 2 2 2) TaitColorPair.redBlue (cert.knownAt base 209) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_210 : StepOkEnum (w 2 2 1 1 1 0 2) TaitColorPair.redBlue (cert.knownAt base 210) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_211 : StepOkEnum (w 2 2 1 2 1 1 0) TaitColorPair.redBlue (cert.knownAt base 211) (fun (k : Nat) => match k with | 0 => ({2, 4} : Finset (Fin 7)) | 1 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_212 : StepOkEnum (w 2 2 1 2 2 0 2) TaitColorPair.redBlue (cert.knownAt base 212) (fun (k : Nat) => match k with | 0 => ({2, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_213 : StepOkEnum (w 2 2 1 2 2 2 0) TaitColorPair.redBlue (cert.knownAt base 213) (fun (k : Nat) => match k with | 0 => ({2, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_214 : StepOkEnum (w 2 2 2 0 0 0 1) TaitColorPair.redPurple (cert.knownAt base 214) (fun (k : Nat) => match k with | 0 => ({2, 3} : Finset (Fin 7)) | 1 => ({2, 5} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_215 : StepOkEnum (w 2 2 2 0 1 1 1) TaitColorPair.redBlue (cert.knownAt base 215) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({4, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_216 : StepOkEnum (w 2 2 2 0 2 2 1) TaitColorPair.redPurple (cert.knownAt base 216) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_217 : StepOkEnum (w 2 2 2 1 0 0 0) TaitColorPair.redBlue (cert.knownAt base 217) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_218 : StepOkEnum (w 2 2 2 1 1 1 0) TaitColorPair.redBlue (cert.knownAt base 218) (fun (k : Nat) => match k with | 0 => ({3, 4} : Finset (Fin 7)) | 1 => ({3, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_219 : StepOkEnum (w 2 2 2 1 2 2 0) TaitColorPair.redBlue (cert.knownAt base 219) (fun (k : Nat) => match k with | 0 => ({3, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_220 : StepOkEnum (w 2 2 2 2 2 0 1) TaitColorPair.redPurple (cert.knownAt base 220) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_221 : StepOkEnum (w 2 2 2 2 2 1 0) TaitColorPair.redBlue (cert.knownAt base 221) (fun (k : Nat) => match k with | 0 => ({5, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_222 : StepOkEnum (w 0 0 0 1 0 0 2) TaitColorPair.redBlue (cert.knownAt base 222) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_223 : StepOkEnum (w 0 0 0 1 1 1 2) TaitColorPair.redBlue (cert.knownAt base 223) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_224 : StepOkEnum (w 0 0 0 1 2 2 2) TaitColorPair.redBlue (cert.knownAt base 224) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 3} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_225 : StepOkEnum (w 0 0 0 2 0 0 1) TaitColorPair.redBlue (cert.knownAt base 225) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_226 : StepOkEnum (w 0 0 0 2 1 1 1) TaitColorPair.redBlue (cert.knownAt base 226) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_227 : StepOkEnum (w 0 0 0 2 2 2 1) TaitColorPair.redBlue (cert.knownAt base 227) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_228 : StepOkEnum (w 0 0 1 0 0 0 2) TaitColorPair.redBlue (cert.knownAt base 228) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 5} : Finset (Fin 7)) | 4 => ({0, 5} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_229 : StepOkEnum (w 0 0 1 0 0 2 0) TaitColorPair.redBlue (cert.knownAt base 229) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_230 : StepOkEnum (w 0 0 1 1 1 2 0) TaitColorPair.redBlue (cert.knownAt base 230) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_231 : StepOkEnum (w 0 0 2 0 0 0 1) TaitColorPair.redBlue (cert.knownAt base 231) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_232 : StepOkEnum (w 0 0 2 0 0 1 0) TaitColorPair.redBlue (cert.knownAt base 232) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 4} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem node_233 : StepOkEnum (w 0 1 0 1 0 2 1) TaitColorPair.redBlue (cert.knownAt base 233) (fun (k : Nat) => match k with | 0 => ({0, 1} : Finset (Fin 7)) | 1 => ({0, 1} : Finset (Fin 7)) | 2 => ({0, 3} : Finset (Fin 7)) | 3 => ({0, 6} : Finset (Fin 7)) | 4 => ({0, 6} : Finset (Fin 7)) | _ => (∅ : Finset (Fin 7))) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ok : cert.Ok base := by
  intro k hk
  simp only [cert, nodes, List.length_cons, List.length_nil] at hk
  interval_cases k
  · exact node_0
  · exact node_1
  · exact node_2
  · exact node_3
  · exact node_4
  · exact node_5
  · exact node_6
  · exact node_7
  · exact node_8
  · exact node_9
  · exact node_10
  · exact node_11
  · exact node_12
  · exact node_13
  · exact node_14
  · exact node_15
  · exact node_16
  · exact node_17
  · exact node_18
  · exact node_19
  · exact node_20
  · exact node_21
  · exact node_22
  · exact node_23
  · exact node_24
  · exact node_25
  · exact node_26
  · exact node_27
  · exact node_28
  · exact node_29
  · exact node_30
  · exact node_31
  · exact node_32
  · exact node_33
  · exact node_34
  · exact node_35
  · exact node_36
  · exact node_37
  · exact node_38
  · exact node_39
  · exact node_40
  · exact node_41
  · exact node_42
  · exact node_43
  · exact node_44
  · exact node_45
  · exact node_46
  · exact node_47
  · exact node_48
  · exact node_49
  · exact node_50
  · exact node_51
  · exact node_52
  · exact node_53
  · exact node_54
  · exact node_55
  · exact node_56
  · exact node_57
  · exact node_58
  · exact node_59
  · exact node_60
  · exact node_61
  · exact node_62
  · exact node_63
  · exact node_64
  · exact node_65
  · exact node_66
  · exact node_67
  · exact node_68
  · exact node_69
  · exact node_70
  · exact node_71
  · exact node_72
  · exact node_73
  · exact node_74
  · exact node_75
  · exact node_76
  · exact node_77
  · exact node_78
  · exact node_79
  · exact node_80
  · exact node_81
  · exact node_82
  · exact node_83
  · exact node_84
  · exact node_85
  · exact node_86
  · exact node_87
  · exact node_88
  · exact node_89
  · exact node_90
  · exact node_91
  · exact node_92
  · exact node_93
  · exact node_94
  · exact node_95
  · exact node_96
  · exact node_97
  · exact node_98
  · exact node_99
  · exact node_100
  · exact node_101
  · exact node_102
  · exact node_103
  · exact node_104
  · exact node_105
  · exact node_106
  · exact node_107
  · exact node_108
  · exact node_109
  · exact node_110
  · exact node_111
  · exact node_112
  · exact node_113
  · exact node_114
  · exact node_115
  · exact node_116
  · exact node_117
  · exact node_118
  · exact node_119
  · exact node_120
  · exact node_121
  · exact node_122
  · exact node_123
  · exact node_124
  · exact node_125
  · exact node_126
  · exact node_127
  · exact node_128
  · exact node_129
  · exact node_130
  · exact node_131
  · exact node_132
  · exact node_133
  · exact node_134
  · exact node_135
  · exact node_136
  · exact node_137
  · exact node_138
  · exact node_139
  · exact node_140
  · exact node_141
  · exact node_142
  · exact node_143
  · exact node_144
  · exact node_145
  · exact node_146
  · exact node_147
  · exact node_148
  · exact node_149
  · exact node_150
  · exact node_151
  · exact node_152
  · exact node_153
  · exact node_154
  · exact node_155
  · exact node_156
  · exact node_157
  · exact node_158
  · exact node_159
  · exact node_160
  · exact node_161
  · exact node_162
  · exact node_163
  · exact node_164
  · exact node_165
  · exact node_166
  · exact node_167
  · exact node_168
  · exact node_169
  · exact node_170
  · exact node_171
  · exact node_172
  · exact node_173
  · exact node_174
  · exact node_175
  · exact node_176
  · exact node_177
  · exact node_178
  · exact node_179
  · exact node_180
  · exact node_181
  · exact node_182
  · exact node_183
  · exact node_184
  · exact node_185
  · exact node_186
  · exact node_187
  · exact node_188
  · exact node_189
  · exact node_190
  · exact node_191
  · exact node_192
  · exact node_193
  · exact node_194
  · exact node_195
  · exact node_196
  · exact node_197
  · exact node_198
  · exact node_199
  · exact node_200
  · exact node_201
  · exact node_202
  · exact node_203
  · exact node_204
  · exact node_205
  · exact node_206
  · exact node_207
  · exact node_208
  · exact node_209
  · exact node_210
  · exact node_211
  · exact node_212
  · exact node_213
  · exact node_214
  · exact node_215
  · exact node_216
  · exact node_217
  · exact node_218
  · exact node_219
  · exact node_220
  · exact node_221
  · exact node_222
  · exact node_223
  · exact node_224
  · exact node_225
  · exact node_226
  · exact node_227
  · exact node_228
  · exact node_229
  · exact node_230
  · exact node_231
  · exact node_232
  · exact node_233

/-- every node word is derivable into any target containing the support words -/
theorem derivable {target : Set (Word 7)} (hbase : ∀ u ∈ base, u ∈ target) :
    ∀ k (h : k < cert.nodes.length), Derivable target (cert.nodes[k]).1 :=
  cert.derivable_of_ok hbase ok

end Flower7Enum
end Mettapedia.GraphTheory.FourColor.KempeDerivation
