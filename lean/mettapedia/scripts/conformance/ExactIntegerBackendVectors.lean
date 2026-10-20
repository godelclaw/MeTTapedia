import Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall

/-! Qualification inputs for the existing exact-integer external-call ABI.
Values come from the integer theory; receipts come from its proved compiler.
This executable oracle does not prove the C printer, ABI, or GMP implementation.
-/

open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall
open Mettapedia.OSLF.MeTTaIL.Syntax

private def tag : CoreOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .tquot => "tquot" | .fquot => "fquot"
  | .trem => "trem" | .frem => "frem"

private def readNat : Pattern → Option Nat
  | .apply "external-call:nat-zero" [] => some 0
  | .apply "external-call:nat-succ" [n] => (readNat n).map Nat.succ
  | _ => none

private def readId (name : String) : Pattern → Option Nat
  | .apply head [n] => if head = name then readNat n else none
  | _ => none

/-- The ABI retains chronological events; the source stores a reverse list.
The external-call instruction is recovered from the preceding step event.
-/
private def events : Pattern → Option (List String)
  | .apply "external-call:receipt-nil" [] => some []
  | .apply "external-call:receipt-cons"
      [.apply "external-call:step-event" [pc], rest] => do
      let n ← readId "external-call:label" pc
      return (← events rest) ++ [s!"S:{n}"]
  | .apply "external-call:receipt-cons"
      [.apply "external-call:external-event" [ext, .apply "external-call:external-value" [_]],
       rest@(.apply "external-call:receipt-cons" [.apply "external-call:step-event" [pc], _])] => do
      let n ← readId "external-call:label" pc
      let e ← readId "external-call:external-id" ext
      return (← events rest) ++ [s!"E:{n}:{e}:0"]
  | _ => none

private def pairs : List (Int × Int) :=
  let small := [-9, -7, -3, -1, 0, 1, 2, 3, 7, 9]
  let boundaries := [31, 32, 63, 64, 127, 128, 255, 1024]
  small.flatMap (fun a => small.map (a, ·)) ++
    boundaries.flatMap (fun bits =>
      let k : Int := Int.ofNat (2 ^ bits)
      [(k-1, 1), (k, 1), (k+1, -1), (-k, -1), (-k-1, 1),
       (k, k), (k, -k), (k+1, 3), (-k-1, 3), (k+1, -3),
       (-k-1, -3), (k, 0)])

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: ExactIntegerBackendVectors OUTPUT.tsv")
  let mut rows : List String := []
  for op in allOps do
    for (a, b) in pairs do
      let value := match coreSem op a b with
        | .val z => toString z
        | .declined => "declined"
      let some trace := events (compiledExternalCallReceipt op a b)
        | throw (IO.userError s!"unrecognized compiled receipt: {tag op}")
      rows := s!"{tag op}\t{a}\t{b}\t{value}\t{String.intercalate "," trace}" :: rows
  IO.FS.writeFile path (String.intercalate "\n" rows.reverse ++ "\n")
  IO.println s!"Exact integer backend: {rows.length} Lean vectors"
  return 0
