import Mettapedia.Algorithms.Compression.Checked

/-!
# Repeated-block instance and executable word descriptions

A small independently implemented IC family. The cost is a declared unary
constructor-size model, not Kolmogorov complexity or UTF-8 byte length. The
checker validates extraction proposals; no correctness of the guessed period
is assumed. Python and MeTTa can implement these same finite operations.
-/

namespace Mettapedia.Algorithms.Compression.RepeatedBlock

open Checked

variable {Symbol : Type*}

def repeatBlock (count : Nat) (block : List Symbol) : List Symbol :=
  (List.replicate count block).flatten

def model (Symbol : Type*) : Model (List Symbol) Nat where
  extract count source :=
    if 2 ≤ count ∧ source.length % count = 0 then
      some (source.take (source.length / count))
    else none
  expand count residual := some (repeatBlock count residual)
  featureCost count := count + 2
  dataCost source := source.length + 1

inductive Description (Symbol : Type*) where
  | literal : List Symbol → Description Symbol
  | repeat : Nat → Description Symbol → Description Symbol

def Description.decode : Description Symbol → List Symbol
  | .literal values => values
  | .repeat count body => repeatBlock count body.decode

def Description.size : Description Symbol → Nat
  | .literal values => values.length + 1
  | .repeat count body => count + 2 + body.size

def describe (features : List Nat) (residual : List Symbol) : Description Symbol :=
  features.foldr Description.repeat (.literal residual)

theorem describe_decode (features : List Nat) (residual : List Symbol) :
    restore (model Symbol) features residual = some (describe features residual).decode := by
  induction features with
  | nil => rfl
  | cons feature rest ih =>
      change ((restore (model Symbol) rest residual).bind ((model Symbol).expand feature)) =
        some (repeatBlock feature (describe rest residual).decode)
      rw [ih]
      rfl

theorem describe_size (features : List Nat) (residual : List Symbol) :
    (describe features residual).size = cost (model Symbol) features residual := by
  induction features with
  | nil => simp [describe, Description.size, cost, model]
  | cons feature rest ih =>
      calc
        (describe (feature :: rest) residual).size =
            feature + 2 + (describe rest residual).size := rfl
        _ = feature + 2 + cost (model Symbol) rest residual := by rw [ih]
        _ = cost (model Symbol) (feature :: rest) residual := by
          simp [cost, model, Nat.add_assoc]

def encode [DecidableEq Symbol] (fuel : Nat) (proposals : List Nat) (source : List Symbol) : Description Symbol :=
  let result := compress (model Symbol) (fun _ => proposals) fuel source
  describe result.1 result.2

/-- Every returned description reconstructs the complete source, including
symbol order and repeated occurrences, at every finite search budget. -/
theorem decode_encode [DecidableEq Symbol] (fuel : Nat) (proposals : List Nat) (source : List Symbol) :
    (encode fuel proposals source).decode = source := by
  have correct := (compress_correct (model Symbol) (fun _ => proposals) fuel source).1
  rw [describe_decode] at correct
  exact Option.some.inj correct

theorem encode_size_le [DecidableEq Symbol] (fuel : Nat) (proposals : List Nat) (source : List Symbol) :
    (encode fuel proposals source).size ≤ source.length + 1 := by
  unfold encode
  rw [describe_size]
  exact (compress_correct (model Symbol) (fun _ => proposals) fuel source).2.1

/-- A rejected early candidate does not hide a later admissible one. -/
theorem skips_rejected_candidate :
    select (model Bool) (repeatBlock 8 [true, false]) [3, 2] =
      some (2, repeatBlock 4 [true, false]) := by decide

theorem genuinely_compresses :
    (encode 8 [2, 3, 4, 5, 6, 7, 8] (repeatBlock 16 [true, false])).size <
      (repeatBlock 16 [true, false]).length + 1 := by decide

theorem scrambled_control :
    accept (model Bool) [true, false, false, true, true, true, false, false] 2 = none := by
  decide

theorem zero_count_control :
    accept (model Bool) [true, true, true, true] 0 = none := by decide

end Mettapedia.Algorithms.Compression.RepeatedBlock
