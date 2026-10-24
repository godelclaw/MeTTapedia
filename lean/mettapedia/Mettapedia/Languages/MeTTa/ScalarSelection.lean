import Mathlib.Order.Defs.LinearOrder

/-!
# Ready-scalar selection

PeTTa expands binary `min` and `max` into one comparison followed by an
`if` which returns one of the two already-evaluated operands.  The payload is
kept separate from its ordered key so a tie can retain the left operand's
exact representation (for example, an integer rather than an equal float).

The final section gives a comparison-query lower bound.  It is deliberately
limited to this ready, binary, total-order region; evaluation, faults, partial
application and dialect dispatch are separate admission obligations.
-/

namespace Mettapedia.Languages.MeTTa.ScalarSelection

inductive Direction where
  | minimum
  | maximum
  deriving DecidableEq

/-- A ready scalar's ordered meaning and its exact runtime representation. -/
structure ReadyScalar (Key Representation : Type) where
  key : Key
  representation : Representation
  deriving DecidableEq

def comparison [LE Key] [DecidableRel (fun a b : Key => a ≤ b)]
    (direction : Direction)
    (left right : ReadyScalar Key Representation) : Bool :=
  match direction with
  | .minimum => decide (left.key ≤ right.key)
  | .maximum => decide (right.key ≤ left.key)

/-- PeTTa's comparison-and-selection expansion on ready operands. -/
def select [LE Key] [DecidableRel (fun a b : Key => a ≤ b)]
    (direction : Direction) (left right : ReadyScalar Key Representation) :
    ReadyScalar Key Representation :=
  if comparison direction left right then left else right

theorem select_is_operand [LE Key]
    [DecidableRel (fun a b : Key => a ≤ b)]
    (direction : Direction) (left right : ReadyScalar Key Representation) :
    select direction left right = left ∨ select direction left right = right := by
  unfold select
  split <;> simp_all

/-- Equal keys select the left operand, retaining its representation. -/
theorem select_tie_left [LinearOrder Key]
    (direction : Direction) (key : Key)
    (leftRepresentation rightRepresentation : Representation) :
    select direction
        ⟨key, leftRepresentation⟩ ⟨key, rightRepresentation⟩ =
      ⟨key, leftRepresentation⟩ := by
  cases direction <;> simp [select, comparison]

/-- Which input a comparison branch returns. -/
inductive Operand where
  | left
  | right
  deriving DecidableEq

def Operand.read (operand : Operand)
    (left right : ReadyScalar Key Representation) :
    ReadyScalar Key Representation :=
  match operand with
  | .left => left
  | .right => right

/-- Programs in the black-box comparison model: either choose an operand
without comparing, or inspect the one comparison used by the specification. -/
inductive CompareProgram where
  | constant (operand : Operand)
  | branch (whenTrue whenFalse : Operand)

def CompareProgram.run [LE Key]
    [DecidableRel (fun a b : Key => a ≤ b)]
    (program : CompareProgram) (direction : Direction)
    (left right : ReadyScalar Key Representation) :
    ReadyScalar Key Representation :=
  match program with
  | .constant operand => operand.read left right
  | .branch whenTrue whenFalse =>
      if comparison direction left right
      then whenTrue.read left right
      else whenFalse.read left right

def CompareProgram.comparisons : CompareProgram → Nat
  | .constant _ => 0
  | .branch _ _ => 1

def CompareProgram.Correct {Key Representation : Type} [LE Key]
    [DecidableRel (fun a b : Key => a ≤ b)]
    (program : CompareProgram) (direction : Direction) : Prop :=
  ∀ (left right : ReadyScalar Key Representation),
    program.run direction left right =
    select direction left right

def direct : CompareProgram := .branch .left .right

theorem direct_correct {Key Representation : Type} [LE Key]
    [DecidableRel (fun a b : Key => a ≤ b)] (direction : Direction) :
    CompareProgram.Correct (Key := Key) (Representation := Representation)
      direct direction := by
  intro left right
  rfl

theorem direct_one_comparison : direct.comparisons = 1 := rfl

/-- With two distinguishable keys, no zero-comparison operand choice computes
binary minimum or maximum in both input orders. -/
theorem correct_comparisons_lower_bound {Key Representation : Type}
    [LinearOrder Key]
    (payload : Representation) (low high : Key) (strict : low < high)
    (direction : Direction) (program : CompareProgram)
    (correct : CompareProgram.Correct
      (Key := Key) (Representation := Representation) program direction) :
    1 ≤ program.comparisons := by
  let lo : ReadyScalar Key Representation := ⟨low, payload⟩
  let hi : ReadyScalar Key Representation := ⟨high, payload⟩
  have lowLeHigh : low ≤ high := le_of_lt strict
  have notHighLeLow : ¬ high ≤ low := not_le_of_gt strict
  have lowNeHigh : low ≠ high := ne_of_lt strict
  cases program with
  | branch whenTrue whenFalse => simp [CompareProgram.comparisons]
  | constant operand =>
      cases direction with
      | minimum =>
          cases operand with
          | left =>
              have keys : high = low := by
                simpa [CompareProgram.run, select, comparison, Operand.read,
                  lo, hi, notHighLeLow] using
                  congrArg ReadyScalar.key (correct hi lo)
              exact (lowNeHigh keys.symm).elim
          | right =>
              have keys : high = low := by
                simpa [CompareProgram.run, select, comparison, Operand.read,
                  lo, hi, lowLeHigh] using
                  congrArg ReadyScalar.key (correct lo hi)
              exact (lowNeHigh keys.symm).elim
      | maximum =>
          cases operand with
          | left =>
              have keys : low = high := by
                simpa [CompareProgram.run, select, comparison, Operand.read,
                  lo, hi, notHighLeLow] using
                  congrArg ReadyScalar.key (correct lo hi)
              exact (lowNeHigh keys).elim
          | right =>
              have keys : low = high := by
                simpa [CompareProgram.run, select, comparison, Operand.read,
                  lo, hi, lowLeHigh] using
                  congrArg ReadyScalar.key (correct hi lo)
              exact (lowNeHigh keys).elim

theorem direct_optimal {Key Representation : Type}
    [LinearOrder Key]
    (payload : Representation) (low high : Key) (strict : low < high)
    (direction : Direction) :
    CompareProgram.Correct (Key := Key) (Representation := Representation)
        direct direction ∧
      direct.comparisons = 1 ∧
      ∀ (program : CompareProgram),
        CompareProgram.Correct (Key := Key) (Representation := Representation)
          program direction →
        direct.comparisons ≤ program.comparisons := by
  refine ⟨direct_correct (Key := Key) (Representation := Representation) direction,
    direct_one_comparison, ?_⟩
  intro program correct
  exact correct_comparisons_lower_bound
    payload low high strict direction program correct

example :
    select .minimum
        (⟨1, "integer"⟩ : ReadyScalar Nat String)
        ⟨1, "float"⟩ =
      ⟨1, "integer"⟩ := by
  decide

example :
    select .maximum
        (⟨1, "float"⟩ : ReadyScalar Nat String)
        ⟨1, "integer"⟩ =
      ⟨1, "float"⟩ := by
  decide

end Mettapedia.Languages.MeTTa.ScalarSelection
