import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Completion of certified PeTTa partial applications

The runtime's private partial carrier stores a callable value and an ordered
prefix of arguments which have already been evaluated. Applying it to another
ordered vector concatenates the two argument vectors and dispatches the same
callable. No stored or newly supplied value is evaluated by this structural
step.

The carrier type below is the admission certificate: authored syntax which
merely prints as `partial` is not a `Partial`. Dispatch authority, arity,
effects, type guards and fallback remain obligations of the caller.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.PartialApplicationExpansion

/-- The semantic payload of an already-recognized private partial carrier. -/
structure Partial (Value : Type) where
  base : Value
  bound : List Value
  deriving DecidableEq

/-- The explicit call vector produced when a certified partial is completed. -/
def expand (carrier : Partial Value) (supplied : List Value) : List Value :=
  carrier.base :: (carrier.bound ++ supplied)

@[simp] theorem expand_length (carrier : Partial Value)
    (supplied : List Value) :
    (expand carrier supplied).length =
      1 + carrier.bound.length + supplied.length := by
  simp [expand, Nat.add_assoc, Nat.add_comm]

/-- The callable stays first and the complete argument vector follows in
stored-then-supplied order. -/
theorem expand_tail (carrier : Partial Value) (supplied : List Value) :
    (expand carrier supplied).tail = carrier.bound ++ supplied := by
  rfl

/-- Completing a partial in two stages is the same ordered call vector as
completing it once with the concatenated new arguments. -/
theorem expand_associative (carrier : Partial Value)
    (first second : List Value) :
    expand ⟨carrier.base, carrier.bound ++ first⟩ second =
      expand carrier (first ++ second) := by
  simp [expand, List.append_assoc]

def Partial.map (function : Source → Target)
    (carrier : Partial Source) : Partial Target :=
  ⟨function carrier.base, carrier.bound.map function⟩

/-- Transporting values before or after structural completion agrees. This is
the substitution/capture law used when a cursor renames its cells. -/
theorem expand_map (function : Source → Target)
    (carrier : Partial Source) (supplied : List Source) :
    (expand carrier supplied).map function =
      expand (carrier.map function) (supplied.map function) := by
  simp [expand, Partial.map, List.map_append]

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)

theorem expand_subst (σ : Subst) (carrier : Partial Atom)
    (supplied : List Atom) :
    (expand carrier supplied).map (subst σ) =
      expand (carrier.map (subst σ)) (supplied.map (subst σ)) :=
  expand_map (subst σ) carrier supplied

/-! ## Explicit-vector cost bound

CeTTa's entered relation consumes an explicit pointer vector. Every exact
materialization of the specified call therefore has one unavoidable output
write per vector position. The direct builder writes exactly that many slots.
This bound does not claim optimal allocation or cache behavior outside the
explicit-vector region.
-/

def directWrites (carrier : Partial Value) (supplied : List Value) : Nat :=
  1 + carrier.bound.length + supplied.length

theorem directWrites_exact (carrier : Partial Value)
    (supplied : List Value) :
    directWrites carrier supplied = (expand carrier supplied).length := by
  simp [directWrites]

/-- Any extensionally exact explicit output vector has the same unavoidable
number of written positions as the direct builder. -/
theorem exact_materialization_write_lower_bound
    (carrier : Partial Value) (supplied output : List Value)
    (exact : output = expand carrier supplied) :
    directWrites carrier supplied ≤ output.length := by
  subst output
  rw [directWrites_exact]

example :
    expand (⟨"f", ["captured", "stored"]⟩ : Partial String)
      ["new", "last"] =
    ["f", "captured", "stored", "new", "last"] := by
  decide

/-- Reversing stored and supplied arguments is observably wrong. -/
example :
    expand (⟨"f", ["stored"]⟩ : Partial String) ["supplied"] ≠
      ["f", "supplied", "stored"] := by
  decide

end Mettapedia.Languages.MeTTa.PeTTa.PartialApplicationExpansion
