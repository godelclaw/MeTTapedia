import Mettapedia.OSLF.Framework.RhoScopeExpressionDecomposition
import Mettapedia.OSLF.Syntax.RhoScopedScopeDecompositionControls

/-!
# Binary scope descriptions and their semantic boundaries

Three independently interpreted atoms describe the two nonempty separated
output scopes and their actual combined process. The complete binary
decoder reconstructs sorted fixed-point scopes and rejects malformed or
unclosed descriptions. A shared primitive description can be shorter than
the sum of semantic minimum descriptions, even for the admitted separated
scopes. This separates construction upper bounds from additive lower bounds.

Repeated disjunction gives arbitrarily long distinct programs for the same
nonempty scope. Supplied description length therefore retains information
that cannot be recovered from the erased predicate alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeDescriptionControls

open Mettapedia.OSLF.Binding RhoSchema RhoQuotationClassFibres
open RhoScopedScopeDecomposition RhoScopedScopeDecision
open RhoScopedScopeDecompositionControls
open RhoScopeExpression RhoScopeExpressionCode RhoScopeBinaryDescription
open RhoScopeExpressionDecomposition

def code : AtomCode (Fin 3) where
  encode label := if label = 0 then [false, false] else
    if label = 1 then [false, true] else [true, false]
  decode
    | [false, false] => some 0
    | [false, true] => some 1
    | [true, false] => some 2
    | _ => none
  roundtrip label := by fin_cases label <;> rfl

def atoms (label : Fin 3) (process : Process []) : Prop :=
  if label = 0 then leftScope process else if label = 1 then rightScope process else
    process = join repeatedLeft secondOutput

def emptyEnv : Environment [] := fun _ _ => False

def recursiveScope : Expression (Fin 3) Srt.nm :=
  .mu (.quote (.par (.or (.atom 0) (.drop (.var 0)))
    (.or (.atom 1) (.drop (.var 0)))))

theorem full_sorted_fixed_point_roundtrip :
    decodeBinary code (encodeBinary code recursiveScope) = some ⟨.nm, recursiveScope⟩ :=
  decodeBinary_encode code recursiveScope

theorem closed_fixed_point_is_admitted :
    decodeClosed code (encodeBinary code recursiveScope) = some ⟨.nm, recursiveScope⟩ :=
  decodeClosed_encode code recursiveScope (by decide +kernel)

theorem arbitrary_variable_index_is_retained :
    decodeBinary code (encodeBinary code (.var 137)) =
      some ⟨.nm, (Expression.var 137 : Expression (Fin 3) Srt.nm)⟩ :=
  decodeBinary_encode code (.var 137)

theorem unbound_variable_is_rejected_by_closed_admission :
    decodeClosed code (encodeBinary code (.var 137)) = none := by
  rw [decodeClosed, decodeBinary_encode]
  rfl

theorem wrong_sort_and_underflow_are_rejected :
    decode (Atom := Fin 3) [.var 0, .quote] = none ∧
      decode (Atom := Fin 3) [.par] = none := ⟨rfl, rfl⟩

theorem truncated_payload_and_multiple_results_are_rejected :
    decodeBinary code [false, false, false] = none ∧
      decode (Atom := Fin 3) [.atom 0, .atom 1] = none := ⟨rfl, rfl⟩

theorem first_atom_reading : reading atoms emptyEnv (.atom 0) = leftScope := rfl
theorem second_atom_reading : reading atoms emptyEnv (.atom 1) = rightScope := rfl

theorem actual_formula_membership :
    reading atoms emptyEnv (.quote (.par (.atom 0) (.atom 1))) compositeName := by
  rw [reading_quote_parallel, first_atom_reading, second_atom_reading]
  exact ⟨repeatedLeft, secondOutput, rfl, rfl, rfl⟩

theorem shared_description_has_the_same_actual_composite_reading :
    reading atoms emptyEnv (.quote (.atom 2)) = Composite leftScope rightScope := by
  funext name
  apply propext
  change (∃ process, process = join repeatedLeft secondOutput ∧ quote process = name) ↔ _
  constructor
  · rintro ⟨process, rfl, readout⟩
    exact ⟨repeatedLeft, secondOutput, rfl, rfl, readout⟩
  · rintro ⟨first, second, firstAdmitted, secondAdmitted, readout⟩
    change first = repeatedLeft at firstAdmitted
    change second = secondOutput at secondAdmitted
    subst first
    subst second
    exact ⟨join repeatedLeft secondOutput, rfl, readout⟩

theorem atom_payload_bound (label : Fin 3) : 7 ≤ (cell code (.atom label)).length := by
  fin_cases label <;> decide +kernel

theorem shared_description_length : (encodeBinary code (.quote (.atom 2))).length = 13 :=
  by decide +kernel

theorem constructive_minimum_upper_bound :
    minimum atoms emptyEnv code (Composite leftScope rightScope) ≤
      minimum atoms emptyEnv code leftScope + minimum atoms emptyEnv code rightScope + 6 :=
  composite_minimum_upper_bound atoms emptyEnv code
    ⟨.atom 0, first_atom_reading⟩ ⟨.atom 1, second_atom_reading⟩

/-- Even nonempty, admitted separated scopes need not have exactly additive semantic minima. -/
theorem shared_primitive_can_make_the_composite_shorter :
    minimum atoms emptyEnv code (Composite leftScope rightScope) <
      minimum atoms emptyEnv code leftScope + minimum atoms emptyEnv code rightScope := by
  have upper := minimum_le_supplied_description atoms emptyEnv code (.quote (.atom 2))
  rw [shared_description_has_the_same_actual_composite_reading, shared_description_length] at upper
  have leftBound : 7 ≤ minimum atoms emptyEnv code leftScope :=
    minimum_lower_bound atoms emptyEnv code ⟨.atom 0, first_atom_reading⟩
      (fun expression _same => sorted_description_lower_bound code atom_payload_bound expression)
  have rightBound : 7 ≤ minimum atoms emptyEnv code rightScope :=
    minimum_lower_bound atoms emptyEnv code ⟨.atom 1, second_atom_reading⟩
      (fun expression _same => sorted_description_lower_bound code atom_payload_bound expression)
  omega

def repeatOr : Nat → Expression (Fin 3) Srt.pr
  | 0 => .atom 0
  | count + 1 => .or (.atom 0) (repeatOr count)

theorem repeated_disjunction_has_the_same_scope (count : Nat) :
    reading atoms emptyEnv (repeatOr count) = leftScope := by
  induction count with
  | zero => exact first_atom_reading
  | succ count ih =>
    funext process
    apply propext
    change reading atoms emptyEnv (.atom 0) process ∨
      reading atoms emptyEnv (repeatOr count) process ↔ leftScope process
    rw [first_atom_reading, ih]
    simp

theorem repeated_description_length (count : Nat) :
    (encodeBinary code (repeatOr count)).length = 10 + 13 * count := by
  have atomicLength : (encodeBinary code (.atom 0)).length = 10 := by decide +kernel
  induction count with
  | zero => exact atomicLength
  | succ count ih =>
    have appendLength : (encodeBinary code (repeatOr (count + 1))).length =
        (encodeBinary code (.atom 0)).length + (encodeBinary code (repeatOr count)).length + 3 := by
      simp [repeatOr, encodeBinary, encode, stream, cell, Nat.add_assoc]
      omega
    rw [appendLength, atomicLength, ih]
    omega

theorem equal_predicates_can_have_unbounded_distinct_descriptions (bound : Nat) :
    ∃ expression : Expression (Fin 3) Srt.pr,
      reading atoms emptyEnv expression = leftScope ∧
      bound < (encodeBinary code expression).length := by
  refine ⟨repeatOr bound, repeated_disjunction_has_the_same_scope bound, ?_⟩
  rw [repeated_description_length]
  omega

end Mettapedia.OSLF.Framework.RhoScopeDescriptionControls
