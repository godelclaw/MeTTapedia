import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stability
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.GraphLaws

open Mettapedia.OSLF.Framework

/-!
# Stable commutativity constraints on the actual profile slots

The two input slots agree exactly when the swapped-variable law has a common
formation context and preserves formation under every context valuation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra

variable {S : Signature.{0}}

private theorem forall_binary {arity : Nat} (two : arity = 2) (predicate : Fin arity → Prop) :
    (∀ position, predicate position) ↔
      predicate ⟨0, by omega⟩ ∧ predicate ⟨1, by omega⟩ := by
  constructor
  · intro all
    exact ⟨all _, all _⟩
  · rintro ⟨first, second⟩ position
    have bound := position.isLt
    have cases : position.val = 0 ∨ position.val = 1 := by omega
    rcases cases with zero | one
    · have equal : position = ⟨0, by omega⟩ := Fin.ext zero
      rw [equal]
      exact first
    · have equal : position = ⟨1, by omega⟩ := Fin.ext one
      rw [equal]
      exact second

theorem binary_commutative_stable_iff (profile : Profile S) (operation : S.Operation)
    (arity : S.arity operation = 2) :
    StableEquation profile (commutativeEquation operation) ↔
      input profile operation ⟨0, by omega⟩ = input profile operation ⟨1, by omega⟩ := by
  constructor
  · intro stable
    exact (binary_commutative_iff profile operation arity).mp stable.1
  · intro equal
    refine ⟨(binary_commutative_iff profile operation arity).mpr equal, ?_⟩
    intro valuation sort
    change Formed profile valuation (.op operation (fun position => .var position.val)) sort ↔
      Formed profile valuation (.op operation (fun position => .var (1 - position.val))) sort
    rw [formed_operation_iff, formed_operation_iff,
      forall_binary arity, forall_binary arity]
    simp only [formed_variable_iff, Nat.sub_zero, Nat.sub_self]
    rw [equal]
    constructor
    · rintro ⟨result, first, second⟩
      exact ⟨result, second, first⟩
    · rintro ⟨result, first, second⟩
      exact ⟨result, second, first⟩

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
