import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formation

open Mettapedia.OSLF.Framework

/-!
# Slot equalities earned by typed equation coherence

Repeated variables on opposite sides of a commutativity law require the two
input slots to agree. The result is a law of the independent profile formation
system and applies to every actual binary operation in a compiled signature.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable {S : Signature.{0}}

theorem formed_variable_iff (profile : Profile S) (valuation : Nat → HSort)
    (index : Nat) (sort : HSort) :
    Formed profile valuation (.var index) sort ↔ valuation index = sort := by
  constructor
  · intro formed
    cases formed
    rfl
  · intro equal
    exact equal ▸ .variableTerm index

theorem formed_operation_iff (profile : Profile S) (valuation : Nat → HSort)
    (operation : S.Operation) (arguments : Fin (S.arity operation) → Term S) (sort : HSort) :
    Formed profile valuation (.op operation arguments) sort ↔
      output profile operation = sort ∧
        ∀ position, Formed profile valuation (arguments position) (input profile operation position) := by
  constructor
  · intro formed
    cases formed with
    | operation _ _ children => exact ⟨rfl, children⟩
  · rintro ⟨equal, children⟩
    exact equal ▸ .operation operation arguments children

def commutativeEquation (operation : S.Operation) : Equation S :=
  (.op operation (fun position => .var position.val),
   .op operation (fun position => .var (1 - position.val)))

/-- Commutativity is a genuine restriction on the two authored input slots;
it does not check an unrelated operation table beside those slots. -/
theorem binary_commutative_iff (profile : Profile S) (operation : S.Operation)
    (arity : S.arity operation = 2) :
    CoherentEquation profile (commutativeEquation operation) ↔
      input profile operation ⟨0, by omega⟩ = input profile operation ⟨1, by omega⟩ := by
  let zero : Fin (S.arity operation) := ⟨0, by omega⟩
  let one : Fin (S.arity operation) := ⟨1, by omega⟩
  constructor
  · rintro ⟨valuation, sort, first, second⟩
    obtain ⟨_, firstChildren⟩ := (formed_operation_iff _ _ _ _ _).mp first
    obtain ⟨_, secondChildren⟩ := (formed_operation_iff _ _ _ _ _).mp second
    have left := (formed_variable_iff _ _ _ _).mp (firstChildren zero)
    have right := (formed_variable_iff _ _ _ _).mp (secondChildren one)
    exact left.symm.trans right
  · intro equal
    let valuation : Nat → HSort := fun _ => input profile operation zero
    have allInputs : ∀ position, input profile operation position = input profile operation zero := by
      intro position
      have below := position.isLt
      have options : position = zero ∨ position = one := by
        apply (show position.val = zero.val ∨ position.val = one.val by
          simp only [zero, one]
          omega).imp <;> exact Fin.ext
      rcases options with same | same
      · rw [same]
      · rw [same]
        exact equal.symm
    refine ⟨valuation, output profile operation, ?_, ?_⟩
    · apply Formed.operation
      intro position
      apply (formed_variable_iff _ _ _ _).mpr
      exact (allInputs position).symm
    · apply Formed.operation
      intro position
      apply (formed_variable_iff _ _ _ _).mpr
      exact (allInputs position).symm

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
