import Mettapedia.OSLF.NativeTypes.SortProfiles.Derived
import Mathlib.Data.Fintype.Basic

/-!
# Free type-code carriers and independently gated kind formation

An operational carrier enters the enrichment by an explicit injection. Sort
constants and generated type codes are different constructors of the free
carrier. A slot assignment controls actual formation premises and conclusions;
it supplies no interpretation of a sort as a predicate power or universe.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeEnrichment

open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

structure Signature where
  Carrier : Type
  Former : Type
  arity : Former → Nat
  input : (former : Former) → Fin (arity former) → Carrier
  output : Former → Carrier

universe u v

variable (signature : Signature)

abbrev Vertex := (former : signature.Former) → Fin (signature.arity former + 1) → HSort

def inputSort (vertex : Vertex signature) (former : signature.Former)
    (position : Fin (signature.arity former)) : HSort :=
  vertex former ⟨position.val, Nat.lt_trans position.isLt (Nat.lt_succ_self _)⟩

def outputSort (vertex : Vertex signature) (former : signature.Former) : HSort :=
  vertex former ⟨signature.arity former, Nat.lt_succ_self _⟩

/-- Operational values remain distinguishable from sort constants and codes. -/
inductive Code (operational : signature.Carrier → Type u) : signature.Carrier → Type u where
  | operational {carrier : signature.Carrier} (value : operational carrier) : Code operational carrier
  | sort {carrier : signature.Carrier} (value : HSort) : Code operational carrier
  | former (declaration : signature.Former)
      (arguments : (position : Fin (signature.arity declaration)) →
        Code operational (signature.input declaration position)) :
      Code operational (signature.output declaration)

variable {signature}

namespace Code

variable {operational : signature.Carrier → Type u}

/-- Interpretation of the free carrier, including its operational generators. -/
structure Algebra (target : signature.Carrier → Type v) where
  operational : {carrier : signature.Carrier} → operational carrier → target carrier
  sort : {carrier : signature.Carrier} → HSort → target carrier
  former : (declaration : signature.Former) →
    ((position : Fin (signature.arity declaration)) → target (signature.input declaration position)) →
    target (signature.output declaration)

def fold {target : signature.Carrier → Type u} (algebra : Algebra (operational := operational) target) :
    {carrier : signature.Carrier} → Code signature operational carrier → target carrier
  | _, .operational value => algebra.operational value
  | _, .sort value => algebra.sort value
  | _, .former declaration arguments => algebra.former declaration (fun position => fold algebra (arguments position))

@[simp] theorem fold_operational {target : signature.Carrier → Type u}
    (algebra : Algebra (operational := operational) target) {carrier : signature.Carrier}
    (value : operational carrier) : fold algebra (.operational value) = algebra.operational value := rfl

@[simp] theorem fold_sort {target : signature.Carrier → Type u}
    (algebra : Algebra (operational := operational) target) {carrier : signature.Carrier}
    (value : HSort) : fold algebra (Code.sort value : Code signature operational carrier) = algebra.sort value := rfl

@[simp] theorem fold_former {target : signature.Carrier → Type u}
    (algebra : Algebra (operational := operational) target) (declaration : signature.Former)
    (arguments : (position : Fin (signature.arity declaration)) →
      Code signature operational (signature.input declaration position)) :
    fold algebra (.former declaration arguments) =
      algebra.former declaration (fun position => fold algebra (arguments position)) := rfl

theorem fold_unique {target : signature.Carrier → Type u}
    (algebra : Algebra (operational := operational) target)
    (interpretation : {carrier : signature.Carrier} → Code signature operational carrier → target carrier)
    (operationalLaw : ∀ carrier (value : operational carrier), interpretation (.operational value) = algebra.operational value)
    (sortLaw : ∀ carrier value, interpretation (Code.sort value : Code signature operational carrier) = algebra.sort value)
    (formerLaw : ∀ declaration arguments, interpretation (.former declaration arguments) =
      algebra.former declaration (fun position => interpretation (arguments position))) :
    ∀ carrier (code : Code signature operational carrier), interpretation code = fold algebra code := by
  intro carrier code
  induction code with
  | operational value => exact operationalLaw _ value
  | sort value => exact sortLaw _ value
  | former declaration arguments hypotheses =>
      rw [formerLaw]
      change algebra.former declaration (fun position => interpretation (arguments position)) =
        algebra.former declaration (fun position => fold algebra (arguments position))
      congr 1
      funext position
      exact hypotheses position

/-- The injection does not identify different operational values. -/
theorem operational_injective {carrier : signature.Carrier} :
    Function.Injective (Code.operational : operational carrier → Code signature operational carrier) := by
  intro first second equality
  cases equality
  rfl

theorem operational_ne_sort {carrier : signature.Carrier} (value : operational carrier) (sort : HSort) :
    (Code.operational value : Code signature operational carrier) ≠ .sort sort := by
  intro equality
  cases equality

theorem star_ne_box {carrier : signature.Carrier} :
    (Code.sort .star : Code signature operational carrier) ≠ .sort .box := by
  intro equality
  cases equality

end Code

/-- Kind formation follows exactly the selected local slots. Operational
values have no implicit type-code or kind conversion. -/
inductive Kinded {operational : signature.Carrier → Type u} (vertex : Vertex signature) :
    {carrier : signature.Carrier} → Code signature operational carrier → HSort → Type u where
  | star {carrier : signature.Carrier} : Kinded vertex (Code.sort .star : Code signature operational carrier) .box
  | former (declaration : signature.Former)
      (arguments : (position : Fin (signature.arity declaration)) →
        Code signature operational (signature.input declaration position))
      (premises : ∀ position, Kinded vertex (arguments position) (inputSort signature vertex declaration position)) :
      Kinded vertex (.former declaration arguments) (outputSort signature vertex declaration)

/-- Inference computes a kind rather than accepting a claimed kind. -/
def inferKind {operational : signature.Carrier → Type u} (vertex : Vertex signature) :
    {carrier : signature.Carrier} → Code signature operational carrier → Option HSort
  | _, .operational _ => none
  | _, .sort .star => some .box
  | _, .sort .box => none
  | _, .former declaration arguments =>
      if ∀ position, inferKind vertex (arguments position) =
          some (inputSort signature vertex declaration position)
      then some (outputSort signature vertex declaration) else none

theorem inferKind_sound {operational : signature.Carrier → Type u} {vertex : Vertex signature}
    {carrier : signature.Carrier} {code : Code signature operational carrier} {kind : HSort}
    (computed : inferKind vertex code = some kind) : Nonempty (Kinded vertex code kind) := by
  induction code generalizing kind with
  | operational value => cases computed
  | sort value =>
      cases value with
      | star => cases computed; exact ⟨.star⟩
      | box => cases computed
  | former declaration arguments hypotheses =>
      simp only [inferKind] at computed
      split at computed
      · rename_i accepted
        cases computed
        exact ⟨.former declaration arguments (fun position => Classical.choice (hypotheses position (accepted position)))⟩
      · cases computed

theorem inferKind_complete {operational : signature.Carrier → Type u} {vertex : Vertex signature}
    {carrier : signature.Carrier} {code : Code signature operational carrier} {kind : HSort}
    (formed : Kinded vertex code kind) : inferKind vertex code = some kind := by
  induction formed with
  | star => rfl
  | former declaration arguments premises hypotheses => exact if_pos hypotheses

theorem inferKind_exact {operational : signature.Carrier → Type u} (vertex : Vertex signature)
    {carrier : signature.Carrier} (code : Code signature operational carrier) (kind : HSort) :
    inferKind vertex code = some kind ↔ Nonempty (Kinded vertex code kind) :=
  ⟨inferKind_sound, fun ⟨formed⟩ => inferKind_complete formed⟩

theorem no_operational_kind {operational : signature.Carrier → Type u} (vertex : Vertex signature)
    {carrier : signature.Carrier} (value : operational carrier) (kind : HSort) :
    ¬ Nonempty (Kinded vertex (Code.operational value) kind) := by
  rw [← inferKind_exact]
  simp [inferKind]

/-- Every nullary generated former changes its actual inferred kind when its
output slot changes. This does not rely on a language-specific example. -/
theorem nullary_output_effect {operational : signature.Carrier → Type u}
    (first second : Vertex signature) (declaration : signature.Former)
    (nullary : signature.arity declaration = 0)
    (different : outputSort signature first declaration ≠ outputSort signature second declaration)
    (arguments : (position : Fin (signature.arity declaration)) →
      Code signature operational (signature.input declaration position)) :
    inferKind first (.former declaration arguments) ≠ inferKind second (.former declaration arguments) := by
  have empty : IsEmpty (Fin (signature.arity declaration)) := by rw [nullary]; infer_instance
  have allFirst : ∀ position, inferKind first (arguments position) =
      some (inputSort signature first declaration position) := fun position => isEmptyElim position
  have allSecond : ∀ position, inferKind second (arguments position) =
      some (inputSort signature second declaration position) := fun position => isEmptyElim position
  simpa only [inferKind, if_pos allFirst, if_pos allSecond, ne_eq, Option.some.injEq] using different

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeEnrichment
