import Mettapedia.OSLF.NativeTypes.Modal.NativeHistorySubstitutionComposition
import Mettapedia.OSLF.NativeTypes.Modal.NativeReceiptRechecking

/-!
# Contextual transport of the executor's complete dependent receipts

Transport constructs an actual typed RootAnswer in the new source fibre.
Identity and composition compare the complete payload, including every
capture and nested history. The certified executor can recheck every
transported receipt under its computed structural admission.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalReceiptTransport

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise RuleBinding ScopedRuleMatching StructuralDescent
open Mettapedia.GSLT.LanguageDef.WellSorted
open NativeReceiptRechecking

def payload (source target : List TypeExpr) (substitution : ContextSubstitution.Assignment)
    (original : Payload) : Payload where
  index := original.index
  trace := original.trace
  captured := NativeContextualSubstitution.assignment target.length substitution original.captured
  completed := NativeContextualSubstitution.assignment target.length substitution original.completed
  history := NativeEventSubstitution.events source target substitution original.history
  target := ContextSubstitution.substitute substitution original.target

theorem payload_identity {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {original : Payload}
    (valid : Valid environment bound type source original) : payload bound bound Pattern.bvar original = original := by
  obtain ⟨capturedSame, completedSame⟩ := NativeHistorySubstitutionIdentity.firing_assignment_identity valid
  have historySame := NativeHistorySubstitutionIdentity.firing_identity valid
  cases original
  simp only [payload, capturedSame, completedSame, historySame, ContextSubstitution.substitute_id]

theorem payload_composition {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {original : Payload}
    (valid : Valid environment bound type source original)
    (middle target : List TypeExpr) (first second : ContextSubstitution.Assignment) :
    payload middle target second (payload bound middle first original) =
      payload bound target (fun index => ContextSubstitution.substitute second (first index)) original := by
  have historySquare := NativeHistorySubstitutionComposition.firing_composes valid middle target first second
  cases original
  simp only [payload, NativeContextualSubstitution.assignment_composition,
    ContextSubstitution.substitute_comp, historySquare]

def compose {language : LanguageDef} {free : FreeTypeContext} {source middle target : List TypeExpr}
    (first : TypedBoundAssignment language free source middle)
    (second : TypedBoundAssignment language free middle target) :
    TypedBoundAssignment language free source target where
  assignment := fun index => ContextSubstitution.substitute second.assignment (first.assignment index)
  typed := fun selected => (first.typed selected).substituteBound second

def transport {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (ready : NativeOperationalProfile.Admitted environment) {target : List TypeExpr}
    (substitution : TypedBoundAssignment environment.language environment.free bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true)
    (original : Execution.RootAnswer environment bound type source) :
    Execution.RootAnswer environment target type (ContextSubstitution.substitute substitution.assignment source) where
  index := original.index
  trace := original.trace
  captured := NativeContextualSubstitution.assignment target.length substitution.assignment original.captured
  completed := NativeContextualSubstitution.assignment target.length substitution.assignment original.completed
  history := NativeEventSubstitution.events bound target substitution.assignment original.history
  target := ContextSubstitution.substitute substitution.assignment original.target
  valid := NativeFiringSubstitution.firing_substitutes original.valid ready substitution canonical objects

theorem transport_readout {environment : Environment} {bound target : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (ready : NativeOperationalProfile.Admitted environment)
    (substitution : TypedBoundAssignment environment.language environment.free bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true)
    (original : Execution.RootAnswer environment bound type source) :
    read (transport ready substitution canonical objects original) = payload bound target substitution.assignment (read original) := rfl

theorem transported_rechecked {environment : Environment} {bound target : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (ready : NativeOperationalProfile.Admitted environment)
    (substitution : TypedBoundAssignment environment.language environment.free bound target)
    (canonical : ∀ index, (substitution.assignment index).hasCanonicalBinderMetadata = true)
    (objects : ∀ index, isObjectPattern (substitution.assignment index) = true)
    (original : Execution.RootAnswer environment bound type source) :
    ∃ answer, recheck environment target type (ContextSubstitution.substitute substitution.assignment source)
        (payload bound target substitution.assignment (read original)) = some answer ∧
      read answer = payload bound target substitution.assignment (read original) := by
  apply recheck_complete ready.prerequisites.recursive
  exact (transport ready substitution canonical objects original).valid

def identity {language : LanguageDef} {free : FreeTypeContext} (bound : List TypeExpr) :
    TypedBoundAssignment language free bound bound where
  assignment := Pattern.bvar
  typed := fun selected => .bvar selected

theorem transport_identity {environment : Environment} {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (ready : NativeOperationalProfile.Admitted environment)
    (original : Execution.RootAnswer environment bound type source) :
    read (transport ready (identity bound) (fun _ => rfl) (fun _ => rfl) original) = read original := by
  change payload bound bound Pattern.bvar (read original) = read original
  exact payload_identity (original := read original) original.valid

theorem transport_composes {environment : Environment} {bound middle target : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (ready : NativeOperationalProfile.Admitted environment)
    (first : TypedBoundAssignment environment.language environment.free bound middle)
    (second : TypedBoundAssignment environment.language environment.free middle target)
    (firstCanonical : ∀ index, (first.assignment index).hasCanonicalBinderMetadata = true)
    (secondCanonical : ∀ index, (second.assignment index).hasCanonicalBinderMetadata = true)
    (firstObjects : ∀ index, isObjectPattern (first.assignment index) = true)
    (secondObjects : ∀ index, isObjectPattern (second.assignment index) = true)
    (original : Execution.RootAnswer environment bound type source) :
    read (transport ready second secondCanonical secondObjects
      (transport ready first firstCanonical firstObjects original)) =
    read (transport ready (compose first second)
      (fun index => contextSubstitute_canonical (firstCanonical index) secondCanonical)
      (fun index => contextSubstitute_objects (firstObjects index) secondObjects) original) := by
  change payload middle target second.assignment (payload bound middle first.assignment (read original)) =
    payload bound target (compose first second).assignment (read original)
  exact payload_composition (original := read original) original.valid middle target first.assignment second.assignment

end Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalReceiptTransport
