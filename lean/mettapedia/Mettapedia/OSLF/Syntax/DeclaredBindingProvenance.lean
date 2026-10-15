import Mettapedia.OSLF.Syntax.DeclaredBindingInterpretation
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation

/-!
# Retained origins and binding occurrences of authored programs

The existing origin-sensitive entry stores the source program. A separate
instance identifier labels its actual declared binding occurrences. Lowering
does not identify either the entries or their receipts. These mathematical
identifiers are not a representation bridge to private native identities.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Provenance

open Mettapedia.GSLT.LanguageDef.ModuleAlgebra

universe u

/-- Paths name declared binding occurrences, including those nested in
recursive bodies. Opaque target-language payloads remain opaque here. -/
def bindingOccurrences : {Γ : Ctx sig} → Program Γ → List (List Nat)
  | _, .lambda body => [] :: (bindingOccurrences body).map (fun path => 1 :: path)
  | _, .whereBinding _ body => [] :: (bindingOccurrences body).map (fun path => 2 :: path)
  | _, .result _ => []

theorem bindingOccurrences_substitute : ∀ {Γ Δ : Ctx sig}
    (sigma : Sub Target.sig Γ Δ) (program : Program Γ),
    bindingOccurrences (program.substitute sigma) = bindingOccurrences program
  | _, _, sigma, .lambda body => by
      simp only [Program.substitute, bindingOccurrences, bindingOccurrences_substitute]
  | _, _, sigma, .whereBinding value body => by
      simp only [Program.substitute, bindingOccurrences, bindingOccurrences_substitute]
  | _, _, _, .result _ => rfl

abbrev Retained (Origin : Type u) (Γ : Ctx sig) := Entry Origin String (Program Γ) × Nat

def instantiate {Origin : Type u} {Γ : Ctx sig} (origin : Origin) (label : String)
    (instanceId : Nat) (program : Program Γ) : Retained Origin Γ :=
  (⟨origin, label, program⟩, instanceId)

def receipts {Origin : Type u} {Γ : Ctx sig} (retained : Retained Origin Γ) :
    List (Nat × List Nat) :=
  (bindingOccurrences retained.1.body).map (fun path => (retained.2, path))

def observe {Origin : Type u} {Γ : Ctx sig} (retained : Retained Origin Γ) :
    Term Target.sig Γ .term := lower retained.1.body.source

def substitute {Origin : Type u} {Γ Δ : Ctx sig} (sigma : Sub Target.sig Γ Δ)
    (retained : Retained Origin Γ) : Retained Origin Δ :=
  (⟨retained.1.origin, retained.1.label, retained.1.body.substitute sigma⟩, retained.2)

theorem substitute_retains_origin {Origin : Type u} {Γ Δ : Ctx sig}
    (sigma : Sub Target.sig Γ Δ) (retained : Retained Origin Γ) :
    (substitute sigma retained).1.origin = retained.1.origin := rfl

theorem substitute_retains_receipts {Origin : Type u} {Γ Δ : Ctx sig}
    (sigma : Sub Target.sig Γ Δ) (retained : Retained Origin Γ) :
    receipts (substitute sigma retained) = receipts retained := by
  unfold receipts substitute
  rw [bindingOccurrences_substitute]

theorem substitute_observation {Origin : Type u} {Γ Δ : Ctx sig}
    (sigma : Sub Target.sig Γ Δ) (retained : Retained Origin Γ) :
    observe (substitute sigma retained) = bind sigma (observe retained) := by
  simp only [observe, substitute, Program.lower_source, Program.meaning_substitute]

theorem origin_not_recoverable_from_observation {Origin : Type u} {Γ : Ctx sig}
    (first second : Origin) (different : first ≠ second) (program : Program Γ) :
    ¬ ∃ recover : Term Target.sig Γ .term → Origin,
      ∀ retained : Retained Origin Γ, recover (observe retained) = retained.1.origin := by
  rintro ⟨recover, law⟩
  have one := law (instantiate first "declared" 0 program)
  have two := law (instantiate second "declared" 0 program)
  exact different (one.symm.trans two)

def identityProgram : Program [] := .lambda (.result (.var .zero))

theorem receipts_of_identity_instance (instanceId : Nat) :
    receipts (instantiate 0 "identity" instanceId identityProgram) = [(instanceId, [])] := rfl

theorem independent_instances_same_observation :
    observe (instantiate 0 "identity" 10 identityProgram) =
      observe (instantiate 1 "identity" 11 identityProgram) := rfl

theorem independent_instances_different_receipts :
    receipts (instantiate 0 "identity" 10 identityProgram) ≠
      receipts (instantiate 1 "identity" 11 identityProgram) := by
  decide

theorem receipts_not_recoverable_from_observation :
    ¬ ∃ recover : Term Target.sig [] .term → List (Nat × List Nat),
      ∀ retained : Retained Nat [], recover (observe retained) = receipts retained := by
  rintro ⟨recover, law⟩
  have one := law (instantiate 0 "identity" 10 identityProgram)
  have two := law (instantiate 1 "identity" 11 identityProgram)
  exact independent_instances_different_receipts (one.symm.trans two)

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation.Provenance
