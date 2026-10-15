import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableQuotient

open Mettapedia.OSLF.Framework

/-!
# The actual active equation bodies at a fixed provider

Every ordered source law is classified before the active body system is
returned. A complete empty guard disables that body's conversion; missing
query signatures or unsupported source bodies retain an unresolved result.
The system retains original law membership and guard witnesses. Its typed
display quotient has the same checked sort readout as the guarded source
check, without treating disabled bodies as unconditional equations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.ActiveSystem

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource
open Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

def activeEquations? (language : LanguageDef) (provider : ProviderSnapshot) :
    List Law → Option (List (Equation (signature language)))
  | [] => some []
  | law :: laws => do
      let guards ← guards? provider law.premises
      let equation ← encodeLaw language (bodyLaw law)
      let rest ← activeEquations? language provider laws
      pure (if enabled guards then equation :: rest else rest)

theorem check_is_active_system (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (laws : List Law) :
    checkLaws? language provider profile laws =
      (activeEquations? language provider laws).map (fun equations => checkStable ⟨equations⟩ profile) := by
  induction laws with
  | nil => rfl
  | cons law laws ih =>
    unfold checkLaws? checkLaw? activeEquations?
    rw [ih]
    cases guardRead : guards? provider law.premises with
    | none => rfl
    | some guards =>
      cases bodyRead : encodeLaw language (bodyLaw law) with
      | none => rfl
      | some equation =>
        cases tailRead : activeEquations? language provider laws with
        | none => rfl
        | some tail =>
          cases active : enabled guards <;>
            simp [Option.bind_eq_bind, active, checkStable]

theorem active_equation_origin (language : LanguageDef) (provider : ProviderSnapshot)
    (laws : List Law) (equations : List (Equation (signature language)))
    (computed : activeEquations? language provider laws = some equations)
    (equation : Equation (signature language)) :
    equation ∈ equations ↔ ∃ law ∈ laws, ∃ guards,
      guards? provider law.premises = some guards ∧ enabled guards = true ∧
        encodeLaw language (bodyLaw law) = some equation := by
  induction laws generalizing equations with
  | nil =>
    cases Option.some.inj computed
    simp
  | cons law laws ih =>
    simp only [activeEquations?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at computed
    obtain ⟨guards, originalGuards, body, originalBody, rest, originalRest, result⟩ := computed
    cases active : enabled guards with
    | false =>
      have same : rest = equations := by simpa [active] using result
      subst equations
      rw [ih rest originalRest]
      constructor
      · rintro ⟨original, member, witnesses, read, enabled, bodyRead⟩
        exact ⟨original, List.mem_cons_of_mem law member, witnesses, read, enabled, bodyRead⟩
      · rintro ⟨original, member, witnesses, read, enabled, bodyRead⟩
        rcases List.mem_cons.mp member with same | tail
        · subst original
          have equal : witnesses = guards := Option.some.inj (read.symm.trans originalGuards)
          rw [equal, active] at enabled
          cases enabled
        · exact ⟨original, tail, witnesses, read, enabled, bodyRead⟩
    | true =>
      have same : body :: rest = equations := by simpa [active] using result
      subst equations
      rw [List.mem_cons, ih rest originalRest]
      constructor
      · rintro (rfl | ⟨original, member, witnesses, read, enabled, bodyRead⟩)
        · exact ⟨law, List.mem_cons_self, guards, originalGuards, active, originalBody⟩
        · exact ⟨original, List.mem_cons_of_mem law member, witnesses, read, enabled, bodyRead⟩
      · rintro ⟨original, member, witnesses, read, enabled, bodyRead⟩
        rcases List.mem_cons.mp member with same | tail
        · subst original
          exact Or.inl (Option.some.inj (bodyRead.symm.trans originalBody))
        · exact Or.inr ⟨original, tail, witnesses, read, enabled, bodyRead⟩

theorem checked_active_system_stable (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (laws : List Law)
    (equations : List (Equation (signature language)))
    (computed : activeEquations? language provider laws = some equations)
    (admitted : checkLaws? language provider profile laws = some true) :
    Stable ⟨equations⟩ profile := by
  rw [check_is_active_system, computed, Option.map_some] at admitted
  exact (checkStable_iff _ _).mp (Option.some.inj admitted)

theorem active_typed_quotient_readout (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (laws : List Law)
    (equations : List (Equation (signature language)))
    (computed : activeEquations? language provider laws = some equations)
    (admitted : checkLaws? language provider profile laws = some true)
    (valuation : Nat → ModalHypercube.HSort) (first second : Term (signature language))
    (equivalent : TypedDisplayConvertibility profile ⟨equations⟩ valuation first second) :
    displaySort profile valuation first = displaySort profile valuation second := by
  exact displaySort_equation_invariant
    (checked_active_system_stable language provider profile laws equations computed admitted)
    valuation first second equivalent

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.ActiveSystem
