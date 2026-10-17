import Mettapedia.Languages.Megalodon.SourceNormalizationInvariant

/-!
# Protected polymorphic regions through definition expansion

Every imported definition is checked for term closure and protected type
regions. Unfolding can then introduce type abstractions without invalidating
the substitution correspondence. Cyclic lookup can still exhaust the supplied
bound; no termination claim follows just from this scope invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceScopeInvariant
open MathdataKernel

def Definitions (environment : Environment) : Prop :=
  ∀ name declaration body, environment.lookupTerm? name = some declaration →
    declaration.definition = some body → Scoped 0 body ∧ Protected body

def definitionsCheck (environment : Environment) : Bool :=
  environment.terms.all fun declaration => match declaration.definition with
    | none => true
    | some body => decide (Scoped 0 body ∧ Protected body)

private theorem lookup_member {name : Name} {declarations : List TermDecl} {declaration : TermDecl}
    (found : lookupTermList? declarations name = some declaration) : declaration ∈ declarations := by
  induction declarations with
  | nil => cases found
  | cons first rest ih =>
      simp only [lookupTermList?] at found
      split at found
      · cases Option.some.inj found
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem first (ih found)

theorem definitionsCheck_sound {environment : Environment} (checked : definitionsCheck environment = true) :
    Definitions environment := by
  intro name declaration body found defined
  have member := lookup_member found
  have each := List.all_eq_true.mp checked declaration member
  simpa [defined] using each

theorem delta_invariants (environment : Environment) (definitions : Definitions environment) :
    ∀ (fuel : Nat) (body result : Tm), deltaNormalize environment fuel body = some result →
      (∀ depth, Scoped depth body → Scoped depth result) ∧ (Protected body → Protected result)
  | fuel, .named name, result, normalized => by
      cases found : environment.lookupTerm? name with
      | none =>
          cases fuel <;> simp only [deltaNormalize, found, Option.some.injEq] at normalized <;>
            subst result <;> exact ⟨fun _ _ => trivial, fun _ => trivial⟩
      | some declaration =>
          rcases declaration with ⟨declaredName, type, body⟩
          cases body with
          | none =>
              cases fuel <;> simp only [deltaNormalize, found, Option.some.injEq] at normalized <;>
                subst result <;> exact ⟨fun _ _ => trivial, fun _ => trivial⟩
          | some body =>
              have admissible := definitions name _ body found rfl
              cases fuel with
              | zero => simp [deltaNormalize, found] at normalized
              | succ fuel =>
                  have expanded : deltaNormalize environment fuel body = some result := by
                    simpa [deltaNormalize, found] using normalized
                  obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body result expanded
                  exact ⟨fun depth _ => scope depth (scoped_mono admissible.1 (Nat.zero_le depth)),
                    fun _ => safe admissible.2⟩
  | fuel, .app function argument, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨first, firstExpanded, second, secondExpanded, rfl⟩ := normalized
      obtain ⟨fs, fp⟩ := delta_invariants environment definitions fuel function first firstExpanded
      obtain ⟨ars, arp⟩ := delta_invariants environment definitions fuel argument second secondExpanded
      exact ⟨fun depth scope => ⟨fs depth scope.1, ars depth scope.2⟩, fun safe => ⟨fp safe.1, arp safe.2⟩⟩
  | fuel, .imp domain codomain, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨first, firstExpanded, second, secondExpanded, rfl⟩ := normalized
      obtain ⟨ds, dp⟩ := delta_invariants environment definitions fuel domain first firstExpanded
      obtain ⟨cs, cp⟩ := delta_invariants environment definitions fuel codomain second secondExpanded
      exact ⟨fun depth scope => ⟨ds depth scope.1, cs depth scope.2⟩, fun safe => ⟨dp safe.1, cp safe.2⟩⟩
  | fuel, .lam type body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body next expanded
      exact ⟨fun depth scopedBody => scope (depth + 1) scopedBody, safe⟩
  | fuel, .all type body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body next expanded
      exact ⟨fun depth scopedBody => scope (depth + 1) scopedBody, safe⟩
  | fuel, .typeApp body type, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body next expanded
      exact ⟨scope, fun protectedBody => ⟨scope 0 protectedBody.1, safe protectedBody.2⟩⟩
  | fuel, .typeLam body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body next expanded
      exact ⟨scope, fun protectedBody => ⟨scope 0 protectedBody.1, safe protectedBody.2⟩⟩
  | fuel, .typeAll body, result, normalized => by
      simp [deltaNormalize, Option.bind_eq_some_iff] at normalized
      obtain ⟨next, expanded, rfl⟩ := normalized
      obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body next expanded
      exact ⟨scope, fun protectedBody => ⟨scope 0 protectedBody.1, safe protectedBody.2⟩⟩
  | fuel, .db index, result, normalized => by
      cases fuel <;> simp only [deltaNormalize, Option.some.injEq] at normalized <;>
        subst result <;> exact ⟨fun _ scope => scope, fun _ => trivial⟩
  | fuel, .prim index, result, normalized => by
      cases fuel <;> simp only [deltaNormalize, Option.some.injEq] at normalized <;>
        subst result <;> exact ⟨fun _ _ => trivial, fun _ => trivial⟩
termination_by fuel body _ _ => (fuel, sizeOf body)

theorem full_normalize_invariants {environment : Environment} (definitions : Definitions environment)
    {body result : Tm} (fuel : Nat) (normalized : MathdataKernel.normalize environment fuel body = some result) :
    (∀ depth, Scoped depth body → Scoped depth result) ∧ (Protected body → Protected result) := by
  obtain ⟨expanded, delta, beta⟩ := Option.bind_eq_some_iff.mp normalized
  obtain ⟨scope, safe⟩ := delta_invariants environment definitions fuel body expanded delta
  exact ⟨fun depth scopedBody => normalize_scoped depth fuel (scope depth scopedBody) beta,
    fun protectedBody => normalize_protected fuel (safe protectedBody) beta⟩

/-- After normalization, the publication and Lean substitution traversals
still agree, not merely on the original surface expression. -/
theorem normalized_substitution_agrees {environment : Environment} (definitions : Definitions environment)
    {body result : Tm} (safe : Protected body) (fuel : Nat)
    (normalized : MathdataKernel.normalize environment fuel body = some result)
    (depth : Nat) (replacement : Tm) :
    SourceTermFragment.publicationSubstitute depth replacement result = Tm.instantiateAt depth replacement result :=
  publication_substitution_agrees ((full_normalize_invariants definitions fuel normalized).2 safe) depth replacement

namespace Controls
private def identity : Tm := .typeLam (.lam (.var 0) (.db 0))
private def environment : Environment := { terms := [⟨"id", .all (.arr (.var 0) (.var 0)), some identity⟩] }

theorem polymorphic_definition_admitted : definitionsCheck environment = true := by decide

theorem internal_expansion_can_leave_surface_grammar :
    SourceTermFragment.termCheck (.typeApp (.named "id") .prop) = true ∧
      SourceTermFragment.termCheck (.typeApp identity .prop) = false ∧
      Protected (.typeApp identity .prop) := by decide

theorem capture_definition_refused :
    definitionsCheck { terms := [⟨"capture", .arr .prop (.all .prop), some (.lam .prop (.typeLam (.db 0)))⟩] } = false := by decide
end Controls

end Mettapedia.Languages.Megalodon.SourceScopeInvariant
