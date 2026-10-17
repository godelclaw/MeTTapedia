import Mettapedia.Languages.Megalodon.NativeTheorem

/-!
# Ordered native Megalodon admission under a selected import authority

Imports carry actual parameter/type and known/proposition associations.
A profile nickname is not an axiom and a submitted declaration is not an
import capability. Native names are fresh; this excludes the shadowing cycles
possible in unchecked environment lists. Source hash validation can supply
these associations, but is not replaced by this native admission protocol.

Checking a batch computes a proposed immutable environment. A refusal returns
no proposal; the caller still owns its original environment. Native allocation
and publication must commit that proposal together, rather than mutating the
live environment during checking.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeAdmission

open MathdataKernel

/-- The five source profile tags are descriptive. Each service retains its
actual primitive inventory and import associations separately. -/
inductive Profile where
  | hf | egal | mizar | hoas | setmm
  deriving DecidableEq, Repr

structure Authority where
  profile : Profile
  parameters : List (Name × Tp)
  known : List KnownDecl
  deriving DecidableEq, Repr

inductive Item where
  | parameter (name : Name) (type : Tp)
  | definition (name : Name) (type : Tp) (body : Tm)
  | known (name : Name) (proposition : Tm)
  | theorem_ (name : Name) (proposition : Tm) (proof : Pf)
  | conjecture (proposition : Tm)
  deriving DecidableEq, Repr

def addTerm (environment : Environment) (declaration : TermDecl) : Environment :=
  { environment with terms := declaration :: environment.terms }

def addKnown (environment : Environment) (name : Name) (proposition : Tm) : Environment :=
  { environment with known := ⟨name, proposition⟩ :: environment.known }

inductive Admits (authority : Authority) (fuel : Nat) : Environment → Item → Environment → Prop where
  | parameter {environment : Environment} {name : Name} {type : Tp} :
      environment.lookupTerm? name = none → type.polyWellFormed 0 = true →
      (name, type) ∈ authority.parameters →
      Admits authority fuel environment (.parameter name type) (addTerm environment ⟨name, type, none⟩)
  | definition {environment : Environment} {name : Name} {type : Tp} {body : Tm} :
      environment.lookupTerm? name = none → type.polyWellFormed 0 = true →
      Tm.normalizeOne body = (body, true) → inferTerm environment 0 [] body = some type →
      Admits authority fuel environment (.definition name type body)
        (addTerm environment ⟨name, type, some body⟩)
  | known {environment : Environment} {name : Name} {proposition : Tm} :
      environment.lookupKnown? name = none → checkProposition environment 0 [] proposition = true →
      ⟨name, proposition⟩ ∈ authority.known →
      Admits authority fuel environment (.known name proposition) (addKnown environment name proposition)
  | theorem_ {environment : Environment} {name : Name} {proposition : Tm} {proof : Pf} :
      environment.lookupKnown? name = none → checkProposition environment 0 [] proposition = true →
      checkProof environment fuel 0 [] [] proof proposition = true →
      Admits authority fuel environment (.theorem_ name proposition proof) (addKnown environment name proposition)
  | conjecture {environment : Environment} {proposition : Tm} :
      checkProposition environment 0 [] proposition = true →
      Admits authority fuel environment (.conjecture proposition) environment

def admit (authority : Authority) (fuel : Nat) (environment : Environment) : Item → Option Environment
  | .parameter name type =>
      if environment.lookupTerm? name = none ∧ type.polyWellFormed 0 = true ∧
          (name, type) ∈ authority.parameters then some (addTerm environment ⟨name, type, none⟩) else none
  | .definition name type body =>
      if environment.lookupTerm? name = none ∧ type.polyWellFormed 0 = true ∧
          Tm.normalizeOne body = (body, true) ∧ inferTerm environment 0 [] body = some type then
        some (addTerm environment ⟨name, type, some body⟩) else none
  | .known name proposition =>
      if environment.lookupKnown? name = none ∧ checkProposition environment 0 [] proposition = true ∧
          ⟨name, proposition⟩ ∈ authority.known then some (addKnown environment name proposition) else none
  | .theorem_ name proposition proof =>
      if environment.lookupKnown? name = none ∧ checkProposition environment 0 [] proposition = true ∧
          checkProof environment fuel 0 [] [] proof proposition = true then
        some (addKnown environment name proposition) else none
  | .conjecture proposition => if checkProposition environment 0 [] proposition then some environment else none

theorem admit_iff (authority : Authority) (fuel : Nat) (environment result : Environment) (item : Item) :
    admit authority fuel environment item = some result ↔ Admits authority fuel environment item result := by
  constructor
  · intro accepted
    cases item <;> simp only [admit] at accepted
    all_goals split at accepted <;> try contradiction
    all_goals rename_i checks
    all_goals cases Option.some.inj accepted
    · exact .parameter checks.1 checks.2.1 checks.2.2
    · exact .definition checks.1 checks.2.1 checks.2.2.1 checks.2.2.2
    · exact .known checks.1 checks.2.1 checks.2.2
    · exact .theorem_ checks.1 checks.2.1 checks.2.2
    · exact .conjecture checks
  · intro admitted
    cases admitted <;> simp_all [admit]

/-- The inductive prefix meaning does not invoke the batch checker. -/
inductive AdmitsAll (authority : Authority) (fuel : Nat) : Environment → List Item → Environment → Prop where
  | nil (environment : Environment) : AdmitsAll authority fuel environment [] environment
  | cons {initial middle final : Environment} {item : Item} {rest : List Item} :
      Admits authority fuel initial item middle → AdmitsAll authority fuel middle rest final →
      AdmitsAll authority fuel initial (item :: rest) final

def checkAll (authority : Authority) (fuel : Nat) : Environment → List Item → Option Environment
  | environment, [] => some environment
  | environment, item :: rest => do
      let next ← admit authority fuel environment item
      checkAll authority fuel next rest

theorem checkAll_iff (authority : Authority) (fuel : Nat) (items : List Item) (initial final : Environment) :
    checkAll authority fuel initial items = some final ↔ AdmitsAll authority fuel initial items final := by
  induction items generalizing initial with
  | nil => constructor
           · intro same; cases Option.some.inj same; exact .nil _
           · intro admitted; cases admitted; rfl
  | cons item rest ih =>
      constructor
      · intro accepted
        cases step : admit authority fuel initial item with
        | none => simp [checkAll, step] at accepted
        | some next =>
            exact .cons ((admit_iff _ _ _ _ _).mp step)
              ((ih next).mp (by simpa [checkAll, step] using accepted))
      · intro admitted
        cases admitted with
        | cons first later =>
            simp [checkAll, (admit_iff _ _ _ _ _).mpr first, (ih _).mpr later]

theorem checkAll_append (authority : Authority) (fuel : Nat) (first second : List Item)
    (initial : Environment) :
    checkAll authority fuel initial (first ++ second) =
      (checkAll authority fuel initial first).bind (fun middle => checkAll authority fuel middle second) := by
  induction first generalizing initial with
  | nil => rfl
  | cons item rest ih =>
      cases step : admit authority fuel initial item <;> simp [checkAll, step, ih]

/-- The sealed inference route admits exactly the same retained proposition,
without reconstructing an erased proof tree. -/
def admitChecked {environment : Environment} {fuel : Nat}
    (name : Name) (theorem_ : NativeTheorem.Theorem environment fuel) : Option Environment :=
  if environment.lookupKnown? name = none then some (addKnown environment name theorem_.proposition) else none

theorem admitChecked_original {authority : Authority} {environment result : Environment} {fuel : Nat}
    (name : Name) (theorem_ : NativeTheorem.Theorem environment fuel)
    (accepted : admitChecked name theorem_ = some result) :
    ∃ proof, Admits authority fuel environment (.theorem_ name theorem_.proposition proof) result := by
  obtain ⟨formed, proof, checked⟩ := theorem_.valid
  unfold admitChecked at accepted
  split at accepted
  · rename_i fresh
    cases Option.some.inj accepted
    exact ⟨proof, .theorem_ fresh formed checked⟩
  · contradiction

/-- A successful native step never changes the selected primitive inventory. -/
theorem Admits.primitives {authority : Authority} {fuel : Nat} {initial final : Environment} {item : Item}
    (admitted : Admits authority fuel initial item final) : final.primitives = initial.primitives := by
  cases admitted <;> rfl

private theorem addTerm_retains {environment : Environment} {new : TermDecl}
    {name : Name} {declaration : TermDecl}
    (fresh : environment.lookupTerm? new.name = none)
    (found : environment.lookupTerm? name = some declaration) :
    (addTerm environment new).lookupTerm? name = some declaration := by
  have different : new.name ≠ name := by
    intro same
    rw [same, found] at fresh
    cases fresh
  simpa [addTerm, Environment.lookupTerm?, lookupTermList?, different] using found

private theorem addKnown_retains {environment : Environment} {new : Name} {body : Tm}
    {name : Name} {proposition : Tm}
    (fresh : environment.lookupKnown? new = none)
    (found : environment.lookupKnown? name = some proposition) :
    (addKnown environment new body).lookupKnown? name = some proposition := by
  have different : new ≠ name := by
    intro same
    rw [same, found] at fresh
    cases fresh
  simpa [addKnown, Environment.lookupKnown?, lookupKnownList?, different] using found

/-- Earlier bindings cannot be overwritten by admission of a fresh name. -/
theorem Admits.retains_term {authority : Authority} {fuel : Nat} {initial final : Environment} {item : Item}
    (admitted : Admits authority fuel initial item final) {name : Name} {declaration : TermDecl}
    (found : initial.lookupTerm? name = some declaration) : final.lookupTerm? name = some declaration := by
  cases admitted with
  | parameter fresh _ _ | definition fresh _ _ _ => exact addTerm_retains fresh found
  | known | theorem_ | conjecture => exact found

theorem Admits.retains_known {authority : Authority} {fuel : Nat} {initial final : Environment} {item : Item}
    (admitted : Admits authority fuel initial item final) {name : Name} {proposition : Tm}
    (found : initial.lookupKnown? name = some proposition) : final.lookupKnown? name = some proposition := by
  cases admitted with
  | known fresh _ _ | theorem_ fresh _ _ => exact addKnown_retains fresh found
  | parameter | definition | conjecture => exact found

namespace Controls
private def authority : Authority := ⟨.mizar, [("p", .prop)], [⟨"axiom", .named "p"⟩]⟩
private def env : Environment := { terms := [⟨"p", .prop, none⟩] }

theorem parameter_without_import_authority_refused :
    admit authority 8 {} (.parameter "unknown" .prop) = none := by decide
theorem imported_parameter_accepted :
    admit authority 8 {} (.parameter "p" .prop) = some env := by decide
theorem axiom_text_does_not_grant_authority :
    admit authority 8 env (.known "forged" (.named "p")) = none := by decide
theorem selected_known_accepted :
    admit authority 8 env (.known "axiom" (.named "p")) = some (addKnown env "axiom" (.named "p")) := by decide
theorem conjecture_does_not_add_knowledge :
    admit authority 8 env (.conjecture (.named "p")) = some env := by decide
theorem shadowing_definition_refused :
    admit authority 8 env (.definition "p" .prop (.named "p")) = none := by decide
theorem self_definition_refused :
    admit authority 8 env (.definition "q" .prop (.named "q")) = none := by decide
theorem older_alias_accepted :
    admit authority 8 env (.definition "q" .prop (.named "p")) =
      some (addTerm env ⟨"q", .prop, some (.named "p")⟩) := by decide
theorem profile_tag_alone_grants_nothing :
    admit { authority with known := [] } 8 env (.known "axiom" (.named "p")) = none := by decide
end Controls

end Mettapedia.Languages.Megalodon.NativeAdmission
