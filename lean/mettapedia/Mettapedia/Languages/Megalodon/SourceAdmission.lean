import Mettapedia.Languages.Megalodon.SourceProofInvariant
import Mettapedia.Languages.Megalodon.NativeAdmission

/-!
# Admission preserving the source binding invariant

This layer refines ordinary native admission with executable checks on proof
payloads and polymorphic regions. The same checks support every selected
profile. They do not add axioms, interpret names as capabilities, or change
the selected theory. Imported environments are checked once; subsequent
admission preserves the invariant without rescanning their old declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SourceAdmission
open MathdataKernel NativeAdmission SourceScopeInvariant

def EnvironmentSafe (environment : Environment) : Prop :=
  Definitions environment ∧ Known environment

def environmentCheck (environment : Environment) : Bool :=
  definitionsCheck environment && environment.known.all fun declaration =>
    decide (Scoped 0 declaration.proposition ∧ Protected declaration.proposition)

private theorem lookup_known_member {declarations : List KnownDecl} {name : Name} {proposition : Tm}
    (found : lookupKnownList? declarations name = some proposition) :
    ∃ declaration ∈ declarations, declaration.proposition = proposition := by
  induction declarations with
  | nil => cases found
  | cons first rest ih =>
      simp only [lookupKnownList?] at found
      split at found
      · exact ⟨first, List.mem_cons_self, Option.some.inj found⟩
      · obtain ⟨declaration, member, same⟩ := ih found
        exact ⟨declaration, List.mem_cons_of_mem first member, same⟩

theorem environmentCheck_sound {environment : Environment} (checked : environmentCheck environment = true) :
    EnvironmentSafe environment := by
  simp only [environmentCheck, Bool.and_eq_true] at checked
  obtain ⟨definitions, known⟩ := checked
  refine ⟨definitionsCheck_sound definitions, ?_⟩
  intro name proposition found
  obtain ⟨declaration, member, same⟩ := lookup_known_member found
  have safe := of_decide_eq_true (List.all_eq_true.mp known declaration member)
  simpa only [same] using safe

def ItemSafe : Item → Prop
  | .parameter .. => True
  | .definition _ _ body => Protected body
  | .known _ proposition | .conjecture proposition => Protected proposition
  | .theorem_ _ proposition proof => Protected proposition ∧ ProofPayload proof

instance itemSafeDecidable (item : Item) : Decidable (ItemSafe item) := by
  cases item <;> unfold ItemSafe <;> infer_instance

def admit (authority : Authority) (fuel : Nat) (environment : Environment) (item : Item) : Option Environment :=
  if ItemSafe item then NativeAdmission.admit authority fuel environment item else none

theorem admit_iff (authority : Authority) (fuel : Nat) (environment result : Environment) (item : Item) :
    admit authority fuel environment item = some result ↔
      ItemSafe item ∧ NativeAdmission.Admits authority fuel environment item result := by
  by_cases safe : ItemSafe item
  · simp [admit, safe, NativeAdmission.admit_iff]
  · simp [admit, safe]

theorem checkProposition_scoped {environment : Environment} {typeDepth : Nat} {context : List Tp}
    {proposition : Tm} (formed : checkProposition environment typeDepth context proposition = true) :
    Scoped context.length proposition := by
  induction proposition generalizing typeDepth context with
  | typeAll body ih =>
      exact scoped_mono (ih (context := []) formed) (Nat.zero_le _)
  | _ => exact inferTerm_scoped (by simpa only [checkProposition, decide_eq_true_eq] using formed)

private theorem addTerm_safe {environment : Environment} (safe : EnvironmentSafe environment)
    (declaration : TermDecl)
    (newSafe : ∀ body, declaration.definition = some body → Scoped 0 body ∧ Protected body) :
    EnvironmentSafe (addTerm environment declaration) := by
  refine ⟨?_, safe.2⟩
  intro name foundDeclaration body found defined
  simp only [addTerm, Environment.lookupTerm?, lookupTermList?] at found
  split at found
  · cases Option.some.inj found
    exact newSafe body defined
  · exact safe.1 name foundDeclaration body found defined

private theorem addKnown_safe {environment : Environment} (safe : EnvironmentSafe environment)
    (name : Name) (proposition : Tm) (newSafe : Scoped 0 proposition ∧ Protected proposition) :
    EnvironmentSafe (addKnown environment name proposition) := by
  refine ⟨safe.1, ?_⟩
  intro foundName foundProposition found
  simp only [addKnown, Environment.lookupKnown?, lookupKnownList?] at found
  split at found
  · cases Option.some.inj found
    exact newSafe
  · exact safe.2 foundName foundProposition found

theorem admitted_preserves {authority : Authority} {fuel : Nat} {initial final : Environment} {item : Item}
    (environmentSafe : EnvironmentSafe initial) (itemSafe : ItemSafe item)
    (admitted : NativeAdmission.Admits authority fuel initial item final) : EnvironmentSafe final := by
  cases admitted with
  | parameter => exact addTerm_safe environmentSafe _ (by intro body impossible; cases impossible)
  | definition _ _ _ typed =>
      apply addTerm_safe environmentSafe
      intro body same
      cases Option.some.inj same
      exact ⟨inferTerm_scoped typed, itemSafe⟩
  | known _ formed _ => exact addKnown_safe environmentSafe _ _ ⟨checkProposition_scoped formed, itemSafe⟩
  | theorem_ _ formed _ => exact addKnown_safe environmentSafe _ _ ⟨checkProposition_scoped formed, itemSafe.1⟩
  | conjecture => exact environmentSafe

theorem admit_preserves {authority : Authority} {fuel : Nat} {initial final : Environment} {item : Item}
    (safe : EnvironmentSafe initial) (accepted : admit authority fuel initial item = some final) :
    EnvironmentSafe final :=
  let checks := (admit_iff _ _ _ _ _).mp accepted
  admitted_preserves safe checks.1 checks.2

def checkAll (authority : Authority) (fuel : Nat) : Environment → List Item → Option Environment
  | environment, [] => some environment
  | environment, item :: rest => do
      let next ← admit authority fuel environment item
      checkAll authority fuel next rest

theorem checkAll_iff (authority : Authority) (fuel : Nat) (items : List Item) (initial final : Environment) :
    checkAll authority fuel initial items = some final ↔
      (∀ item ∈ items, ItemSafe item) ∧ NativeAdmission.AdmitsAll authority fuel initial items final := by
  induction items generalizing initial with
  | nil => simp [checkAll, ← NativeAdmission.checkAll_iff, NativeAdmission.checkAll, eq_comm]
  | cons item rest ih =>
      constructor
      · intro accepted
        obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp accepted
        obtain ⟨safe, admitted⟩ := (admit_iff _ _ _ _ _).mp first
        obtain ⟨restSafe, restAdmitted⟩ := (ih middle).mp later
        exact ⟨by simpa using And.intro safe restSafe, .cons admitted restAdmitted⟩
      · rintro ⟨safe, admitted⟩
        cases admitted with
        | cons first later =>
            have headSafe := safe item List.mem_cons_self
            have tailSafe := fun next member => safe next (List.mem_cons_of_mem item member)
            exact Option.bind_eq_some_iff.mpr ⟨_, (admit_iff _ _ _ _ _).mpr ⟨headSafe, first⟩,
              (ih _).mpr ⟨tailSafe, later⟩⟩

theorem checkAll_preserves {authority : Authority} {fuel : Nat} {items : List Item} {initial final : Environment}
    (safe : EnvironmentSafe initial) (accepted : checkAll authority fuel initial items = some final) :
    EnvironmentSafe final := by
  induction items generalizing initial with
  | nil => cases Option.some.inj accepted; exact safe
  | cons item rest ih =>
      obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp accepted
      exact ih (admit_preserves safe first) later

namespace Controls
private def authority : Authority := ⟨.mizar, [("p", .prop)], []⟩
private def identity : Tm := .typeLam (.lam (.var 0) (.db 0))

theorem polymorphic_identity_admitted :
    admit authority 8 {} (.definition "id" (.all (.arr (.var 0) (.var 0))) identity) =
      some (addTerm {} ⟨"id", .all (.arr (.var 0) (.var 0)), some identity⟩) := by decide

theorem mixed_binder_capture_definition_refused :
    admit authority 8 {} (.definition "capture" (.arr .prop (.all .prop)) (.lam .prop (.typeLam (.db 0)))) = none := by decide

theorem primitive_inventory_still_selected :
    admit authority 8 {} (.definition "unknown" .prop (.prim 99)) = none := by decide
end Controls

end Mettapedia.Languages.Megalodon.SourceAdmission
