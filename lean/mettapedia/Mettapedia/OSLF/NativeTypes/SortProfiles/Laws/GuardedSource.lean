import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

open Mettapedia.OSLF.Framework

/-!
# Equation-stable profiles under finite authored provider guards

The original ordered premise stream is checked against one fixed provider.
Only nullary queries are admitted here. The source law's display formation
is checked separately; disabling a guard does not hide malformed or
uninterpreted law syntax. Directed laws retain their separate stream.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards
open Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

def bodyLaw (law : Law) : Law := {law with premises := []}

def checkLaw? (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (law : Law) : Option Bool := do
  let guards ← guards? provider law.premises
  let equation ← encodeLaw language (bodyLaw law)
  pure (!enabled guards || checkStableEquation profile equation)

def SourceAdmitted (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (law : Law) : Prop :=
  ∃ guards, GuardedBy provider 0 law.premises guards ∧
    unresolved language (bodyLaw law) = [] ∧
      (enabled guards = true → SourceEquationStable language (bodyLaw law) profile)

theorem law_check_exact (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (law : Law) :
    checkLaw? language provider profile law = some true ↔ SourceAdmitted language provider profile law := by
  constructor
  · intro checked
    simp only [checkLaw?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at checked
    obtain ⟨guards, original, equation, encoded, accepted⟩ := checked
    have complete := (encodeLaw_components language (bodyLaw law) equation encoded).1
    refine ⟨guards, (guards?_exact _ _ _).mp original, complete, ?_⟩
    intro active
    have stable : checkStableEquation profile equation = true := by
      simpa [active] using Option.some.inj accepted
    exact (encoded_source_stable_iff _ _ _ encoded _).mpr
      ((checkStableEquation_iff _ _).mp stable)
  · rintro ⟨guards, original, complete, accepted⟩
    obtain ⟨equation, encoded⟩ := encodeLaw_exists_of_no_diagnostics language (bodyLaw law) complete
    simp only [checkLaw?, (guards?_exact _ _ _).mpr original, encoded, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq]
    cases active : enabled guards with
    | false => rfl
    | true =>
      exact (checkStableEquation_iff _ _).mpr
        ((encoded_source_stable_iff _ _ _ encoded _).mp (accepted active))

def checkLaws? (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) : List Law → Option Bool
  | [] => some true
  | law :: tail => do
      let first ← checkLaw? language provider profile law
      let more ← checkLaws? language provider profile tail
      pure (first && more)

theorem laws_check_exact (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (laws : List Law) :
    checkLaws? language provider profile laws = some true ↔
      ∀ law ∈ laws, SourceAdmitted language provider profile law := by
  induction laws with
  | nil => simp [checkLaws?]
  | cons law tail ih =>
    constructor
    · intro checked
      simp only [checkLaws?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at checked
      obtain ⟨first, lawRead, more, tailRead, combined⟩ := checked
      have both : first = true ∧ more = true := by simpa using Option.some.inj combined
      rw [both.1] at lawRead
      rw [both.2] at tailRead
      exact List.forall_mem_cons.mpr ⟨(law_check_exact _ _ _ _).mp lawRead, ih.mp tailRead⟩
    · intro admitted
      obtain ⟨first, more⟩ := List.forall_mem_cons.mp admitted
      rw [checkLaws?, (law_check_exact _ _ _ _).mpr first]
      change (checkLaws? language provider profile tail).bind _ = _
      rw [ih.mpr more]
      rfl

def checkLanguage? (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) : Option Bool :=
  checkLaws? language provider profile (equationLaws language)

def center (language : LanguageDef) (provider : ProviderSnapshot) :
    Finset (Profile (signature language)) :=
  Finset.univ.filter fun profile => checkLanguage? language provider profile = some true

theorem original_equation_check_exact (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) :
    checkLanguage? language provider profile = some true ↔
      ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
        SourceAdmitted language provider profile (equationLaw equation index) := by
  rw [checkLanguage?, laws_check_exact]
  constructor
  · intro source equation index declared
    exact source _ ((equation_law_origin _ _).mpr ⟨equation, index, declared, rfl⟩)
  · intro source law declared
    obtain ⟨equation, index, member, rfl⟩ := (equation_law_origin _ _).mp declared
    exact source equation index member

theorem mem_center_iff (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) :
    profile ∈ center language provider ↔
      ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
        SourceAdmitted language provider profile (equationLaw equation index) := by
  simp [center, original_equation_check_exact]

theorem no_equations_whole_cube (language : LanguageDef) (provider : ProviderSnapshot)
    (empty : language.equations = []) : center language provider = Finset.univ := by
  simp [center, checkLanguage?, equationLaws, empty, checkLaws?]

def checkDirected? (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) : Option Bool :=
  checkLaws? language provider profile (rewriteLaws language)

theorem original_directed_check_exact (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) :
    checkDirected? language provider profile = some true ↔
      ∀ rule index, (rule, index) ∈ language.rewrites.zipIdx →
        SourceAdmitted language provider profile (rewriteLaw rule index) := by
  rw [checkDirected?, laws_check_exact]
  constructor
  · intro source rule index declared
    exact source _ ((rewrite_law_origin _ _).mpr ⟨rule, index, declared, rfl⟩)
  · intro source law declared
    obtain ⟨rule, index, member, rfl⟩ := (rewrite_law_origin _ _).mp declared
    exact source rule index member

theorem body_rename (permutation : String ≃ String) (law : Law) :
    bodyLaw (renameLawVariables permutation law) = renameLawVariables permutation (bodyLaw law) := rfl

theorem law_check_rename (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (permutation : String ≃ String) (law : Law) :
    checkLaw? language provider profile (renameLawVariables permutation law) =
      checkLaw? language provider profile law := by
  unfold checkLaw?
  rw [body_rename, encodeLaw_rename]
  rfl

theorem laws_check_rename (language : LanguageDef) (provider : ProviderSnapshot)
    (profile : Profile (signature language)) (permutation : String ≃ String) (laws : List Law) :
    checkLaws? language provider profile (laws.map (renameLawVariables permutation)) =
      checkLaws? language provider profile laws := by
  induction laws with
  | nil => rfl
  | cons law laws ih => simp only [List.map_cons, checkLaws?, law_check_rename, ih]

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.GuardedSource
