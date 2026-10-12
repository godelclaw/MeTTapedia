import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Stability
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Source

open Mettapedia.OSLF.Framework

/-!
# Executable equation-stable profiles from original authored laws

The source checker retains every original law and its diagnostics. Acceptance
requires common formation somewhere and preservation of the complete typed
formation relation everywhere. Its arguments and result are the generated
profile slots themselves, rather than a second independent operation table.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open Mettapedia.UniversalAlgebra

def SourceEquationStable (language : LanguageDef) (law : Law)
    (profile : Profile (signature language)) : Prop :=
  SourceEquationFormed language law profile ∧
    ∀ left right,
      encode language (law.context.map Prod.fst) law.left = some left →
      encode language (law.context.map Prod.fst) law.right = some right →
      ∀ valuation sort, Formed profile valuation left sort ↔ Formed profile valuation right sort

theorem encoded_source_stable_iff (language : LanguageDef) (law : Law)
    (equation : Mettapedia.UniversalAlgebra.Equation (signature language))
    (encoded : encodeLaw language law = some equation) (profile : Profile (signature language)) :
    SourceEquationStable language law profile ↔ StableEquation profile equation := by
  obtain ⟨_, leftEncoded, rightEncoded⟩ := encodeLaw_components language law equation encoded
  constructor
  · rintro ⟨coherent, uniform⟩
    exact ⟨(encoded_source_formation_iff _ _ _ encoded profile).mp coherent,
      uniform equation.1 equation.2 leftEncoded rightEncoded⟩
  · rintro ⟨coherent, uniform⟩
    refine ⟨(encoded_source_formation_iff _ _ _ encoded profile).mpr coherent, ?_⟩
    intro left right leftRead rightRead
    have first := Option.some.inj (leftRead.symm.trans leftEncoded)
    have second := Option.some.inj (rightRead.symm.trans rightEncoded)
    subst left
    subst right
    exact uniform

def checkStableCompiled? {language : LanguageDef} (compiled : Compilation language)
    (profile : Profile (signature language)) : Option Bool :=
  if compiled.diagnostics = [] then some (checkStable compiled.system profile) else none

theorem checkStableCompiled?_some_iff {language : LanguageDef} (compiled : Compilation language)
    (profile : Profile (signature language)) (answer : Bool) :
    checkStableCompiled? compiled profile = some answer ↔
      compiled.diagnostics = [] ∧ checkStable compiled.system profile = answer := by
  by_cases complete : compiled.diagnostics = [] <;> simp [checkStableCompiled?, complete]

theorem compiled_stable_check_exact_source (language : LanguageDef) (laws : List Law)
    (profile : Profile (signature language)) :
    checkStableCompiled? (compileLaws language laws) profile = some true ↔
      (compileLaws language laws).diagnostics = [] ∧
        ∀ law ∈ laws, SourceEquationStable language law profile := by
  rw [checkStableCompiled?_some_iff, checkStable_iff]
  constructor
  · rintro ⟨complete, stable⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨equation, encoded⟩ := encodeLaw_exists_of_no_diagnostics language law
      (complete_laws language laws complete law member)
    exact (encoded_source_stable_iff _ _ _ encoded profile).mpr
      (stable equation ((compiled_equation_member _ _ _).mpr ⟨law, member, encoded⟩))
  · rintro ⟨complete, source⟩
    refine ⟨complete, ?_⟩
    intro equation member
    obtain ⟨law, declared, encoded⟩ := (compiled_equation_member _ _ _).mp member
    exact (encoded_source_stable_iff _ _ _ encoded profile).mp (source law declared)

def checkStableLanguage? (language : LanguageDef) (profile : Profile (signature language)) : Option Bool :=
  checkStableCompiled? (equations language) profile

def stableLanguageCenter (language : LanguageDef) : Finset (Profile (signature language)) :=
  Finset.univ.filter fun profile => checkStableLanguage? language profile = some true

theorem original_stable_equation_check_exact (language : LanguageDef) (profile : Profile (signature language)) :
    checkStableLanguage? language profile = some true ↔
      (equations language).diagnostics = [] ∧
        ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
          SourceEquationStable language (equationLaw equation index) profile := by
  change checkStableCompiled? (compileLaws language (equationLaws language)) profile = some true ↔ _
  rw [compiled_stable_check_exact_source]
  constructor
  · rintro ⟨complete, stable⟩
    exact ⟨complete, fun equation index member =>
      stable _ ((equation_law_origin _ _).mpr ⟨equation, index, member, rfl⟩)⟩
  · rintro ⟨complete, stable⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨equation, index, declared, rfl⟩ := (equation_law_origin _ _).mp member
    exact stable equation index declared

theorem mem_stableLanguageCenter_iff (language : LanguageDef) (profile : Profile (signature language)) :
    profile ∈ stableLanguageCenter language ↔
      (equations language).diagnostics = [] ∧
        ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
          SourceEquationStable language (equationLaw equation index) profile := by
  simp only [stableLanguageCenter, Finset.mem_filter, Finset.mem_univ, true_and,
    original_stable_equation_check_exact]

theorem no_authored_equations_stable_whole_cube (language : LanguageDef) (empty : language.equations = []) :
    stableLanguageCenter language = Finset.univ := by
  have complete : (equations language).diagnostics = [] := by
    simp [equations, compileLaws, equationLaws, empty]
  have noLaws : (equations language).system.equations = [] := by
    simp [equations, compileLaws, equationLaws, empty]
  simp [stableLanguageCenter, checkStableLanguage?, checkStableCompiled?, complete, checkStable, noLaws]

/-- Directed law preservation is a separately earned formation comparison,
not an equation-center condition. -/
def checkStableDirected? (language : LanguageDef) (profile : Profile (signature language)) : Option Bool :=
  checkStableCompiled? (rewrites language) profile

theorem original_stable_directed_check_exact (language : LanguageDef) (profile : Profile (signature language)) :
    checkStableDirected? language profile = some true ↔
      (rewrites language).diagnostics = [] ∧
        ∀ rule index, (rule, index) ∈ language.rewrites.zipIdx →
          SourceEquationStable language (rewriteLaw rule index) profile := by
  change checkStableCompiled? (compileLaws language (rewriteLaws language)) profile = some true ↔ _
  rw [compiled_stable_check_exact_source]
  constructor
  · rintro ⟨complete, stable⟩
    exact ⟨complete, fun rule index member =>
      stable _ ((rewrite_law_origin _ _).mpr ⟨rule, index, member, rfl⟩)⟩
  · rintro ⟨complete, stable⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨rule, index, declared, rfl⟩ := (rewrite_law_origin _ _).mp member
    exact stable rule index declared

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
