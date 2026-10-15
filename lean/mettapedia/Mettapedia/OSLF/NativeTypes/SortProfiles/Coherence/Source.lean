import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formation
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerOrigins

open Mettapedia.OSLF.Framework

/-!
# Authored equation coherence through independent display formation

The executable source compiler retains constructor, binder, substitution and
collection headers. Here it feeds typed argument/result profiles, not complete
operation tables. An authored equation is accepted exactly when both original
sides have a common sort in one consistent display context. Unsupported source
premises and unresolved encodings retain the compiler's diagnostics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open Mettapedia.UniversalAlgebra

/-- Both original syntax trees are encoded using the same authored context,
then judged by the independent typed display-formation rules. -/
def SourceEquationFormed (language : LanguageDef) (law : Law)
    (profile : Profile (signature language)) : Prop :=
  ∃ valuation sort left right,
    encode language (law.context.map Prod.fst) law.left = some left ∧
    encode language (law.context.map Prod.fst) law.right = some right ∧
    Formed profile valuation left sort ∧ Formed profile valuation right sort

theorem encoded_source_formation_iff (language : LanguageDef) (law : Law)
    (equation : Mettapedia.UniversalAlgebra.Equation (signature language))
    (encoded : encodeLaw language law = some equation) (profile : Profile (signature language)) :
    SourceEquationFormed language law profile ↔ CoherentEquation profile equation := by
  obtain ⟨_, leftEncoded, rightEncoded⟩ := encodeLaw_components language law equation encoded
  constructor
  · rintro ⟨valuation, sort, left, right, leftRead, rightRead, first, second⟩
    have leftEqual := Option.some.inj (leftRead.symm.trans leftEncoded)
    have rightEqual := Option.some.inj (rightRead.symm.trans rightEncoded)
    subst left
    subst right
    exact ⟨valuation, sort, first, second⟩
  · rintro ⟨valuation, sort, first, second⟩
    exact ⟨valuation, sort, equation.1, equation.2, leftEncoded, rightEncoded, first, second⟩

def checkCompiled? {language : LanguageDef} (compiled : Compilation language)
    (profile : Profile (signature language)) : Option Bool :=
  if compiled.diagnostics = [] then some (check compiled.system profile) else none

theorem checkCompiled?_some_iff {language : LanguageDef} (compiled : Compilation language)
    (profile : Profile (signature language)) (answer : Bool) :
    checkCompiled? compiled profile = some answer ↔
      compiled.diagnostics = [] ∧ check compiled.system profile = answer := by
  by_cases complete : compiled.diagnostics = [] <;> simp [checkCompiled?, complete]

/-- Every original authored law is covered. A check cannot succeed merely
because a failed encoding was removed from the compiled equation list. -/
theorem compiled_check_exact_source (language : LanguageDef) (laws : List Law)
    (profile : Profile (signature language)) :
    checkCompiled? (compileLaws language laws) profile = some true ↔
      (compileLaws language laws).diagnostics = [] ∧
        ∀ law ∈ laws, SourceEquationFormed language law profile := by
  rw [checkCompiled?_some_iff, check_iff_coherent]
  constructor
  · rintro ⟨complete, coherent⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨equation, encoded⟩ := encodeLaw_exists_of_no_diagnostics language law
      (complete_laws language laws complete law member)
    exact (encoded_source_formation_iff _ _ _ encoded profile).mpr
      (coherent equation ((compiled_equation_member _ _ _).mpr ⟨law, member, encoded⟩))
  · rintro ⟨complete, source⟩
    refine ⟨complete, ?_⟩
    intro equation member
    obtain ⟨law, declared, encoded⟩ := (compiled_equation_member _ _ _).mp member
    exact (encoded_source_formation_iff _ _ _ encoded profile).mp (source law declared)

def checkLanguage? (language : LanguageDef) (profile : Profile (signature language)) : Option Bool :=
  checkCompiled? (equations language) profile

def languageCenter (language : LanguageDef) : Finset (Profile (signature language)) :=
  Finset.univ.filter fun profile => checkLanguage? language profile = some true

theorem original_equation_check_exact (language : LanguageDef) (profile : Profile (signature language)) :
    checkLanguage? language profile = some true ↔
      (equations language).diagnostics = [] ∧
        ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
          SourceEquationFormed language (equationLaw equation index) profile := by
  change checkCompiled? (compileLaws language (equationLaws language)) profile = some true ↔ _
  rw [compiled_check_exact_source]
  constructor
  · rintro ⟨complete, formed⟩
    exact ⟨complete, fun equation index member =>
      formed _ ((equation_law_origin _ _).mpr ⟨equation, index, member, rfl⟩)⟩
  · rintro ⟨complete, formed⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨equation, index, declared, rfl⟩ := (equation_law_origin _ _).mp member
    exact formed equation index declared

theorem mem_languageCenter_iff (language : LanguageDef) (profile : Profile (signature language)) :
    profile ∈ languageCenter language ↔
      (equations language).diagnostics = [] ∧
        ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
          SourceEquationFormed language (equationLaw equation index) profile := by
  simp only [languageCenter, Finset.mem_filter, Finset.mem_univ, true_and,
    original_equation_check_exact]

theorem no_authored_equations_whole_cube (language : LanguageDef) (empty : language.equations = []) :
    languageCenter language = Finset.univ := by
  have complete : (equations language).diagnostics = [] := by
    simp [equations, compileLaws, equationLaws, empty]
  have noLaws : (equations language).system.equations = [] := by
    simp [equations, compileLaws, equationLaws, empty]
  simp [languageCenter, checkLanguage?, checkCompiled?, complete, check, noLaws]

/-- Directed source laws have a separate check: they do not become equations
merely because their source and target displays can form together. -/
def checkDirected? (language : LanguageDef) (profile : Profile (signature language)) : Option Bool :=
  checkCompiled? (rewrites language) profile

theorem original_directed_check_exact (language : LanguageDef) (profile : Profile (signature language)) :
    checkDirected? language profile = some true ↔
      (rewrites language).diagnostics = [] ∧
        ∀ rule index, (rule, index) ∈ language.rewrites.zipIdx →
          SourceEquationFormed language (rewriteLaw rule index) profile := by
  change checkCompiled? (compileLaws language (rewriteLaws language)) profile = some true ↔ _
  rw [compiled_check_exact_source]
  constructor
  · rintro ⟨complete, formed⟩
    exact ⟨complete, fun rule index member =>
      formed _ ((rewrite_law_origin _ _).mpr ⟨rule, index, member, rfl⟩)⟩
  · rintro ⟨complete, formed⟩
    refine ⟨complete, ?_⟩
    intro law member
    obtain ⟨rule, index, declared, rfl⟩ := (rewrite_law_origin _ _).mp member
    exact formed rule index declared

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
