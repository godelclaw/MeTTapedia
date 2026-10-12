import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerSemantics
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableSource

open Mettapedia.OSLF.Framework

/-!
# Variable-name invariance of admitted display laws

A bijection renames the free variables of the actual authored templates and
their declaration context. Structural operation headers and binder display
metadata are retained. This is the display-law compiler's variable action,
not an assertion that unchanged premise providers implement a renamed query.
Unresolved premise and scoped-dependency diagnostics remain explicit.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

mutual

def renameVariables (permutation : String ≃ String) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar (permutation name)
  | .apply constructor arguments => .apply constructor (renameVariablesList permutation arguments)
  | .lambda binder body => .lambda binder (renameVariables permutation body)
  | .multiLambda arity binders body => .multiLambda arity binders (renameVariables permutation body)
  | .subst body replacement => .subst (renameVariables permutation body) (renameVariables permutation replacement)
  | .collection kind elements rest =>
      .collection kind (renameVariablesList permutation elements) (rest.map permutation)

def renameVariablesList (permutation : String ≃ String) : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => renameVariables permutation pattern :: renameVariablesList permutation patterns

end

theorem renameVariablesList_length (permutation : String ≃ String) (patterns : List Pattern) :
    (renameVariablesList permutation patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp only [renameVariablesList, List.length_cons, ih]

theorem idxOf_rename (permutation : String ≃ String) (names : List String) (name : String) :
    (names.map permutation).idxOf (permutation name) = names.idxOf name := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
    by_cases equal : first = name
    · subst first
      simp
    · have different : permutation first ≠ permutation name :=
        fun same => equal (permutation.injective same)
      simp [equal, different, ih]

theorem variableIndex?_rename (permutation : String ≃ String) (names : List String) (name : String) :
    variableIndex? (names.map permutation) (permutation name) = variableIndex? names name := by
  simp [variableIndex?, List.mem_map_of_injective permutation.injective, idxOf_rename]

mutual

theorem encode_rename (language : LanguageDef) (permutation : String ≃ String) (names : List String) :
    (pattern : Pattern) →
      encode language (names.map permutation) (renameVariables permutation pattern) =
        encode language names pattern
  | .bvar _ => rfl
  | .fvar name => by simp [renameVariables, encode, variableIndex?_rename]
  | .apply constructor arguments => by
      simp only [renameVariables, encode, renameVariablesList_length, encodeList_rename]
  | .lambda binder body => by
      simp only [renameVariables, encode, encode_rename language permutation names body]
  | .multiLambda arity binders body => by
      simp only [renameVariables, encode, encode_rename language permutation names body]
  | .subst body replacement => by
      simp only [renameVariables, encode, encode_rename language permutation names body,
        encode_rename language permutation names replacement]
  | .collection kind elements rest => by
      cases rest <;>
        simp only [renameVariables, encode, renameVariablesList_length, encodeList_rename,
          Option.map_none, Option.map_some, variableIndex?_rename]

theorem encodeList_rename (language : LanguageDef) (permutation : String ≃ String) (names : List String) :
    (patterns : List Pattern) →
      encodeList language (names.map permutation) (renameVariablesList permutation patterns) =
        encodeList language names patterns
  | [] => rfl
  | pattern :: patterns => by
      simp only [renameVariablesList, encodeList, encode_rename language permutation names pattern,
        encodeList_rename language permutation names patterns]

end

theorem evaluate_rename (language : LanguageDef) (permutation : String ≃ String)
    (names : List String) (model : Model (signature language) HSort)
    (valuation : Nat → HSort) (pattern : Pattern) :
    evaluate? language (names.map permutation) model valuation (renameVariables permutation pattern) =
      evaluate? language names model valuation pattern := by
  calc
    _ = (encode language (names.map permutation) (renameVariables permutation pattern)).map
        (Term.evaluate model valuation) := (encode_evaluate _ _ _ _ _).symm
    _ = (encode language names pattern).map (Term.evaluate model valuation) := by
      rw [encode_rename]
    _ = _ := encode_evaluate _ _ _ _ _

def renameLawVariables (permutation : String ≃ String) (law : Law) : Law :=
  {law with
    context := law.context.map (fun entry => (permutation entry.1, entry.2))
    left := renameVariables permutation law.left
    right := renameVariables permutation law.right}

theorem renamed_context_names (permutation : String ≃ String) (law : Law) :
    ((renameLawVariables permutation law).context.map Prod.fst) =
      (law.context.map Prod.fst).map permutation := by
  simp [renameLawVariables, List.map_map, Function.comp_def]

theorem source_law_rename (language : LanguageDef) (permutation : String ≃ String)
    (law : Law) (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    SourceLawHolds language (renameLawVariables permutation law) vertex ↔
      SourceLawHolds language law vertex := by
  simp only [SourceLawHolds, renamed_context_names]
  change (∀ valuation, ∃ value,
    evaluate? language ((law.context.map Prod.fst).map permutation)
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.model _ vertex) valuation
      (renameVariables permutation law.left) = some value ∧
    evaluate? language ((law.context.map Prod.fst).map permutation)
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.model _ vertex) valuation
      (renameVariables permutation law.right) = some value) ↔ _
  simp only [evaluate_rename]

theorem unresolved_rename (language : LanguageDef) (permutation : String ≃ String) (law : Law) :
    unresolved language (renameLawVariables permutation law) = unresolved language law := by
  simp only [unresolved, renamed_context_names]
  simp only [List.nodup_map_iff permutation.injective, renameLawVariables,
    encode_rename]
  rfl

theorem encodeLaw_rename (language : LanguageDef) (permutation : String ≃ String) (law : Law) :
    encodeLaw language (renameLawVariables permutation law) = encodeLaw language law := by
  simp only [encodeLaw, unresolved_rename, renamed_context_names]
  simp only [renameLawVariables, encode_rename]

theorem compile_renamed_system (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) :
    (compileLaws language (laws.map (renameLawVariables permutation))).system =
      (compileLaws language laws).system := by
  change EquationSystem.mk ((laws.map (renameLawVariables permutation)).filterMap (encodeLaw language)) =
    EquationSystem.mk (laws.filterMap (encodeLaw language))
  congr 1
  simp [List.filterMap_map, encodeLaw_rename]

theorem compile_renamed_diagnostics (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) :
    (compileLaws language (laws.map (renameLawVariables permutation))).diagnostics =
      (compileLaws language laws).diagnostics := by
  simp [compileLaws, List.flatMap_map, unresolved_rename]

/-- The actual table decision is invariant under bijective renaming of the
source variable declarations and their template occurrences. -/
theorem source_check_rename (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.Vertex (signature language)) :
    (compileLaws language (laws.map (renameLawVariables permutation))).check? vertex =
      (compileLaws language laws).check? vertex := by
  simp only [Compilation.check?, compile_renamed_diagnostics, compile_renamed_system]

theorem profile_source_rename (language : LanguageDef) (permutation : String ≃ String)
    (law : Law) (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationFormed language (renameLawVariables permutation law) profile ↔
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationFormed language law profile := by
  simp only [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationFormed, renamed_context_names]
  change (∃ valuation sort left right,
    encode language ((law.context.map Prod.fst).map permutation)
      (renameVariables permutation law.left) = some left ∧
    encode language ((law.context.map Prod.fst).map permutation)
      (renameVariables permutation law.right) = some right ∧
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formed profile valuation left sort ∧
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formed profile valuation right sort) ↔ _
  simp only [encode_rename]

theorem profile_check_rename (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkCompiled? (compileLaws language (laws.map (renameLawVariables permutation))) profile =
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkCompiled? (compileLaws language laws) profile := by
  simp only [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkCompiled?, compile_renamed_diagnostics, compile_renamed_system]

/-- The finite simultaneous-formation center is invariant under the actual
authored variable action, with the original law origins and diagnostics retained. -/
theorem profile_center_rename (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) :
    (Finset.univ.filter fun profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language) =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkCompiled? (compileLaws language (laws.map (renameLawVariables permutation)))
        profile = some true) =
    (Finset.univ.filter fun profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language) =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkCompiled? (compileLaws language laws) profile = some true) := by
  simp only [profile_check_rename]

theorem stable_profile_source_rename (language : LanguageDef) (permutation : String ≃ String)
    (law : Law) (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationStable language (renameLawVariables permutation law) profile ↔
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationStable language law profile := by
  simp only [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationStable, profile_source_rename, renamed_context_names]
  change (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationFormed language law profile ∧
    ∀ left right,
      encode language ((law.context.map Prod.fst).map permutation)
        (renameVariables permutation law.left) = some left →
      encode language ((law.context.map Prod.fst).map permutation)
        (renameVariables permutation law.right) = some right →
      ∀ valuation sort, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formed profile valuation left sort ↔
        Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Formed profile valuation right sort) ↔ _
  simp only [encode_rename]

theorem stable_profile_check_rename (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws language (laws.map (renameLawVariables permutation)))
        profile =
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws language laws) profile := by
  simp only [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?, compile_renamed_diagnostics, compile_renamed_system]

theorem stable_profile_center_rename (language : LanguageDef) (permutation : String ≃ String)
    (laws : List Law) :
    (Finset.univ.filter fun profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language) =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws language (laws.map (renameLawVariables permutation)))
        profile = some true) =
    (Finset.univ.filter fun profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language) =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws language laws) profile = some true) := by
  simp only [stable_profile_check_rename]

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
